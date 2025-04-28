use std::borrow::Cow;
use std::collections::BTreeSet;
use std::sync::{Arc, Mutex, MutexGuard};

use itertools::Itertools as _;
use serde::{Deserialize, Serialize};

use crate::encoding::{self, Key as _, Value as _, bincode, keycode};
use crate::error::{Result, Error};
use crate::storage::engine::Engine;
use crate::{errdata, errinput};

pub type Version = u64;

impl encoding::Value for Version {}

#[derive(Debug, Deserialize, Serialize)]
pub enum Key<'a> {
    // the next available version
    NextVersion,
    // Active transactions by version (uncommitted);
    TxnActive(Version),
    TxnActiveSnapshot(Version),
    /// Keeps track of all keys written to by an active transaction (identified
    /// by its version), in case it needs to roll back.
    TxnWrite(
        Version,
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
    Version(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
        Version,
    ),
    /// Unversioned non-transactional key/value pairs, mostly used for metadata.
    /// These exist separately from versioned keys, i.e. the unversioned key
    /// "foo" is entirely independent of the versioned key "foo@7".
    Unversioned(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
}

impl<'a> encoding::Key<'a> for Key<'a> {}

#[derive(Debug, Deserialize, Serialize)]
enum KeyPrefix<'a> {
    NextVersion,
    TxnActive,
    TxnActiveSnapshot,
    TxnWrite(Version),
    Version(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
    Unversioned,
}
impl<'a> encoding::Key<'a> for KeyPrefix<'a> {}

/// An MVCC-based transactional key-value engine. It wraps an underlying storage
/// engine that's used for raw key/value storage.
///
/// While it supports any number of concurrent transactions, individual read or
/// write operations are executed sequentially, serialized via a mutex. There
/// are two reasons for this: the storage engine itself is not thread-safe,
/// requiring serialized access, and the Raft state machine that manages the
/// MVCC engine applies commands one at a time from the Raft log, which will
/// serialize them anyway.
pub struct MVCC<E: Engine> {
    pub engine: Arc<Mutex<E>>,
}


impl<E: Engine> MVCC<E> {
    pub fn new(engine: E) -> Self {
        Self {
            engine: Arc::new(Mutex::new(engine)),
        }
    }

    pub fn begin(&self) -> Result<Transaction<E>> {
        Transaction::begin(self.engine.clone())
    }

    /// Begins a new read-only transaction at the latest version.
    pub fn begin_read_only(&self) -> Result<Transaction<E>> {
        Transaction::begin_read_only(Arc::clone(&self.engine), None)
    }

    /// Begins a new read-only transaction as of the given version.
    pub fn begin_as_of(&self, version: Version) -> Result<Transaction<E>> {
        Transaction::begin_read_only(Arc::clone(&self.engine), Some(version))
    }

    /// Resumes a transaction from the given transaction state.
    pub fn resume(&self, state: TransactionState) -> Result<Transaction<E>> {
        Transaction::resume(Arc::clone(&self.engine), state)
    }

    pub fn get_unversioned(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        self.engine.lock()?.get(&Key::Unversioned(key.into()).encode())
    }

    pub fn set_unversioned(&self, key:&[u8], value: Vec<u8>) -> Result<()> {
        self.engine.lock()?.set(&Key::Unversioned(key.into()).encode(), value)
    }

    pub fn status(&self) -> Result<Status> {
        let mut engine = self.engine.lock()?;
        let version = match engine.get(&Key::NextVersion.encode())?{
            Some(ref v) => Version::decode(&v)? - 1,
            None => 0,
        };
        let active_txns = engine.scan_prefix(&KeyPrefix::TxnActive.encode()).count() as u64;
        let storage = engine.status()?;

        Ok(Status {
            version,
            active_txns,
            storage,
        })

    }

}


#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Status {
    /// The total number of MVCC versions (i.e. read-write transactions).
    pub version: u64,
    pub active_txns: u64,
    pub storage: super::Status,
}

impl encoding::Value for Status {}

/// An MVCC transaction.
pub struct Transaction<E: Engine> {
    engine: Arc<Mutex<E>>,
    state: TransactionState,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TransactionState {
    pub version: Version,
    pub read_only: bool,
    pub active: BTreeSet<Version>,
}
impl encoding::Value for TransactionState {}

impl TransactionState {
    pub fn is_visible(&self, version: Version) -> bool {
        if self.active.contains(&version) {
            false
        } else if self.read_only {
            version < self.version
        } else {
            version <= self.version
        }
    }
}

impl From<TransactionState> for Cow<'_, TransactionState> {
    fn from(txn: TransactionState) -> Self {
        Cow::Owned(txn)
    }
}

impl<'a> From<&'a TransactionState> for Cow<'a, TransactionState> {
    fn from(txn: &'a TransactionState) -> Self {
        Cow::Borrowed(txn)
    }
}


impl<E: Engine> Transaction<E> {
    pub fn begin(engine: Arc<Mutex<E>>) -> Result<Self> {
        let mut session = engine.lock()?;
        
        let version = match session.get(&Key::NextVersion.encode())? {
            Some(ref v) => Version::decode(&v)?,
            None => 1,
        };

        session.set(&Key::NextVersion.encode(), (version + 1).encode())?;
        
        // Fetch the current set of active transactions, persist it for
        // time-travel queries if non-empty, then add this txn to it.
        let active = Self::scan_active(&mut session)?;
        if !active.is_empty() {
            session.set(&Key::TxnActiveSnapshot(version).encode(), active.encode())?;
        }
        session.set(&Key::TxnActive(version).encode(), vec![])?;
        drop(session);

        return Ok(Self {
            engine,
            state: TransactionState {
                version,
                read_only: false,
                active,
            },
        });

    }


    fn scan_active(session: &mut MutexGuard<E>) -> Result<BTreeSet<Version>> {
        let mut actives = BTreeSet::new();
        let mut scan = session.scan_prefix(&KeyPrefix::TxnActive.encode());
        while let Some((k, _)) = scan.next().transpose()?{
            match Key::decode(&k)? {
                Key::TxnActive(version) => actives.insert(version),
                key => return errdata!("unexpected key type: {key:?}"),
            };
        }

        return Ok(actives);

    }

    /// Begins a new read-only transaction. If version is given it will see the
    /// state as of the beginning of that version (ignoring writes at that
    /// version). In other words, it sees the same state as the read-write
    /// transaction at that version saw when it began.
    fn begin_read_only(engine: Arc<Mutex<E>>, as_of: Option<Version>) -> Result<Self> {
        let mut session = engine.lock()?;

        let mut version = match session.get(&Key::NextVersion.encode())? {
            Some(ref v) => Version::decode(&v)?,
            None => 1,
        };

        // fetch the current set of active txn
        let mut active = BTreeSet::new();
        if let Some(as_of) = as_of {
            if as_of >= version {
                return errinput!("version {as_of} does not exist")
            }
            version = as_of;
            if let Some(value) = session.get(&Key::TxnActiveSnapshot(version).encode())? {
                active = BTreeSet::<Version>::decode(&value)?;
            }
        } else {
            active = Self::scan_active(&mut session)?;
        }

        drop(session);

        Ok(Self {
            engine,
            state: TransactionState{
                version,
                read_only: true,
                active,
            },
        })
    }

    fn resume(engine: Arc<Mutex<E>>, state: TransactionState) -> Result<Self> {
        // For read-write transactions, verify that the transaction is still
        // active before making further writes.
        if !state.read_only && engine.lock()?.get(&Key::TxnActive(state.version).encode())?.is_none() {
            return errinput!("no active transaction with version {}", state.version)
        }

        Ok(Self {
            engine,
            state
        })
    }

    /// Returns the version the transaction is running at.
    pub fn version(&self) -> Version {
        self.state.version
    }

    /// Returns whether the transaction is read-only.
    pub fn read_only(&self) -> bool {
        self.state.read_only
    }

    /// Returns the transaction's state. This can be used to instantiate a
    /// functionally equivalent transaction via resume().
    pub fn state(&self) -> &TransactionState {
        &self.state
    }
    /// Commits the transaction, by removing it from the active set. This will
    /// immediately make its writes visible to subsequent transactions. Also
    /// removes its TxnWrite records, which are no longer needed.
    ///
    /// NB: commit does not flush writes to durable storage, since we rely on
    /// the Raft log for persistence.
    pub fn commit(self) -> Result<()> {
        if self.state.read_only {
            return Ok(());
        }

        let mut session = self.engine.lock()?;
        let remove: Vec<_> = session
            .scan_prefix(&KeyPrefix::TxnWrite(self.state.version).encode())
            .map_ok(|(k, _)| k)
            .try_collect()?;
        for k in remove {
            session.delete(&k)?
        }
        session.delete(&Key::TxnActive(self.state.version).encode())
    }

    /// Rolls back the transaction, by undoing all written versions and removing
    /// it from the active set. The active set snapshot is left behind, since
    /// this is needed for time travel queries at this version.
    pub fn rollback(self) -> Result<()> {
        if self.state.read_only {
            return Ok(());
        }

        let mut session = self.engine.lock()?;
        let mut rollback = Vec::new();
        let mut scan = session.scan_prefix(&KeyPrefix::TxnWrite(self.state.version).encode());
        while let Some((k, _)) = scan.next().transpose()? {
            match Key::decode(&k)? {
                Key::TxnWrite(_, k) => {
                    rollback.push(Key::Version(k, self.state.version).encode())
                    // the version
                },
                _ => return errdata!("expected TxnWrite key, got {k:?}"),
            };
            rollback.push(k); // the TxnWrite record
        }
        drop(scan);

        for k in rollback.into_iter() {
            session.delete(&k)?
        }

        session.delete(&Key::TxnActive(self.state.version).encode())

    }


    /// Deletes a key.
    pub fn delete(&self, key: &[u8]) -> Result<()> {
        self.write_version(key, None)
    }

    /// Sets a value for a key.
    pub fn set(&self, key: &[u8], value: Vec<u8>) -> Result<()> {
        self.write_version(key, Some(value))
    }

    /// Writes a new version for a key at the transaction's version. None writes
    /// a deletion tombstone. If a write conflict is found (either a newer or
    /// uncommitted version), a serialization error is returned.  Replacing our
    /// own uncommitted write is fine.
    fn write_version(&self, key: &[u8], value: Option<Vec<u8>>) -> Result<()> {
        if self.state.read_only {
            return Err(Error::ReadOnly);
        }
        let mut session = self.engine.lock()?;

        let from = Key::Version(
            key.into(),
            self.state.active.iter().min().copied().unwrap_or(self.state.version + 1),
        ).encode();
        let to = Key::Version(key.into(), u64::MAX).encode();
        if let Some((key, _)) = session.scan(from..=to).last().transpose()? {
            match Key::decode(&key)? {
                Key::Version(_, version) => {
                    if !self.state.is_visible(version){
                        return Err(Error::Serialization);
                    }
                },
                key => return errdata!("expected Version key, got {key:?}"),
            }
        }
        session.set(&Key::TxnWrite(self.state.version, key.into()).encode(), vec![])?;
        session.set(&Key::Version(key.into(), self.state.version).encode(), bincode::serialize(&value))
    }

    /// Fetches a key's value, or None if it does not exist.
    pub fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        let mut session = self.engine.lock()?;
        let from = Key::Version(key.into(), 0).encode();
        let to = Key::Version(key.into(), self.state.version).encode();

        let mut scan = session.scan(from..=to).rev();
        while let Some((key, value)) = scan.next().transpose()? {
            match Key::decode(&key)? {
                Key::Version(_, version) => {
                    if self.state.is_visible(version) {
                        return bincode::deserialize(&value);
                    }
                },
                key => return errdata!("expected Version key, got {key:?}"),
            }
        }
        Ok(None)
    }

    /// Returns an iterator over the latest visible key/value pairs at the
    /// transaction's version.
    pub fn scan(&self, range: impl RangeBounds<Vec<u8>>) -> ScanIterator<E> {
        unimplemented!()
    }


}
