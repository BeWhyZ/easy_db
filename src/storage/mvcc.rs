use std::borrow::Cow;
use std::collections::{BTreeSet, VecDeque};
use std::ops::{Bound, RangeBounds};
use std::sync::{Arc, Mutex, MutexGuard};

use itertools::Itertools as _;
use serde::{Deserialize, Serialize};

use crate::encoding::{self, Key as _, Value as _, bincode, keycode};
use crate::error::{Result, Error};
use crate::storage::engine::Engine;
use crate::{errdata, errinput};

use super::engine;

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
        let start = match range.start_bound() {
            Bound::Included(k) => Bound::Included(Key::Version(k.into(), 0).encode()),
            Bound::Excluded(k) => Bound::Excluded(Key::Version(k.into(), u64::MAX).encode()),
            Bound::Unbounded => Bound::Included(Key::Version(vec![].into(), 0).encode()),
        };
        let end = match range.end_bound() {
            Bound::Included(k) => Bound::Included(Key::Version(k.into(), u64::MAX).encode()),
            Bound::Excluded(k) => Bound::Excluded(Key::Version(k.into(), 0).encode()),
            Bound::Unbounded => Bound::Excluded(KeyPrefix::Unversioned.encode()),
        };
        ScanIterator::new(self.engine.clone(), self.state().clone(), (start, end))
    }

    pub fn scan_prefix(&self, prefix: &[u8]) -> ScanIterator<E> {
        let mut prefix = KeyPrefix::Version(prefix.into()).encode();
        prefix.truncate(prefix.len() - 1);
        let range = keycode::prefix_range(&prefix);
        ScanIterator::new(self.engine.clone(), self.state().clone(), range)
    }


}

/// An iterator over the latest live and visible key/value pairs for the txn.
///
/// The (single-threaded) engine is shared via mutex, and holding the mutex for
/// the lifetime of the iterator can cause deadlocks (e.g. when the local SQL
/// engine pulls from two tables concurrently during a join). Instead, we pull
/// and buffer a batch of rows at a time, and release the mutex in between.
///
/// This does not implement DoubleEndedIterator (reverse scans), since the SQL
/// layer doesn't currently need it.
pub struct ScanIterator<E: Engine> {
    engine: Arc<Mutex<E>>, 
    txn: TransactionState,
    buffer: VecDeque<(Vec<u8>, Vec<u8>)>,

    // the remaining range after the buffer
    remainder: Option<(Bound<Vec<u8>>, Bound<Vec<u8>>)>,
}

impl<E: Engine> Clone for ScanIterator<E> {
    fn clone(&self) -> Self {
        Self {
            engine: Arc::clone(&self.engine),
            txn: self.txn.clone(),
            buffer: self.buffer.clone(),
            remainder: self.remainder.clone(),
        }
    }
}


impl<E: Engine> ScanIterator<E> {
    const BUFFER_SIZE: usize = if cfg!(test) {2} else { 32};

    fn new(engine: Arc<Mutex<E>>, txn: TransactionState, range: (Bound<Vec<u8>>, Bound<Vec<u8>>)) -> Self {
        Self {
            engine,
            txn,
            buffer: VecDeque::with_capacity(Self::BUFFER_SIZE),
            remainder: Some(range),
        }
    }
    /// Fills the buffer, if there's any pending items.
    fn fill_buffer(&mut self) -> Result<()> {
        if self.buffer.len() >= Self::BUFFER_SIZE {
            return Ok(());
        }

        let Some(range) = self.remainder.take() else {
            return Ok(());
        };
        let range_end = range.1.clone();

        let mut engine = self.engine.lock()?;
        let mut iter = VersionIterator::new(&self.txn, engine.scan(range)).peekable();
        while let Some((key, _, value)) = iter.next().transpose()? {
            match iter.peek() {
                Some(Ok((next, _, _,) )) if next == &key => continue,
                Some(Err(err)) => return Err(err.clone()),
                Some(Ok(_)) | None => {},
            }
            let Some(value) = bincode::deserialize(&value)? else {
                continue;
            };

            self.buffer.push_back((key, value));
            if self.buffer.len() == Self::BUFFER_SIZE {
                if let Some((next, version, _)) = iter.next().transpose()? {
                    let range_start = Bound::Included(Key::Version(next.into(), version).encode());
                    self.remainder = Some((range_start, range_end));
                }
                return Ok(());
            }
        }

        Ok(())
    }

}

impl<E: Engine> Iterator for ScanIterator<E > {
    type Item = Result<(Vec<u8>, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.buffer.is_empty() {
            if let Err(err) = self.fill_buffer() {
                return Some(Err(err));
            }
        }

        self.buffer.pop_front().map(Ok)
    }
}


pub struct VersionIterator<'a, I: engine::ScanIterator> {
    txn: &'a TransactionState,
    inner: I,
}

impl<'a, I: engine::ScanIterator> VersionIterator<'a, I> {
    fn new(txn: &'a TransactionState, inner: I) -> Self {
        Self { txn, inner}
    }

    fn try_next(&mut self) -> Result<Option<(Vec<u8>, Version, Vec<u8>)>> {
        while let Some((key, value)) = self.inner.next().transpose()? {
            let Key::Version(key, version) = Key::decode(&key)? else {
                return errdata!("expected Key::Version, got {key:?}");
            };
            if !self.txn.is_visible(version) {
                continue;
            }

            return Ok(Some((key.into_owned(), version, value)));

        }
        Ok(None)
    }
}

impl<I: engine::ScanIterator> Iterator for VersionIterator<'_, I> {
    type Item = Result<(Vec<u8>, Version, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.try_next().transpose()
    }
}


/// Most storage tests are Goldenscripts under src/storage/testscripts.
#[cfg(test)]
pub mod tests {
    use std::collections::HashMap;
    use std::error::Error;
    use std::fmt::Write as _;
    use std::path::Path;
    use std::result::Result;

    use crossbeam::channel::Receiver;
    use tempfile::TempDir;
    use test_case::test_case;
    use test_each_file::test_each_path;

    use super::*;
    use crate::encoding::format::{self, Formatter as _};
    use crate::storage::engine::test::{Emit, Mirror, Operation, decode_binary, parse_key_range};
    use crate::storage::{BitCask, Memory};

    // Run goldenscript tests in src/storage/testscripts/mvcc.
    test_each_path! { in "src/storage/testscripts/mvcc" as scripts => test_goldenscript }

    fn test_goldenscript(path: &Path) {
        goldenscript::run(&mut MVCCRunner::new(), path).expect("goldenscript failed")
    }

    /// Tests that key prefixes are actually prefixes of keys.
    #[test_case(KeyPrefix::NextVersion, Key::NextVersion; "NextVersion")]
    #[test_case(KeyPrefix::TxnActive, Key::TxnActive(1); "TxnActive")]
    #[test_case(KeyPrefix::TxnActiveSnapshot, Key::TxnActiveSnapshot(1); "TxnActiveSnapshot")]
    #[test_case(KeyPrefix::TxnWrite(1), Key::TxnWrite(1, b"foo".as_slice().into()); "TxnWrite")]
    #[test_case(KeyPrefix::Version(b"foo".as_slice().into()), Key::Version(b"foo".as_slice().into(), 1); "Version")]
    #[test_case(KeyPrefix::Unversioned, Key::Unversioned(b"foo".as_slice().into()); "Unversioned")]
    fn key_prefix(prefix: KeyPrefix, key: Key) {
        let prefix = prefix.encode();
        let key = key.encode();
        assert_eq!(prefix, key[..prefix.len()])
    }

    /// Runs MVCC goldenscript tests.
    pub struct MVCCRunner {
        mvcc: MVCC<TestEngine>,
        txns: HashMap<String, Transaction<TestEngine>>,
        op_rx: Receiver<Operation>,
        _tempdir: TempDir,
    }

    type TestEngine = Emit<Mirror<BitCask, Memory>>;

    impl MVCCRunner {
        fn new() -> Self {
            // Use both a BitCask and a Memory engine, and mirror operations
            // across them. Emit engine operations to op_rx.
            let (op_tx, op_rx) = crossbeam::channel::unbounded();
            let tempdir = TempDir::with_prefix("toydb").expect("tempdir failed");
            let bitcask = BitCask::new(tempdir.path().join("bitcask")).expect("bitcask failed");
            let memory = Memory::new();
            let engine = Emit::new(Mirror::new(bitcask, memory), op_tx);
            let mvcc = MVCC::new(engine);
            Self { mvcc, op_rx, txns: HashMap::new(), _tempdir: tempdir }
        }

        /// Fetches the named transaction from a command prefix.
        fn get_txn(
            &mut self,
            prefix: &Option<String>,
        ) -> Result<&'_ mut Transaction<TestEngine>, Box<dyn Error>> {
            let name = Self::txn_name(prefix)?;
            self.txns.get_mut(name).ok_or(format!("unknown txn {name}").into())
        }

        /// Fetches the txn name from a command prefix, or errors.
        fn txn_name(prefix: &Option<String>) -> Result<&str, Box<dyn Error>> {
            prefix.as_deref().ok_or("no txn name".into())
        }

        /// Errors if a txn prefix is given.
        fn no_txn(command: &goldenscript::Command) -> Result<(), Box<dyn Error>> {
            if let Some(name) = &command.prefix {
                return Err(format!("can't run {} with txn {name}", command.name).into());
            }
            Ok(())
        }
    }

    impl goldenscript::Runner for MVCCRunner {
        fn run(&mut self, command: &goldenscript::Command) -> Result<String, Box<dyn Error>> {
            let mut output = String::new();
            let mut tags = command.tags.clone();

            match command.name.as_str() {
                // txn: begin [readonly] [as_of=VERSION]
                "begin" => {
                    let name = Self::txn_name(&command.prefix)?;
                    if self.txns.contains_key(name) {
                        return Err(format!("txn {name} already exists").into());
                    }
                    let mut args = command.consume_args();
                    let readonly = match args.next_pos().map(|a| a.value.as_str()) {
                        Some("readonly") => true,
                        None => false,
                        Some(v) => return Err(format!("invalid argument {v}").into()),
                    };
                    let as_of = args.lookup_parse("as_of")?;
                    args.reject_rest()?;
                    let txn = match (readonly, as_of) {
                        (false, None) => self.mvcc.begin()?,
                        (true, None) => self.mvcc.begin_read_only()?,
                        (true, Some(v)) => self.mvcc.begin_as_of(v)?,
                        (false, Some(_)) => return Err("as_of only valid for read-only txn".into()),
                    };
                    self.txns.insert(name.to_string(), txn);
                }

                // txn: commit
                "commit" => {
                    let name = Self::txn_name(&command.prefix)?;
                    let txn = self.txns.remove(name).ok_or(format!("unknown txn {name}"))?;
                    command.consume_args().reject_rest()?;
                    txn.commit()?;
                }

                // txn: delete KEY...
                "delete" => {
                    let txn = self.get_txn(&command.prefix)?;
                    let mut args = command.consume_args();
                    for arg in args.rest_pos() {
                        let key = decode_binary(&arg.value);
                        txn.delete(&key)?;
                    }
                    args.reject_rest()?;
                }

                // dump
                "dump" => {
                    command.consume_args().reject_rest()?;
                    let mut engine = self.mvcc.engine.lock().unwrap();
                    let mut scan = engine.scan(..);
                    while let Some((key, value)) = scan.next().transpose()? {
                        let fmtkv = format::MVCC::<format::Raw>::key_value(&key, &value);
                        let rawkv = format::Raw::key_value(&key, &value);
                        writeln!(output, "{fmtkv} [{rawkv}]")?;
                    }
                }

                // txn: get KEY...
                "get" => {
                    let txn = self.get_txn(&command.prefix)?;
                    let mut args = command.consume_args();
                    for arg in args.rest_pos() {
                        let key = decode_binary(&arg.value);
                        let value = txn.get(&key)?;
                        let fmtkv = format::Raw::key_maybe_value(&key, value.as_deref());
                        writeln!(output, "{fmtkv}")?;
                    }
                    args.reject_rest()?;
                }

                // get_unversioned KEY...
                "get_unversioned" => {
                    Self::no_txn(command)?;
                    let mut args = command.consume_args();
                    for arg in args.rest_pos() {
                        let key = decode_binary(&arg.value);
                        let value = self.mvcc.get_unversioned(&key)?;
                        let fmtkv = format::Raw::key_maybe_value(&key, value.as_deref());
                        writeln!(output, "{fmtkv}")?;
                    }
                    args.reject_rest()?;
                }

                // import [VERSION] KEY=VALUE...
                "import" => {
                    Self::no_txn(command)?;
                    let mut args = command.consume_args();
                    let version = args.next_pos().map(|a| a.parse()).transpose()?;
                    let mut txn = self.mvcc.begin()?;
                    if let Some(version) = version {
                        if txn.version() > version {
                            return Err(format!("version {version} already used").into());
                        }
                        while txn.version() < version {
                            txn = self.mvcc.begin()?;
                        }
                    }
                    for kv in args.rest_key() {
                        let key = decode_binary(kv.key.as_ref().unwrap());
                        let value = decode_binary(&kv.value);
                        if value.is_empty() {
                            txn.delete(&key)?;
                        } else {
                            txn.set(&key, value)?;
                        }
                    }
                    args.reject_rest()?;
                    txn.commit()?;
                }

                // txn: resume JSON
                "resume" => {
                    let name = Self::txn_name(&command.prefix)?;
                    let mut args = command.consume_args();
                    let raw = &args.next_pos().ok_or("state not given")?.value;
                    args.reject_rest()?;
                    let state: TransactionState = serde_json::from_str(raw)?;
                    let txn = self.mvcc.resume(state)?;
                    self.txns.insert(name.to_string(), txn);
                }

                // txn: rollback
                "rollback" => {
                    let name = Self::txn_name(&command.prefix)?;
                    let txn = self.txns.remove(name).ok_or(format!("unknown txn {name}"))?;
                    command.consume_args().reject_rest()?;
                    txn.rollback()?;
                }

                // txn: scan [RANGE]
                "scan" => {
                    let txn = self.get_txn(&command.prefix)?;
                    let mut args = command.consume_args();
                    let range =
                        parse_key_range(args.next_pos().map(|a| a.value.as_str()).unwrap_or(".."))?;
                    args.reject_rest()?;

                    let kvs: Vec<_> = txn.scan(range).try_collect()?;
                    for (key, value) in kvs {
                        writeln!(output, "{}", format::Raw::key_value(&key, &value))?;
                    }
                }

                // txn: scan_prefix PREFIX
                "scan_prefix" => {
                    let txn = self.get_txn(&command.prefix)?;
                    let mut args = command.consume_args();
                    let prefix = decode_binary(&args.next_pos().ok_or("prefix not given")?.value);
                    args.reject_rest()?;

                    let kvs: Vec<_> = txn.scan_prefix(&prefix).try_collect()?;
                    for (key, value) in kvs {
                        writeln!(output, "{}", format::Raw::key_value(&key, &value))?;
                    }
                }

                // txn: set KEY=VALUE...
                "set" => {
                    let txn = self.get_txn(&command.prefix)?;
                    let mut args = command.consume_args();
                    for kv in args.rest_key() {
                        let key = decode_binary(kv.key.as_ref().unwrap());
                        let value = decode_binary(&kv.value);
                        txn.set(&key, value)?;
                    }
                    args.reject_rest()?;
                }

                // set_unversioned KEY=VALUE...
                "set_unversioned" => {
                    Self::no_txn(command)?;
                    let mut args = command.consume_args();
                    for kv in args.rest_key() {
                        let key = decode_binary(kv.key.as_ref().unwrap());
                        let value = decode_binary(&kv.value);
                        self.mvcc.set_unversioned(&key, value)?;
                    }
                    args.reject_rest()?;
                }

                // txn: state
                "state" => {
                    command.consume_args().reject_rest()?;
                    let txn = self.get_txn(&command.prefix)?;
                    let state = txn.state();
                    write!(
                        output,
                        "v{} {} active={{{}}}",
                        state.version,
                        if state.read_only { "ro" } else { "rw" },
                        state.active.iter().sorted().join(",")
                    )?;
                }

                // status
                "status" => writeln!(output, "{:#?}", self.mvcc.status()?)?,

                name => return Err(format!("invalid command {name}").into()),
            }

            // If requested, output engine operations.
            if tags.remove("ops") {
                while let Ok(op) = self.op_rx.try_recv() {
                    match op {
                        Operation::Delete { key } => {
                            let fmtkey = format::MVCC::<format::Raw>::key(&key);
                            let rawkey = format::Raw::key(&key);
                            writeln!(output, "engine delete {fmtkey} [{rawkey}]")?
                        }
                        Operation::Flush => writeln!(output, "engine flush")?,
                        Operation::Set { key, value } => {
                            let fmtkv = format::MVCC::<format::Raw>::key_value(&key, &value);
                            let rawkv = format::Raw::key_value(&key, &value);
                            writeln!(output, "engine set {fmtkv} [{rawkv}]")?
                        }
                    }
                }
            }

            if let Some(tag) = tags.iter().next() {
                return Err(format!("unknown tag {tag}").into());
            }

            Ok(output)
        }

        // Drain unhandled engine operations.
        fn end_command(&mut self, _: &goldenscript::Command) -> Result<String, Box<dyn Error>> {
            while self.op_rx.try_recv().is_ok() {}
            Ok(String::new())
        }
    }
}

