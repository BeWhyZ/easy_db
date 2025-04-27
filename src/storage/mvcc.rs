use std::borrow::Cow;
use std::collections::BTreeSet;
use std::sync::{Arc, Mutex};

use serde::{Deserialize, Serialize};

use crate::encoding;
use crate::error::Result;
use crate::storage::engine::Engine;

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
    TxnActive(Version),
    TxnActiveSnapshot(Version),
    TxnWrite(Version),
    Version(
        #[serde(with = "serde_bytes")]
        #[serde(borrow)]
        Cow<'a, [u8]>,
    ),
    Unversioned,
}

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
}

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

impl<E: Engine> Transaction<E> {
    pub fn begin(engine: Arc<Mutex<E>>) -> Result<Self> {
        
    }
}
