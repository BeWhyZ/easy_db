use std::fmt::Display;

use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
pub enum Error {
    Abort,
    InvalidData(String),
    InvalidInput(String),
    IO(String),
    ReadOnly,
    Serialization,
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Abort => write!(f, "abort"),
            Error::InvalidData(ref msg) => write!(f, "invalid data: {msg}"),
            Error::InvalidInput(ref msg) => write!(f, "invalid input: {msg}"),
            Error::IO(ref msg) => write!(f, "io error: {msg}"),
            Error::ReadOnly => write!(f, "read only"),
            Error::Serialization => write!(f, "serialization error"),
        }
    }
}

impl Error {
    pub fn is_deterministic(&self) -> bool {
        match self {
            // Aborts don't happen during application, only leader changes. But
            // we consider them non-deterministic in case an abort should happen
            // unexpectedly below Raft.
            Error::Abort => false,
            // Possible data corruption local to this node.
            Error::InvalidData(_) => false,
            // Input errors are (likely) deterministic. They might not be in
            // case data was corrupted in flight, but we ignore this case.
            Error::InvalidInput(_) => true,
            // IO errors are typically local to the node (e.g. faulty disk).
            Error::IO(_) => false,
            // Write commands in read-only transactions are deterministic.
            Error::ReadOnly => true,
            // Write conflicts are determinstic.
            Error::Serialization => true,
        }
    }
}
