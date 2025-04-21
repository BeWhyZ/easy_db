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

#[macro_export]
macro_rules! errdata {
    ($($args:tt)*) => {$crate::error::Error::InvaildData(format!($($args)*).into())};
}

#[macro_export]
macro_rules! errinput {
    ($($args:tt)*) => {$crate::error::Error::InvalidInput(format!($($args)*).into())};
}

/// A type alias for `Result<T, Error>`. and specify unified error to result 
pub type Result<T> = std::result::Result<T, Error>;


impl<T> From<Error> for Result<T> {
    fn from(e: Error) -> Self {
        Err(e)
    }
}

impl serde::de::Error for Error{
    fn custom<T>(msg: T) -> Self
        where
            T: Display,
        {
            Error::InvalidData(msg.to_string())
        }
}

impl serde::ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error::InvalidData(msg.to_string())
    }
}

impl From<Box<bincode::error::DecodeError>> for Error {
    fn from(err: Box<bincode::error::DecodeError>) -> Self {
        Error::InvalidData(err.to_string())
    }
}

impl From<Box<bincode::error::EncodeError>> for Error {
    fn from(err: Box<bincode::error::EncodeError>) -> Self {
        Error::InvalidData(err.to_string())
    }
}

impl From<config::ConfigError> for Error {
    fn from(err: config::ConfigError) -> Self {
        Error::InvalidInput(err.to_string())
    }
}

impl From<crossbeam::channel::RecvError> for Error {
    fn from(err: crossbeam::channel::RecvError) -> Self {
        Error::IO(err.to_string())
    }
}

impl<T> From<crossbeam::channel::SendError<T>> for Error {
    fn from(err: crossbeam::channel::SendError<T>) -> Self {
        Error::IO(err.to_string())
    }
}

/// impl crossbeam error for error, RecvError, SendError, TryRecvError, TrySendError

impl From<crossbeam::channel::TryRecvError> for Error {
    fn from(err: crossbeam::channel::TryRecvError) -> Self {
        Error::IO(err.to_string())
    }
}

impl<T> From<crossbeam::channel::TrySendError<T>> for Error {
    fn from(err: crossbeam::channel::TrySendError<T>) -> Self {
        Error::IO(err.to_string())
    }
}

/// impl hdrhistogram error for Error, CreationError, RecordError, 
impl From<hdrhistogram::CreationError> for Error {
    fn from(err: hdrhistogram::CreationError) -> Self {
        panic!("{err}") // faulty code
    }
}

impl From<hdrhistogram::RecordError> for Error {
    fn from(err: hdrhistogram::RecordError)  -> Self {
        Error::InvalidInput(err.to_string())
    }
}

impl From<log::ParseLevelError> for Error {
    fn from(err: log::ParseLevelError) -> Self {
        Error::InvalidInput(err.to_string())
    }
}

impl From<log::SetLoggerError> for Error {
    fn from(err: log::SetLoggerError) -> Self {
        panic!("{err}") // faulty code
    }
}

impl From<regex::Error> for Error {
    fn from(err: regex::Error) -> Self {
        panic!("{err}") // faulty code
    }
}

impl From<rustyline::error::ReadlineError> for Error {
    fn from(err: rustyline::error::ReadlineError) -> Self {
        Error::IO(err.to_string())
    }
}

impl From<std::array::TryFromSliceError> for Error {
    fn from(err: std::array::TryFromSliceError) -> Self {
        Error::InvalidData(err.to_string())
    }
}

impl From<std::io::Error> for Error {
    fn from(err: std::io::Error) -> Self {
        Error::IO(err.to_string())
    }
}

impl From<std::num::ParseFloatError> for Error {
    fn from(err: std::num::ParseFloatError) -> Self {
        Error::InvalidInput(err.to_string())
    }
}

impl From<std::num::ParseIntError> for Error {
    fn from(err: std::num::ParseIntError) -> Self {
        Error::InvalidInput(err.to_string())
    }
}

impl From<std::num::TryFromIntError> for Error {
    fn from(err: std::num::TryFromIntError) -> Self {
        Error::InvalidData(err.to_string())
    }
}

impl From<std::string::FromUtf8Error> for Error {
    fn from(err: std::string::FromUtf8Error) -> Self {
        Error::InvalidData(err.to_string())
    }
}

impl<T> From<std::sync::PoisonError<T>> for Error {
    fn from(err: std::sync::PoisonError<T>) -> Self {
        // This only happens when a different thread panics while holding a
        // mutex. This should be fatal, so we panic here too.
        panic!("{err}")
    }
}

