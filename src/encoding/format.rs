//! Decodes and formats raw keys and values, recursively as needed. Handles both
//! both Raft, MVCC, SQL, and raw binary data.

use super::{bincode, Key as _, Value as _};

use itertools::Itertools as _;
use std::collections::BTreeSet;

/// Formats raw key/value pairs.
pub trait Formatter {
    /// Formats a key.
    fn key(key: &[u8]) -> String;

    /// Formats a value.
    fn value(key: &[u8], value: &[u8]) -> String;

    /// Formats a key/value pair.
    fn key_value(key: &[u8], value: &[u8]) -> String {
        Self::key_maybe_value(key, Some(value))
    }

    /// Formats a key/value pair, where the value may not exist.
    fn key_maybe_value(key: &[u8], value: Option<&[u8]>) -> String {
        let fkey = Self::key(key);
        let fvalue = value
            .map(|v| Self::value(key, v))
            .unwrap_or("None".to_string());
        format!("{fkey} → {fvalue}")
    }
}

/// Formats raw byte slices.
pub struct Raw;

impl Raw {
    pub fn bytes(bytes: &[u8]) -> String {
        let escaped = bytes
            .iter()
            .copied()
            .flat_map(std::ascii::escape_default)
            .collect_vec();
        let string = String::from_utf8_lossy(&escaped);
        format!("\"{string}\"")
    }
}

impl Formatter for Raw {
    fn key(key: &[u8]) -> String {
        Self::bytes(key)
    }

    fn value(_: &[u8], value: &[u8]) -> String {
        Self::bytes(value)
    }
}
