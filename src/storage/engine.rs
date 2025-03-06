use std::ops::{Bound, RangeBounds};

use serde::{Deserialize, Serialize, Serializer};

use crate::encoding::keycode;
use crate::error::Result;


pub trait Engine: Send {
    // the iterator returned by [`Engine::scan`]
    type ScanIterator<'a>: ScanIterator + 'a
    where
        Self: Sized + 'a;

    // Delete a key, or do nothing if the key does not exist.
    fn delete(&mut self, key: &[u8]) -> Result<()>;

    // flush any buffered data to disk
    fn flush(&mut self) -> Result<()>;

    fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>>;

    fn scan(&mut self, range: impl RangeBounds<Vec<u8>>) -> Self::ScanIterator<'_>
    where
        Self: Sized;

    fn scan_dyn(&mut self, range: (Bound<Vec<u8>>, Bound<Vec<u8>>)) -> Box<dyn ScanIterator + '_>;

    fn scan_prefix(&mut self, prefix: &[u8]) -> Self::ScanIterator<'_>
    where
        Self: Sized,
    {
        self.scan(keycode::prefix_range(prefix))
    }

    fn set(&mut self, key: &[u8], value: Vec<u8>) -> Result<()>;

    fn status(&mut self) -> Result<Status>;

}

/// A scan Iterator over key/value pair, returned by [`Engine::scan`]
pub trait ScanIterator: DoubleEndedIterator<Item = Result<(Vec<u8>, Vec<u8>)>> {}

impl<I: DoubleEndedIterator<Item = Result<(Vec<u8>, Vec<u8>)>>> ScanIterator for I {}


#[derive(Clone, Debug, PartialEq, Deserialize, Serialize)]
pub struct Status {
    pub name: String,
    pub keys: u64,
    pub size:u64,
    pub disk_size: u64,
    pub live_disk_size: u64,
}

impl Status {
    pub fn garbage_disk_size(&self) -> u64 {
        self.disk_size - self.live_disk_size
    }

    pub fn garbage_disk_percent(&self,) -> f64 {
        if self.disk_size == 0{
            return 0.0;
        }
        self.garbage_disk_size() as f64 / self.disk_size as f64
    }
}


