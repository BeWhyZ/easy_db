

use std::collections::btree_map::Range;
use std::collections::BTreeMap;
use std::ops::{RangeBounds, Bound};

use super::{Engine, Status};
use crate::error::Result;


// define memory storage
#[derive(Default)]
pub struct Memory(BTreeMap<Vec<u8>, Vec<u8>>);

impl Memory {
    pub fn new() -> Self {
        Self::default()
    }
}

// impl engine for memory storage
impl Engine for Memory {
    type ScanIterator<'a> = ScanIterator<'a>;


    // Delete a key, or do nothing if the key does not exist.
    fn delete(&mut self, key: &[u8]) -> Result<()> {
        self.0.remove(key);
        Ok(())
    }

    // flush any buffered data to disk
    fn flush(&mut self) -> Result<()>{
        // no-op for memory storage
        Ok(())
    }

    fn get(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        Ok(self.0.get(key).cloned())
    }

    fn scan(&mut self, range: impl RangeBounds<Vec<u8>>) -> Self::ScanIterator<'_>
    where
        Self: Sized{
            ScanIterator(self.0.range(range))
        }

    fn scan_dyn(&mut self, range: (Bound<Vec<u8>>, Bound<Vec<u8>>)) -> Box<dyn super::ScanIterator + '_>{
        unimplemented!()
    }

    fn set(&mut self, key: &[u8], value: Vec<u8>) -> Result<()>{
        unimplemented!()
    }

    fn status(&mut self) -> Result<Status>{
        unimplemented!()
    }



}

// new scanIterator for scan
pub struct ScanIterator<'a>(Range<'a, Vec<u8>, Vec<u8>>);

impl Iterator for ScanIterator<'_> {
    type Item = Result<(Vec<u8>, Vec<u8>)>;


    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(k,v)| { Ok((k.clone(), v.clone()))})
    }

}

impl DoubleEndedIterator for ScanIterator<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|(k, v)| Ok((k.clone(), v.clone())))
    }
}



