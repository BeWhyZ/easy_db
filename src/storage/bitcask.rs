// std import 
use std::collections::BTreeMap;
use std::collections::btree_map::Range;
use std::fs::{ File};
use std::path::PathBuf;
use std::io::{BufReader, BufWriter, SeekFrom, Seek as _, Read as _, Write as _};
use std::result::Result as StdResult;
use std::ops::{RangeBounds, Bound};

// third-party import
use fs4::fs_std::FileExt;
use log::{error, info};

// project import
use crate::error::{Result, Error};
use super::{Engine, Status};

pub struct BitCask {
    log: Log,
    keydir: KeyDir,
}

impl BitCask {
    pub fn new(path: PathBuf) -> Result<Self> {
        info!("opening database {path:?}");
        let mut log = Log::new(path.clone())?;
        let keydir = log.build_keydir()?;
        info!("Indexed {} live keys in {}", keydir.len(), path.display());
        Ok(Self{
            log,
            keydir,
        })
    }

    pub fn new_maybe_compact(
        path: PathBuf,
        garbage_min_fraction: f64,
        garbage_min_bytes: u64,
    ) -> Result<Self> {

        let mut engine = Self::new(path)?;
        let status = engine.status()?;
        let garbage_size = status.garbage_disk_size();
        let garbage_fraction = garbage_size as f64 / status.disk_size as f64;
        if garbage_size > 0 
            && garbage_fraction >= garbage_min_fraction 
            && garbage_size >= garbage_min_bytes 
            {
                info!(
                    "Compacting {} to remove {:.0}% garbage {:.1} MB out of {:.1} MB",
                    engine.log.path.display(),
                    garbage_fraction * 100 as f64,
                    garbage_size as f64 / (1024 * 1024) as f64,
                    status.disk_size as f64 / (1024 * 1024) as f64,
                );
                engine.compact()?;
                info!(
                    "Compacted {} to size {:.1} MB",
                    engine.log.path.display(),
                    (status.disk_size - garbage_size) as f64 / (1024 * 1024) as f64,
                );
            }

        return Ok(engine)
        
    }
}


impl Engine for BitCask {
    type ScanIterator<'a> = ScanIterator<'a>;

    fn delete(&mut self, key: &[u8]) -> Result<()> {
        self.log.write_entry(key, None)?;
        self.keydir.remove(key);
        Ok(())
    }

    // flush any buffered data to disk
    fn flush(&mut self) -> Result<()> {
        // Don't fsync in tests, to speed them up. We disable this here, instead
        // of setting `raft::Log::fsync = false` in tests, because we want to
        // assert that the Raft log flushes to disk even if the flush is a noop.
        #[cfg(not(test))]
        self.log.file.sync_all()?;
        Ok(())
    }

    fn get(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        let Some(val_loc) = self.keydir.get(key) else {
            return Ok(None);
        };
        self.log.read_value(*val_loc).map(Some)
    }

    fn scan(&mut self, range: impl RangeBounds<Vec<u8>>) -> Self::ScanIterator<'_>
    where
        Self: Sized {
            ScanIterator {
                inner: self.keydir.range(range),
                log:&mut self.log,
            }
        }

    fn scan_dyn(&mut self, range: (Bound<Vec<u8>>, Bound<Vec<u8>>)) -> Box<dyn super::ScanIterator + '_> {
        Box::new(self.scan(range))
    }

    fn set(&mut self, key: &[u8], value: Vec<u8>) -> Result<()> {
        let val_loc = self.log.write_entry(key, Some(&*value))?;
        self.keydir.insert(key.to_vec(), val_loc);
        Ok(())
    }

    fn status(&mut self) -> Result<Status> {
        let keys = self.keydir.len() as u64;
        let size = self.keydir.iter().map(|(k, vl)| (k.len() + vl.length) as u64).sum();
        let disk_size = self.log.file.metadata()?.len();
        let live_disk_size = size + 8 * keys;
        Ok(Status {
            name: "bitcask".to_string(),
            keys,
            size,
            disk_size,
            live_disk_size,
        })
    }



}

impl BitCask {

    /// Compacts the current log file by writing out a new log file containing
    /// only live keys and replacing the current file with it.
    fn compact(&mut self) -> Result<()> {
        let new_path = self.log.path.with_extension("new");
        let mut new_log = Log::new(new_path)?;

        let mut new_keydir = KeyDir::new();
        for (k, val_loc) in &self.keydir {
            let value = self.log.read_value(*val_loc)?;
            let val_loc = new_log.write_entry(k, Some(&value))?;
            new_keydir.insert(k.clone(), val_loc);
        }

        // rename the new log to the old
        std::fs::rename(&new_log.path, &self.log.path)?;
        new_log.path = self.log.path.clone();
        self.log = new_log;
        self.keydir = new_keydir;

        Ok(())
        
    }
}


pub struct ScanIterator<'a> {
    inner: Range<'a, Vec<u8>, ValueLocation>,
    log: &'a mut Log,
}

impl ScanIterator<'_> {
    fn map(&mut self, item: (&Vec<u8>, &ValueLocation)) -> <Self as Iterator>::Item {
        let (key, value_loc) = item;
        Ok((key.clone(), self.log.read_value(*value_loc)?))
    }
}


impl Iterator for ScanIterator<'_> {
    type Item = Result<(Vec<u8>, Vec<u8>)>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|item|self.map(item))
    }
}

impl DoubleEndedIterator for ScanIterator<'_> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.next_back().map(|item|self.map(item))
    }
}

type KeyDir = BTreeMap<Vec<u8>, ValueLocation>;

#[derive(Clone, Copy)]
pub struct ValueLocation {
    offset: u64,
    length: usize,
}

impl ValueLocation {
    fn end(&self,) -> u64 {
        self.offset + self.length as u64
    }
}


/// A BitCask append-only log file, containing a sequence of key/value
/// entries encoded as follows;
///
/// 1. Key length as big-endian u32 [4 bytes].
/// 2. Value length as big-endian i32, or -1 for tombstones [4 bytes].
/// 3. Key as raw bytes [<= 2 GB].
/// 4. Value as raw bytes [<= 2 GB].
struct Log {
    file: File,
    path: PathBuf,
}

impl Log {
    fn new(path: PathBuf) -> Result<Self> {
        if let Some(dir) = path.parent() {
            std::fs::create_dir_all(dir)?
        }
        let file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(&path)?;

        // get lock
        if !file.try_lock_exclusive()?{
            return Err(Error::IO(format!("file {path:?} is already locked")));

        }
        Ok(Self {file, path})
    }

    fn build_keydir(&mut self) -> Result<KeyDir>{
        let mut len_buf = [0u8; 4];
        let mut keydir = KeyDir::new();
        let file_len = self.file.metadata()?.len();
        let mut r = BufReader::new(&mut self.file);
        let mut offset = r.seek(SeekFrom::Start(0))?;

        while offset < file_len {
            // Read the next entry from the file, returning the key and value
            // location, or None for tombstones.
            let result = || -> StdResult<(Vec<u8>, Option<ValueLocation>), std::io::Error> {
                // Read the key length: 4-byte u32.
                r.read_exact(&mut len_buf)?;
                let key_len = u32::from_be_bytes(len_buf);

                // Read the value length: 4-byte i32, -1 for tombstones.
                r.read_exact(&mut len_buf)?;
                let value_loc = match i32::from_be_bytes(len_buf) {
                    ..0 => None, // tombstone
                    len => Some(ValueLocation {
                        offset: offset + 8 + key_len as u64,
                        length: len as usize,
                    }),
                };

                // Read the key.
                let mut key = vec![0; key_len as usize];
                r.read_exact(&mut key)?;

                // Skip past the value.
                if let Some(value_loc) = value_loc {
                    if value_loc.end() > file_len {
                        return Err(std::io::Error::new(
                            std::io::ErrorKind::UnexpectedEof,
                            "value extends beyond end of file",
                        ));
                    }
                    r.seek_relative(value_loc.length as i64)?;
                }

                // Update the file offset.
                offset += 8 + key_len as u64 + value_loc.map_or(0, |v| v.length) as u64;

                Ok((key, value_loc))
            }();

            // Update the keydir with the entry.
            match result {
                Ok((key, Some(value_loc))) => keydir.insert(key, value_loc),
                Ok((key, None)) => keydir.remove(&key),
                // If an incomplete entry was found at the end of the file, assume an
                // incomplete write and truncate the file.
                Err(err) if err.kind() == std::io::ErrorKind::UnexpectedEof => {
                    error!("Found incomplete entry at offset {offset}, truncating file");
                    self.file.set_len(offset)?;
                    break;
                }
                Err(err) => return Err(err.into()),
            };
        }

        Ok(keydir)

    }

    // read the value from the log file
    fn read_value(&mut self, location: ValueLocation) -> Result<Vec<u8>> {
        let mut value = vec![0u8; location.length];
        self.file.seek(SeekFrom::Start(location.offset))?;
        self.file.read_exact(&mut value)?;
        Ok(value)
    }

    fn write_entry(&mut self, key: &[u8], value: Option<&[u8]>) -> Result<ValueLocation> {
        let length = key.len() + value.map_or(0, |v| v.len()) + 8;
        let offset = self.file.seek(SeekFrom::End(0))?;
        let mut w = BufWriter::with_capacity(length, &mut self.file);

        // write the key and value length
        w.write_all(&(key.len() as u32).to_be_bytes())?;
        w.write_all(&value.map_or(-1, |v| v.len() as i32).to_be_bytes())?;

        // the key and value
        w.write_all(key)?;
        w.write_all(value.unwrap_or_default())?;
        // flush buffer to file
        w.flush()?;

        // translate the entry location into a value location
        Ok(ValueLocation {
            offset: offset + 8 + key.len() as u64,
            length: value.map_or(0, |v| v.len()),
        })


    }
}



/// Most storage tests are Goldenscripts under src/storage/testscripts.
#[cfg(test)]
mod tests {
    use std::error::Error as StdError;
    use std::fmt::Write as _;

    use tempfile::TempDir;
    use test_each_file::test_each_path;

    use super::super::engine::test::Runner;
    use super::*;
    use crate::encoding::format::{self, Formatter as _};

    // Run common goldenscript tests in src/storage/testscripts/engine.
    test_each_path! { in "src/storage/testscripts/engine" as engine => test_goldenscript }

    // Also run BitCask-specific tests in src/storage/testscripts/bitcask.
    test_each_path! { in "src/storage/testscripts/bitcask" as scripts => test_goldenscript }

    fn test_goldenscript(path: &std::path::Path) {
        goldenscript::run(&mut BitCaskRunner::new(), path).expect("goldenscript failed")
    }

    /// Tests that exclusive locks are taken out on log files, erroring if held,
    /// and released when the database is closed.
    #[test]
    fn lock() -> Result<()> {
        let path = TempDir::with_prefix("toydb")?.path().join("bitcask");
        let engine = BitCask::new(path.clone()).expect("bitcask failed");

        // Opening another database with the same file should error.
        assert!(BitCask::new(path.clone()).is_err());

        // Opening another database after the current is closed works.
        drop(engine);
        assert!(BitCask::new(path).is_ok());
        Ok(())
    }

    /// Tests that a log with an incomplete write at the end can be recovered by
    /// discarding the last entry.
    #[test]
    fn recovery() -> Result<()> {
        // Create an initial log file with a few entries. Keep track of where
        // each entry ends.
        let dir = TempDir::with_prefix("toydb")?;
        let path = dir.path().join("complete");
        let mut log = Log::new(path.clone())?;

        let mut ends = vec![];
        let value_loc = log.write_entry("deleted".as_bytes(), Some(&[1, 2, 3]))?;
        ends.push(value_loc.end());
        let value_loc = log.write_entry("deleted".as_bytes(), None)?;
        ends.push(value_loc.end());
        let value_loc = log.write_entry(&[], Some(&[]))?;
        ends.push(value_loc.end());
        let value_loc = log.write_entry("key".as_bytes(), Some(&[1, 2, 3, 4, 5]))?;
        ends.push(value_loc.end());
        drop(log);

        // Copy the file, and truncate it at each byte, then try to open it
        // and assert that we always retain a prefix of entries.
        let truncpath = dir.path().join("truncated");
        let size = std::fs::metadata(&path)?.len();
        for pos in 0..=size {
            std::fs::copy(&path, &truncpath)?;
            let f = std::fs::OpenOptions::new().write(true).open(&truncpath)?;
            f.set_len(pos)?;
            drop(f);

            let mut expect = vec![];
            if pos >= ends[0] {
                expect.push((b"deleted".to_vec(), vec![1, 2, 3]))
            }
            if pos >= ends[1] {
                expect.pop(); // "deleted" key removed
            }
            if pos >= ends[2] {
                expect.push((b"".to_vec(), vec![]))
            }
            if pos >= ends[3] {
                expect.push((b"key".to_vec(), vec![1, 2, 3, 4, 5]))
            }

            let mut engine = BitCask::new(truncpath.clone())?;
            let get = engine.scan(..).collect::<Result<Vec<_>>>()?;
            assert_eq!(expect, get);
        }
        Ok(())
    }

    /// Tests key/value sizes up to 64 MB.
    #[test]
    fn point_ops_sizes() -> Result<()> {
        let path = TempDir::with_prefix("toydb")?.path().join("bitcask");
        let mut engine = BitCask::new(path.clone()).expect("bitcask failed");

        // Generate keys/values for increasing powers of two.
        for size in (1..=26).map(|i| 1 << i) {
            let value = vec![b'x'; size];
            let key = value.as_slice();

            assert_eq!(engine.get(key)?, None);
            engine.set(key, value.clone())?;
            assert_eq!(engine.get(key)?.as_ref(), Some(&value));
            engine.delete(key)?;
            assert_eq!(engine.get(key)?, None);
        }
        Ok(())
    }

    /// A BitCask-specific goldenscript runner, which dispatches through to the
    /// standard Engine runner.
    struct BitCaskRunner {
        inner: Runner<BitCask>,
        tempdir: TempDir,
    }

    impl goldenscript::Runner for BitCaskRunner {
        fn run(&mut self, command: &goldenscript::Command) -> StdResult<String, Box<dyn StdError>> {
            let mut output = String::new();
            match command.name.as_str() {
                // compact
                // Compacts the BitCask entry log.
                "compact" => {
                    command.consume_args().reject_rest()?;
                    self.inner.engine.compact()?;
                }

                // dump
                // Dumps the full BitCask entry log.
                "dump" => {
                    command.consume_args().reject_rest()?;
                    self.dump(&mut output)?;
                }

                // reopen [compact_fraction=FLOAT]
                // Closes and reopens the BitCask database. If compact_ratio is
                // given, it specifies a garbage ratio beyond which the log
                // should be auto-compacted on open.
                "reopen" => {
                    let mut args = command.consume_args();
                    let compact_fraction = args.lookup_parse("compact_fraction")?;
                    args.reject_rest()?;
                    // We need to close the file before we can reopen it, which
                    // happens when the database is dropped. Replace the engine
                    // with a temporary empty engine then reopen the file.
                    let path = self.inner.engine.log.path.clone();
                    self.inner.engine = BitCask::new(self.tempdir.path().join("empty"))?;
                    if let Some(garbage_fraction) = compact_fraction {
                        self.inner.engine = BitCask::new_maybe_compact(path, garbage_fraction, 0)?;
                    } else {
                        self.inner.engine = BitCask::new(path)?;
                    }
                }

                // Pass other commands to the standard engine runner.
                _ => return self.inner.run(command),
            }
            Ok(output)
        }
    }

    impl BitCaskRunner {
        fn new() -> Self {
            let tempdir = TempDir::with_prefix("toydb").expect("tempdir failed");
            let engine = BitCask::new(tempdir.path().join("bitcask")).expect("bitcask failed");
            let inner = Runner::new(engine);
            Self { inner, tempdir }
        }

        /// Dumps the full BitCask entry log.
        fn dump(&mut self, output: &mut String) -> StdResult<(), Box<dyn StdError>> {
            let file = &mut self.inner.engine.log.file;
            let file_len = file.metadata()?.len();
            let mut r = BufReader::new(file);
            let mut pos = r.seek(SeekFrom::Start(0))?;
            let mut len_buf = [0; 4];
            let mut idx = 0;

            while pos < file_len {
                if idx > 0 {
                    writeln!(output, "--------")?;
                }
                write!(output, "{:<7}", format!("{idx}@{pos}"))?;

                r.read_exact(&mut len_buf)?;
                let key_len = u32::from_be_bytes(len_buf);
                write!(output, " keylen={key_len} [{}]", hex::encode(len_buf))?;

                r.read_exact(&mut len_buf)?;
                let value_len_or_tombstone = i32::from_be_bytes(len_buf); // NB: -1 for tombstones
                let value_len = value_len_or_tombstone.max(0) as u32;
                writeln!(output, " valuelen={value_len_or_tombstone} [{}]", hex::encode(len_buf))?;

                let mut key = vec![0; key_len as usize];
                r.read_exact(&mut key)?;
                let mut value = vec![0; value_len as usize];
                r.read_exact(&mut value)?;
                let size = 4 + 4 + key_len as u64 + value_len as u64;
                writeln!(
                    output,
                    "{:<7} key={} [{}] {}",
                    format!("{size}b"),
                    format::Raw::key(&key),
                    hex::encode(key),
                    match value_len_or_tombstone {
                        -1 => "tombstone".to_string(),
                        _ => format!(
                            "value={} [{}]",
                            format::Raw::bytes(&value),
                            hex::encode(&value)
                        ),
                    },
                )?;

                pos += size;
                idx += 1;
            }
            Ok(())
        }
    }
}