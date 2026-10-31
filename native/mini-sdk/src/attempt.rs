//! One attempt's named files: the bytes each step of [`crate::flow`] produced and the next one
//! consumes, under one attempt directory.
//!
//! A write attempt is custody: every file is created durably as it is produced
//! ([`Attempt::disk`]), so a crash leaves the record up to the last completed step. A read commits
//! nothing and its answer is in hand when it returns, so its files are working bytes
//! ([`Attempt::memory`]): they stay in this process and reach the directory only when something
//! needs a path (a one-shot Host process, a refusal's retained record), by [`Attempt::path`] or
//! [`Attempt::materialize`]. Either way a name is created once and never replaced, and a file
//! another process wrote into the directory reads as the attempt's own.
use std::borrow::Cow;
use std::collections::BTreeMap;
use std::io;
use std::path::{Path, PathBuf};

use crate::durable::{self, Perm};
use crate::{Error, Result};

/// The largest file an attempt reads back from its directory.
pub const READ_LIMIT: usize = 64 << 20;

pub struct Attempt {
    dir: PathBuf,
    /// `None`: every file is on disk. `Some`: the bytes made here, and whether each is on disk yet.
    memory: Option<BTreeMap<String, (Vec<u8>, bool)>>,
    /// Whether the directory may hold files this process did not make: it existed when the
    /// attempt began, or a path was handed out. Until then a memory attempt asks the disk nothing.
    shared: bool,
}

impl Attempt {
    /// Files created durably in `dir`, which exists.
    pub fn disk(dir: &Path) -> Attempt {
        Attempt { dir: dir.to_owned(), memory: None, shared: true }
    }

    /// Files kept in this process; `dir` (which need not exist) is where they are written when
    /// one is asked for by path.
    pub fn memory(dir: &Path) -> Attempt {
        Attempt { dir: dir.to_owned(), memory: Some(BTreeMap::new()), shared: dir.exists() }
    }

    pub fn dir(&self) -> &Path {
        &self.dir
    }

    pub fn in_memory(&self) -> bool {
        self.memory.is_some()
    }

    /// Create `name` with `bytes`; an existing name is refused.
    pub fn create(&mut self, name: &str, bytes: &[u8]) -> Result<()> {
        let path = self.dir.join(name);
        match &mut self.memory {
            None => durable::create_new(&path, bytes, Perm::Umask)
                .map_err(|e| Error(format!("cannot create {}: {e}", path.display()))),
            Some(files) => {
                if files.contains_key(name) || (self.shared && path.exists()) {
                    return Err(Error(format!("refusing to replace {}", path.display())));
                }
                files.insert(name.to_owned(), (bytes.to_vec(), false));
                Ok(())
            }
        }
    }

    /// Whether `name` exists.
    pub fn exists(&self, name: &str) -> bool {
        self.memory.as_ref().is_some_and(|files| files.contains_key(name)) || (self.shared && self.dir.join(name).exists())
    }

    /// The bytes of `name`: made here, or read from the directory.
    pub fn read(&self, name: &str) -> Result<Cow<'_, [u8]>> {
        if let Some((bytes, _)) = self.memory.as_ref().and_then(|files| files.get(name)) {
            return Ok(Cow::Borrowed(bytes));
        }
        if !self.shared {
            return Err(Error(format!("{} was not made", self.dir.join(name).display())));
        }
        crate::fsread::read_regular(&self.dir.join(name), 0, READ_LIMIT).map(Cow::Owned).map_err(|e| Error(e.to_string()))
    }

    /// `name` as a file in the directory, written there first when it was made in memory.
    pub fn path(&mut self, name: &str) -> Result<PathBuf> {
        let path = self.dir.join(name);
        self.shared = true;
        if let Some(files) = &mut self.memory {
            if let Some((bytes, written)) = files.get_mut(name) {
                if !*written {
                    write_private_dir(&self.dir)?;
                    durable::create_new(&path, bytes, Perm::Umask)
                        .map_err(|e| Error(format!("cannot create {}: {e}", path.display())))?;
                    *written = true;
                }
            }
        }
        Ok(path)
    }

    /// Where another process writes the new file `name`; the directory exists when this returns.
    pub fn output(&mut self, name: &str) -> Result<PathBuf> {
        self.shared = true;
        if self.memory.is_some() {
            write_private_dir(&self.dir)?;
        }
        Ok(self.dir.join(name))
    }

    /// Every file of the attempt in its directory; returns the directory.
    pub fn materialize(&mut self) -> Result<&Path> {
        self.shared = true;
        let names: Vec<String> = self.memory.as_ref().map(|files| files.keys().cloned().collect()).unwrap_or_default();
        if self.memory.is_some() {
            write_private_dir(&self.dir)?;
        }
        for name in names {
            self.path(&name)?;
        }
        Ok(&self.dir)
    }
}

fn write_private_dir(dir: &Path) -> Result<()> {
    use std::os::unix::fs::DirBuilderExt;
    match std::fs::DirBuilder::new().mode(0o700).create(dir) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists && dir.is_dir() => Ok(()),
        Err(e) => Err(Error(format!("cannot create {}: {e}", dir.display()))),
    }
}

#[cfg(test)]
mod tests {
    use super::Attempt;

    #[test]
    fn a_memory_attempt_writes_only_what_is_asked_for_by_path() {
        let dir = std::env::temp_dir().join(format!("attempt-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        let mut attempt = Attempt::memory(&dir);
        attempt.create("a.bin", b"one").unwrap();
        attempt.create("b.bin", b"two").unwrap();
        assert!(attempt.create("a.bin", b"again").is_err(), "a name is created once");
        assert_eq!(&*attempt.read("a.bin").unwrap(), b"one");
        assert!(!dir.exists(), "nothing reaches the directory unasked");
        let path = attempt.path("a.bin").unwrap();
        assert_eq!(std::fs::read(&path).unwrap(), b"one");
        assert!(!dir.join("b.bin").exists());
        // Another process's file in the directory reads as the attempt's own.
        std::fs::write(attempt.output("c.bin").unwrap(), b"three").unwrap();
        assert_eq!(&*attempt.read("c.bin").unwrap(), b"three");
        assert!(attempt.create("c.bin", b"x").is_err());
        attempt.materialize().unwrap();
        assert_eq!(std::fs::read(dir.join("b.bin")).unwrap(), b"two");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_disk_attempt_creates_each_file_as_it_is_made() {
        let dir = std::env::temp_dir().join(format!("attempt-disk-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir(&dir).unwrap();
        let mut attempt = Attempt::disk(&dir);
        attempt.create("a.bin", b"one").unwrap();
        assert_eq!(std::fs::read(dir.join("a.bin")).unwrap(), b"one");
        assert!(attempt.create("a.bin", b"again").is_err());
        let _ = std::fs::remove_dir_all(&dir);
    }
}
