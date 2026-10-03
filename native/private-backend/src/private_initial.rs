//! Shared original endpoint-private initialization durability. Honest crash
//! filesystem premise; checksum is not storage authentication or reachability.
use crate::{
    codec::{bad, bytes, MAX},
    consensus_wire::Cursor,
    custody,
};
use std::{
    fs::{self, File, OpenOptions},
    io::{Read, Result, Write},
    os::unix::fs::OpenOptionsExt,
    path::{Path, PathBuf},
};
pub(crate) struct Initial {
    pub bytes: Vec<u8>,
    _lock: File,
}
fn file(path: &Path) -> PathBuf {
    path.with_extension("initial")
}
impl Initial {
    pub fn create(path: &Path, domain: &[u8], initial: &[u8]) -> Result<Self> {
        let lock = custody::lock(&path.with_extension("initial.lock"))?;
        if path.exists() {
            return Err(bad("event WAL already exists; recover original"));
        }
        let mut framed = domain.to_vec();
        bytes(initial, &mut framed);
        framed.extend(custody::hash(&framed));
        if framed.len() > MAX {
            return Err(bad("private initialization capacity"));
        }
        let p = file(path);
        let mut f = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&p)?;
        f.write_all(&framed)?;
        f.sync_all()?;
        File::open(p.parent().ok_or_else(|| bad("initial parent"))?)?.sync_all()?;
        if fs::read(&p)? != framed {
            return Err(bad("initial durable readback"));
        }
        Ok(Self {
            bytes: initial.to_vec(),
            _lock: lock,
        })
    }
    pub fn load(path: &Path, domain: &[u8]) -> Result<Self> {
        let lock = custody::lock(&path.with_extension("initial.lock"))?;
        let mut f = File::open(file(path))?;
        if f.metadata()?.len() > MAX as u64 {
            return Err(bad("private initial file bound"));
        }
        let mut framed = vec![];
        f.read_to_end(&mut framed)?;
        if framed.len() < 32 {
            return Err(bad("initial incomplete; source repair required"));
        }
        let end = framed.len() - 32;
        if custody::hash(&framed[..end]) != framed[end..] {
            return Err(bad("initial checksum"));
        }
        let mut c = Cursor::new(&framed[..end])?;
        if c.take(domain.len())? != domain {
            return Err(bad("initial runtime domain"));
        }
        let bytes = c.bytes()?;
        c.finish()?;
        Ok(Self { bytes, _lock: lock })
    }
}
