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
/// Create `p` holding exactly `framed`, or leave `p` absent: written to a
/// sibling temp (0600), then linked into place without replacing, so a
/// crash never leaves a torn file under the final name (a torn `.initial` bricks
/// the original private material). An existing `p` is refused unchanged.
pub(crate) fn write_new_durable(p: &Path, framed: &[u8]) -> Result<()> {
    let mut tmp = p.as_os_str().to_owned();
    tmp.push(".tmp");
    let tmp = PathBuf::from(tmp);
    let parent = p.parent().ok_or_else(|| bad("initial parent"))?;
    // A stale temp is an unpublished tear from an earlier crash.
    match fs::remove_file(&tmp) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => return Err(e),
    }
    let mut f = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(&tmp)?;
    f.write_all(framed)?;
    let linked = fs::hard_link(&tmp, p);
    let _ = fs::remove_file(&tmp);
    linked?;
    if fs::read(p)? != framed {
        return Err(bad("initial durable readback"));
    }
    Ok(())
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
        write_new_durable(&file(path), &framed)?;
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

#[cfg(test)]
mod tests {
    use super::*;
    fn dir(name: &str) -> PathBuf {
        let d = std::env::temp_dir().join(format!("mini-initial-{name}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&d);
        fs::create_dir_all(&d).unwrap();
        d
    }
    #[test]
    fn initial_is_published_whole_via_temp_and_a_stale_tear_is_discarded() {
        let d = dir("atomic");
        let p = d.join("w.initial");
        let mut tmp = p.as_os_str().to_owned();
        tmp.push(".tmp");
        let tmp = PathBuf::from(tmp);
        fs::write(&tmp, b"torn half record").unwrap();
        write_new_durable(&p, b"whole framed initial").unwrap();
        assert_eq!(fs::read(&p).unwrap(), b"whole framed initial");
        assert!(!tmp.exists(), "temp must not outlive publication");
        let again = write_new_durable(&p, b"another").unwrap_err();
        assert_eq!(again.kind(), std::io::ErrorKind::AlreadyExists);
        assert_eq!(fs::read(&p).unwrap(), b"whole framed initial");
        assert!(!tmp.exists());
    }
}
