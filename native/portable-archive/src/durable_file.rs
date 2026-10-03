//! Exact streaming storage transport. No semantic authority, history pruning,
//! wire-frame parsing or private-generation reset is reachable here.
use fs2::FileExt;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Seek, SeekFrom, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::path::Path;
const BLOCK: usize = 65536;

pub fn private_file(path: &Path) -> io::Result<File> {
    let file = OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path)?;
    let m = file.metadata()?;
    if !m.is_file() || m.nlink() != 1 || m.uid() != unsafe { libc::geteuid() } || m.mode() & 0o077 != 0 {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "expected an owned private single-link regular file"));
    }
    Ok(file)
}

pub fn equal_files(a: &mut File, b: &mut File) -> io::Result<bool> {
    a.seek(SeekFrom::Start(0))?;
    b.seek(SeekFrom::Start(0))?;
    let length=a.metadata()?.len();
    if length != b.metadata()?.len() { return Ok(false); }
    let mut remaining=length;
    let mut x = [0u8; BLOCK];
    let mut y = [0u8; BLOCK];
    loop {
        // read_exact over an independently chosen common length prevents short
        // read boundaries from becoming false inequality.
        if remaining == 0 { return Ok(a.metadata()?.len()==length && b.metadata()?.len()==length); }
        let n = usize::try_from(remaining.min(BLOCK as u64)).unwrap();
        a.read_exact(&mut x[..n])?;
        b.read_exact(&mut y[..n])?;
        if x[..n] != y[..n] { return Ok(false); }
        remaining-=n as u64;
    }
}

/// Stable lock plus fsync/rename/dir-fsync; only the bytes offered through
/// independently retained private files are installed. Storage size is unrelated
/// to any network frame bound. Resources/disk capacity remain caller obligations.
pub fn compare_replace(path: &Path, expected: &Path, next: &Path) -> io::Result<bool> {
    compare_replace_inner(path, expected, next, false)
}

fn compare_replace_inner(path: &Path, expected: &Path, next: &Path, lose_reply: bool) -> io::Result<bool> {
    let directory = path.parent().ok_or_else(|| io::Error::other("journal has no parent"))?;
    let lock = OpenOptions::new().read(true).write(true).create(true).truncate(false)
        .mode(0o600).custom_flags(libc::O_NOFOLLOW).open(path.with_extension("lock"))?;
    let meta = lock.metadata()?;
    if !meta.is_file() || meta.nlink() != 1 || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
        return Err(io::Error::other("journal lock custody invalid"));
    }
    lock.lock_exclusive()?;
    let mut old = private_file(path)?;
    let mut wanted = private_file(expected)?;
    if !equal_files(&mut old, &mut wanted)? { return Ok(false); }
    let mut source = private_file(next)?;
    let mut nonce = [0u8; 16];
    getrandom::getrandom(&mut nonce).map_err(|e|io::Error::other(e.to_string()))?;
    let staging = directory.join(format!(".portable-{}", hex::encode(nonce)));
    let mut output = OpenOptions::new().read(true).write(true).create_new(true).mode(0o600).open(&staging)?;
    let source_length=source.metadata()?.len();
    io::copy(&mut (&mut source).take(source_length), &mut output)?;
    output.sync_all()?;
    if !equal_files(&mut source, &mut output)? { return Err(io::Error::other("offered storage changed during capture")); }
    fs::rename(&staging, path)?;
    File::open(directory)?.sync_all()?;
    // Test injection happens after the true durability boundary. There is no
    // temporary disarming of any live check or fake semantic acknowledgement.
    if lose_reply { return Err(io::Error::other("lost reply after durable publication")); }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn write(path: &Path, bytes: &[u8]) {
        let mut f = OpenOptions::new().write(true).create_new(true).mode(0o600).open(path).unwrap();
        f.write_all(bytes).unwrap(); f.sync_all().unwrap();
    }
    #[test]
    fn storage_crosses_wire_bound_and_compares_last_byte() {
        let dir = tempfile::tempdir().unwrap();
        let old = vec![7; 17 * 1024 * 1024 + 3];
        let mut next = old.clone(); *next.last_mut().unwrap() = 9;
        let p = dir.path().join("journal"); let e = dir.path().join("expected"); let n = dir.path().join("next");
        write(&p, &old); write(&e, &old); write(&n, &next);
        assert!(compare_replace(&p, &e, &n).unwrap());
        assert_eq!(fs::read(&p).unwrap(), next);
        assert!(!compare_replace(&p, &e, &n).unwrap());
    }
    #[test]
    fn lost_reply_reopens_exact_successor_and_never_reapplies() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("journal"); let e = dir.path().join("expected"); let n = dir.path().join("next");
        write(&p, b"accepted prefix"); write(&e, b"accepted prefix"); write(&n, b"accepted prefix;exact successor");
        assert!(compare_replace_inner(&p, &e, &n, true).is_err());
        assert_eq!(fs::read(&p).unwrap(), b"accepted prefix;exact successor");
        assert!(!compare_replace(&p, &e, &n).unwrap());
    }
    #[test]
    fn refuses_symlink_and_stale_prefix_without_overwrite() {
        let dir = tempfile::tempdir().unwrap();
        let p = dir.path().join("journal"); let e = dir.path().join("expected"); let n = dir.path().join("next");
        write(&p,b"truth"); write(&e,b"stale"); write(&n,b"new");
        assert!(!compare_replace(&p,&e,&n).unwrap()); assert_eq!(fs::read(&p).unwrap(),b"truth");
        let link = dir.path().join("link"); std::os::unix::fs::symlink(&n,&link).unwrap();
        assert!(compare_replace(&p,&p,&link).is_err());
    }
}
