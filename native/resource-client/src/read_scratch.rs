//! Where a signed read and a codec inspection keep their working files.
//!
//! A read commits nothing and its answer is in hand when it returns, so its files (the intent,
//! the challenge, the signatures, the signed observation, the view, their renderings) are working
//! files of the command that made them, not retained evidence: receipt continuity takes the
//! challenge in memory and keeps its own anchors. They used to land in `WORKSPACE/attempts/a-N`
//! and `WORKSPACE/sources/q-N.json` and stay there, fifteen files a read, without bound.
//!
//! Here each process has one private directory per workspace, on a memory file system when the
//! account has one (`XDG_RUNTIME_DIR`, else `/dev/shm/mini-reads-UID`), else
//! `WORKSPACE/.reads`. It holds at most the newest 64 reads of the process (a resident serves
//! many commands) and is removed when a one-shot command ends; a directory left by a process that
//! no longer runs is removed by the next process that starts one. A refused read is moved into
//! `WORKSPACE/attempts` whole, where the refusal readers look for it.
use crate::Result;
use std::collections::HashMap;
use std::fs;
use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::path::{Path, PathBuf};
use std::sync::Mutex;

const KEEP: usize = 64;

static DIRS: Mutex<Option<HashMap<PathBuf, PathBuf>>> = Mutex::new(None);

fn private_dir(path: &Path) -> bool {
    let uid = unsafe { libc::geteuid() };
    if let Err(e) = fs::DirBuilder::new().mode(0o700).create(path) {
        if e.kind() != std::io::ErrorKind::AlreadyExists {
            return false;
        }
    }
    fs::symlink_metadata(path).is_ok_and(|m| m.is_dir() && m.uid() == uid && m.mode() & 0o077 == 0)
}

fn base(root: &Path) -> PathBuf {
    let uid = unsafe { libc::geteuid() };
    let memory = std::env::var_os("XDG_RUNTIME_DIR").map(PathBuf::from)
        .filter(|dir| dir.is_absolute() && fs::symlink_metadata(dir).is_ok_and(|m| m.is_dir() && m.uid() == uid && m.mode() & 0o077 == 0))
        .map(|dir| dir.join("mini-reads"))
        .or_else(|| Path::new("/dev/shm").is_dir().then(|| PathBuf::from(format!("/dev/shm/mini-reads-{uid}"))));
    match memory {
        Some(dir) if private_dir(&dir) => dir,
        _ => root.join(".reads"),
    }
}

fn alive(pid: i32) -> bool {
    let signalled = unsafe { libc::kill(pid, 0) };
    signalled == 0 || std::io::Error::last_os_error().raw_os_error() != Some(libc::ESRCH)
}

/// This process's directory for `root`'s reads, made (and its dead siblings removed) on first use.
fn dir(root: &Path) -> Result<PathBuf> {
    let mut dirs = DIRS.lock().map_err(|_| "read scratch lock poisoned")?;
    let dirs = dirs.get_or_insert_with(HashMap::new);
    if let Some(dir) = dirs.get(root) {
        if dir.is_dir() {
            return Ok(dir.clone());
        }
    }
    use sha2::Digest;
    let key = format!("{:x}", sha2::Sha256::digest(root.as_os_str().as_encoded_bytes()));
    let parent = base(root).join(&key[..16]);
    if !private_dir(parent.parent().ok_or("read scratch has no parent")?) || !private_dir(&parent) {
        return Err(format!("read scratch {} is not a private directory", parent.display()));
    }
    let pid = std::process::id();
    if let Ok(entries) = fs::read_dir(&parent) {
        for entry in entries.flatten() {
            if let Some(other) = entry.file_name().to_str().and_then(|n| n.parse::<i32>().ok()) {
                if other as u32 != pid && !alive(other) {
                    let _ = fs::remove_dir_all(entry.path());
                }
            }
        }
    }
    let dir = parent.join(pid.to_string());
    if !private_dir(&dir) {
        return Err(format!("read scratch {} is not a private directory", dir.display()));
    }
    dirs.insert(root.to_path_buf(), dir.clone());
    Ok(dir)
}

/// The reads this process made, oldest first, per directory: pruning never lists the directory.
static MADE: Mutex<Vec<(PathBuf, String)>> = Mutex::new(Vec::new());

/// Remove this process's oldest reads in `dir` beyond `KEEP - 1`, so one more fits.
fn prune(dir: &Path) {
    let Ok(mut made) = MADE.lock() else { return };
    let mine = made.iter().filter(|(d, _)| d == dir).count();
    if mine < KEEP {
        return;
    }
    let mut excess = mine + 1 - KEEP;
    made.retain(|(d, nonce)| {
        if excess == 0 || d != dir {
            return true;
        }
        excess -= 1;
        let _ = fs::remove_dir_all(dir.join(format!("a-{nonce}")));
        let _ = fs::remove_file(dir.join(format!("q-{nonce}.json")));
        for n in 0..16 {
            if fs::remove_file(dir.join(format!("qb-{nonce}-{n}.json"))).is_err() {
                break;
            }
        }
        false
    });
}

/// A fresh working directory name for one read or inspection of `root`, and its nonce.
pub(crate) fn attempt(root: &Path) -> Result<(PathBuf, String)> {
    let dir = dir(root)?;
    prune(&dir);
    for _ in 0..8 {
        let nonce = crate::fsio::random_nonce()?;
        let attempt = dir.join(format!("a-{nonce}"));
        if !attempt.exists() {
            if let Ok(mut made) = MADE.lock() {
                made.push((dir.clone(), nonce.clone()));
            }
            return Ok((attempt, nonce));
        }
    }
    Err("could not allocate a distinct read name".into())
}

/// The intent source file `name` beside `attempt` (it is removed with it).
pub(crate) fn source(attempt: &Path, name: &str) -> PathBuf {
    attempt.with_file_name(name)
}

/// A refused read is kept: its directory moves into `root/attempts` whole.
pub(crate) fn keep(root: &Path, attempt: &Path) {
    if attempt.is_dir() {
        let _ = retain(root, attempt);
    }
}

/// A read whose directory becomes a write's custody record (a protected document's enrollment
/// phase is retained beside its observation, and recovery finds it there) moves into
/// `root/attempts` whole; returns where it now is.
pub(crate) fn retain(root: &Path, attempt: &Path) -> Result<PathBuf> {
    let name = attempt.file_name().ok_or("read has no directory name")?;
    let attempts = root.join("attempts");
    if let Err(e) = fs::DirBuilder::new().mode(0o700).create(&attempts) {
        if e.kind() != std::io::ErrorKind::AlreadyExists {
            return Err(format!("{}: {e}", attempts.display()));
        }
    }
    let target = attempts.join(name);
    if fs::rename(attempt, &target).is_err() {
        copy_tree(attempt, &target).map_err(|e| format!("cannot retain {} as {}: {e}", attempt.display(), target.display()))?;
        let _ = fs::remove_dir_all(attempt);
    }
    Ok(target)
}

fn copy_tree(from: &Path, to: &Path) -> std::io::Result<()> {
    fs::DirBuilder::new().mode(0o700).create(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let path = entry.path();
        if entry.file_type()?.is_dir() {
            copy_tree(&path, &to.join(entry.file_name()))?;
        } else {
            fs::copy(&path, to.join(entry.file_name()))?;
        }
    }
    Ok(())
}

/// Remove this process's read directories (a one-shot command's end).
pub(crate) fn clear() {
    if let Ok(mut made) = MADE.lock() {
        made.clear();
    }
    if let Ok(mut dirs) = DIRS.lock() {
        for (_, dir) in dirs.take().unwrap_or_default() {
            let _ = fs::remove_dir_all(dir);
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn reads_are_bounded_and_cleared() {
        let root = std::env::temp_dir().join(format!("read-scratch-{}", std::process::id()));
        std::fs::create_dir_all(root.join("attempts")).unwrap();
        let mut made = Vec::new();
        for _ in 0..super::KEEP + 5 {
            let (attempt, nonce) = super::attempt(&root).unwrap();
            std::fs::create_dir(&attempt).unwrap();
            std::fs::write(super::source(&attempt, &format!("q-{nonce}.json")), b"{}").unwrap();
            made.push(attempt);
        }
        let dir = made[0].parent().unwrap().to_path_buf();
        let reads = std::fs::read_dir(&dir).unwrap().flatten()
            .filter(|e| e.file_name().to_string_lossy().starts_with("a-")).count();
        assert_eq!(reads, super::KEEP);
        let last = made.last().unwrap();
        std::fs::write(last.join("query-refusal.json"), b"{}").unwrap();
        super::keep(&root, last);
        assert!(root.join("attempts").join(last.file_name().unwrap()).join("query-refusal.json").is_file());
        super::clear();
        assert!(!dir.exists());
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn a_retained_read_lives_in_the_workspace() {
        let root = std::env::temp_dir().join(format!("read-retain-{}", std::process::id()));
        std::fs::create_dir_all(&root).unwrap();
        let (attempt, _) = super::attempt(&root).unwrap();
        std::fs::create_dir(&attempt).unwrap();
        std::fs::write(attempt.join("signed-observation.bin"), b"signed").unwrap();
        let kept = super::retain(&root, &attempt).unwrap();
        assert!(kept.starts_with(root.join("attempts")), "{}", kept.display());
        assert_eq!(std::fs::read(kept.join("signed-observation.bin")).unwrap(), b"signed");
        assert!(!attempt.exists(), "the read left the process's scratch, which a one-shot command removes");
        let _ = std::fs::remove_dir_all(&root);
    }
}
