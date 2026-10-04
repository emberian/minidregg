//! Filesystem custody: owner-private directories, fsync-then-rename JSON records under an
//! exclusive lease, and the retained attempt-directory layout `resource-client` already writes
//! (`call.bin`, `outcome.json`, `retry-NNNN.{bin,json,transport.json}`).
use std::fs::{self, OpenOptions};
use std::io::Read;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::custody::{classify, Outcome};
use crate::durable::{self, Perm};
use crate::lock::{Create, Lease, LockError, Wait};
use crate::{Error, Result};

const MAX_RECORD: u64 = 16 * 1024 * 1024;

/// Create (or accept) an owner-only directory owned by this effective uid; refuse anything
/// else, including a symlink.
pub fn private_dir(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {}
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(e) => return Err(Error(format!("{}: {e}", path.display()))),
    }
    let m = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    // SAFETY: geteuid has no preconditions and cannot fail.
    let euid = unsafe { libc::geteuid() };
    if !m.is_dir() || m.mode() & 0o077 != 0 || m.uid() != euid {
        return Err(Error(format!("{} must be an owner-private directory", path.display())));
    }
    Ok(())
}

/// Write `value` to `path` durably: a unique 0600 sibling, fsync, rename, fsync the directory.
pub fn atomic_json(path: &Path, value: &Value) -> Result<()> {
    let bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    durable::replace(path, &bytes, Perm::Private).map_err(|e| e.to_string().into())
}

/// Read a bounded JSON record; absence is `None`, corruption is an error (never absence).
pub fn read_json(path: &Path) -> Result<Option<Value>> {
    let f = match OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path) {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e.to_string().into()),
    };
    let meta = f.metadata().map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.len() > MAX_RECORD {
        return Err("invalid or oversized custody record".into());
    }
    let mut bytes = Vec::new();
    f.take(MAX_RECORD + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    serde_json::from_slice(&bytes).map(Some).map_err(|e| Error(format!("corrupt custody record: {e}")))
}

/// One JSON record under an exclusive, non-blocking lease (`<key>.lock`, flock). While a
/// `Record` lives, no other process holds the same key.
pub struct Record {
    pub path: PathBuf,
    pub value: Option<Value>,
    _lease: Lease,
}

impl Record {
    /// `Ok(None)`: another worker holds this record; no duplicate work may start.
    pub fn lock(root: &Path, key: &str) -> Result<Option<Self>> {
        if key.is_empty() || !key.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
            return Err("invalid custody key".into());
        }
        private_dir(root)?;
        let lease = match Lease::acquire(&root.join(format!("{key}.lock")), Create::Yes, Wait::No) {
            Ok(lease) => lease,
            Err(LockError::Busy) => return Ok(None),
            Err(e) => return Err(e.to_string().into()),
        };
        let path = root.join(format!("{key}.json"));
        Ok(Some(Record { value: read_json(&path)?, path, _lease: lease }))
    }

    pub fn save(&mut self, value: Value) -> Result<()> {
        atomic_json(&self.path, &value)?;
        self.value = Some(value);
        Ok(())
    }
}

/// A retained attempt directory.
pub struct AttemptDir(pub PathBuf);

fn retry_index(name: &str) -> Option<(u64, bool)> {
    let (stem, outcome) = if let Some(s) = name.strip_suffix(".transport.json") {
        (s, false)
    } else if let Some(s) = name.strip_suffix(".json") {
        (s, true)
    } else {
        (name.strip_suffix(".bin")?, false)
    };
    let digits = stem.strip_prefix("retry-")?;
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    Some((digits.parse().ok()?, outcome))
}

impl AttemptDir {
    /// Retain the exact call: complete-or-absent (staged, fsynced, linked into place), then fsync
    /// every ancestor directory. A transmission must never precede a durable call and its
    /// pathname, and a crash can never leave a truncated `call.bin` to be resent.
    pub fn seal_call(&self, call: &[u8]) -> Result<PathBuf> {
        let path = self.0.join("call.bin");
        durable::create_new(&path, call, Perm::Private).map_err(|e| format!("cannot retain exact call {}: {e}", path.display()))?;
        durable::sync_ancestors(&self.0).map_err(|e| e.to_string())?;
        Ok(path)
    }

    pub fn call(&self) -> Result<Option<Vec<u8>>> {
        match fs::read(self.0.join("call.bin")) {
            Ok(b) => Ok(Some(b)),
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e.to_string().into()),
        }
    }

    /// The next `retry-NNNN` evidence paths: after the greatest reserved index, never reusing
    /// a gap, transport metadata reserving its index without being an outcome.
    pub fn next_retry(&self) -> Result<(PathBuf, PathBuf)> {
        let mut greatest = 0u64;
        for entry in fs::read_dir(&self.0).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if let Some((i, _)) = entry.file_name().to_str().and_then(retry_index) {
                greatest = greatest.max(i);
            }
        }
        let i = greatest.checked_add(1).ok_or("retry evidence sequence exceeds u64")?;
        Ok((self.0.join(format!("retry-{i:04}.bin")), self.0.join(format!("retry-{i:04}.json"))))
    }

    /// Retained decoded outcomes, oldest first: `outcome.json`, then `retry-N.json` in numeric
    /// (not lexical) order.
    pub fn history(&self) -> Result<Vec<Value>> {
        let mut rows = Vec::new();
        for entry in fs::read_dir(&self.0).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if let Some((i, true)) = entry.file_name().to_str().and_then(retry_index) {
                rows.push((i, entry.path()));
            }
        }
        rows.sort();
        let mut out = Vec::new();
        if let Some(v) = read_json(&self.0.join("outcome.json"))? {
            out.push(v);
        }
        for (_, p) in rows {
            out.push(read_json(&p)?.ok_or("retained outcome vanished")?);
        }
        Ok(out)
    }

    /// The classified outcome of this attempt's retained history.
    pub fn outcome(&self) -> Result<Option<Outcome>> {
        Ok(classify(&self.history()?))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn scratch(tag: &str) -> PathBuf {
        let p = std::env::temp_dir().join(format!("mini-sdk-store-{tag}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&p);
        p
    }

    #[test]
    fn leases_survive_reopen_and_corruption_is_not_absence() {
        let root = scratch("lease");
        let mut a = Record::lock(&root, "one").unwrap().unwrap();
        a.save(json!({"phase":"started"})).unwrap();
        assert!(Record::lock(&root, "one").unwrap().is_none());
        drop(a);
        let a = Record::lock(&root, "one").unwrap().unwrap();
        assert_eq!(a.value.unwrap()["phase"], "started");
        fs::write(root.join("two.json"), b"{").unwrap();
        assert!(Record::lock(&root, "two").is_err());
        assert!(Record::lock(&root, "../x").is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn attempt_history_is_numeric_and_transport_metadata_is_not_an_outcome() {
        let root = scratch("attempt");
        private_dir(&root).unwrap();
        let dir = AttemptDir(root.clone());
        dir.seal_call(b"call").unwrap();
        assert!(dir.seal_call(b"other").is_err(), "a sealed call is never replaced");
        fs::write(root.join("outcome.json"), json!({"type":"pending"}).to_string()).unwrap();
        fs::write(root.join("retry-0002.json"), json!({"type":"refused"}).to_string()).unwrap();
        fs::write(root.join("retry-10.json"), json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"}).to_string()).unwrap();
        fs::write(root.join("retry-0011.transport.json"), b"{}").unwrap();
        assert_eq!(dir.history().unwrap().len(), 3);
        assert!(matches!(dir.outcome().unwrap(), Some(Outcome::Confirmed(_))));
        assert_eq!(dir.next_retry().unwrap().1, root.join("retry-0012.json"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_group_readable_directory_refuses() {
        use std::os::unix::fs::PermissionsExt;
        let root = scratch("perm");
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o750)).unwrap();
        assert!(private_dir(&root).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
