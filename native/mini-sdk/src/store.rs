//! Filesystem custody: owner-private directories, fsync-then-rename JSON records under an
//! exclusive lease, and the retained attempt-directory layout `resource-client` already writes
//! (`call.bin`, `outcome.json`, `retry-NNNN.{bin,json,transport.json}`).
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::Value;

use crate::custody::{classify, standing, Outcome, Standing};
use crate::durable::{self, Perm};
use crate::lock::{Create, Lease, LockError, Wait};
use crate::{Error, Result};

const MAX_RECORD: u64 = 16 * 1024 * 1024;

/// Write `value` to `path` durably: a unique 0600 sibling, fsync, rename, fsync the directory.
pub fn atomic_json(path: &Path, value: &Value) -> Result<()> {
    let bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    durable::replace(path, &bytes, Perm::Private).map_err(|e| e.to_string().into())
}

/// Write a record that may exist only ONCE with these exact contents: absent, it is written
/// durably (as [`atomic_json`]); present and equal, it is re-synced and accepted (an interrupted
/// writer's retry); present and different, it refuses. A phase marker is retained this way, so a
/// retry can never silently replace what a crashed run decided.
pub fn write_once(path: &Path, value: &Value) -> Result<()> {
    let bytes = serde_json::to_vec(value).map_err(|e| e.to_string())?;
    match durable::retain_exact(path, &bytes, Perm::Private) {
        Ok(_) => Ok(()),
        Err(durable::RetainError::Differs) => {
            Err(Error(format!("retained record {} differs; no replacement", path.display())))
        }
        Err(durable::RetainError::Io(e)) => Err(e.to_string().into()),
    }
}

/// Read a bounded JSON record; absence is `None`, corruption is an error (never absence).
pub fn read_json(path: &Path) -> Result<Option<Value>> {
    let bytes = match crate::fsread::read_regular(path, 0, MAX_RECORD as usize) {
        Ok(bytes) => bytes,
        Err(e) if e.is_not_found() => return Ok(None),
        Err(e) => return Err(Error(format!("invalid or oversized custody record: {e}"))),
    };
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
        crate::private::ensure_dir(root)?;
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

    /// The retained `retry-N.json` outcome files in numeric attempt order (not lexical: a fifth
    /// digit does not reorder time, and legacy zero-padded widths are preserved). Transport
    /// metadata and half-written `.bin` files are never outcomes.
    pub fn outcome_files(&self) -> Result<Vec<PathBuf>> {
        let mut rows = Vec::new();
        for entry in fs::read_dir(&self.0).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            if let Some((i, true)) = entry.file_name().to_str().and_then(retry_index) {
                rows.push((i, entry.path()));
            }
        }
        rows.sort();
        Ok(rows.into_iter().map(|(_, p)| p).collect())
    }

    /// Retained decoded outcomes, oldest first: `outcome.json`, then `retry-N.json` in numeric
    /// (not lexical) order.
    pub fn history(&self) -> Result<Vec<Value>> {
        let mut out = Vec::new();
        if let Some(v) = read_json(&self.0.join("outcome.json"))? {
            out.push(v);
        }
        for p in self.outcome_files()? {
            out.push(read_json(&p)?.ok_or("retained outcome vanished")?);
        }
        Ok(out)
    }

    /// The classified outcome of this attempt's retained history (typed receipts).
    pub fn outcome(&self) -> Result<Option<Outcome>> {
        Ok(classify(&self.history()?))
    }

    /// What the retained history says about the exact call, by the Host's words alone
    /// ([`standing`]): the reading every client uses to decide whether a call is admitted.
    pub fn standing(&self) -> Result<Standing> {
        Ok(standing(&self.history()?))
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
        crate::private::ensure_dir(&root).unwrap();
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
    fn metadata_and_partial_writes_reserve_their_attempt_without_becoming_outcomes() {
        let root = scratch("reserve");
        fs::create_dir_all(&root).unwrap();
        for name in ["retry-0001.bin", "retry-0002.json", "retry-10000.transport.json"] {
            fs::write(root.join(name), name.as_bytes()).unwrap();
        }
        let dir = AttemptDir(root.clone());
        assert_eq!(dir.next_retry().unwrap(), (root.join("retry-10001.bin"), root.join("retry-10001.json")));
        assert_eq!(dir.outcome_files().unwrap(), vec![root.join("retry-0002.json")]);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn later_outcomes_remain_later_beyond_four_digits_and_legacy_padding_is_preserved() {
        let root = scratch("legacy");
        fs::create_dir_all(&root).unwrap();
        for name in ["retry-10000.json", "retry-9999.json", "retry-003.json", "retry-10000.transport.json",
            "retry-garbage.json", "retry--1.json"] {
            fs::write(root.join(name), b"{}").unwrap();
        }
        let dir = AttemptDir(root.clone());
        assert_eq!(dir.outcome_files().unwrap(),
            ["retry-003.json", "retry-9999.json", "retry-10000.json"].map(|n| root.join(n)).to_vec());
        assert_eq!(dir.next_retry().unwrap().0, root.join("retry-10001.bin"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn sparse_history_does_not_reuse_old_attempt_numbers_and_exhaustion_refuses_without_wrapping() {
        let root = scratch("sparse");
        fs::create_dir_all(&root).unwrap();
        fs::write(root.join("retry-0042.bin"), b"x").unwrap();
        assert_eq!(AttemptDir(root.clone()).next_retry().unwrap().1, root.join("retry-0043.json"));
        fs::write(root.join("retry-18446744073709551615.bin"), b"x").unwrap();
        assert!(AttemptDir(root.clone()).next_retry().unwrap_err().0.contains("exceeds u64"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_phase_record_may_exist_only_once_with_these_contents() {
        let root = scratch("once");
        crate::private::ensure_dir(&root).unwrap();
        let path = root.join("phase.json");
        write_once(&path, &json!({"attempt":"a"})).unwrap();
        write_once(&path, &json!({"attempt":"a"})).unwrap(); // an interrupted writer's retry
        assert!(write_once(&path, &json!({"attempt":"b"})).unwrap_err().0.contains("no replacement"));
        assert_eq!(read_json(&path).unwrap().unwrap(), json!({"attempt":"a"}));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_group_readable_directory_refuses() {
        use std::os::unix::fs::PermissionsExt;
        let root = scratch("perm");
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o750)).unwrap();
        assert!(crate::private::ensure_dir(&root).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
