//! The seal record of an attempt directory: ONE durable record per signed write instead of one
//! fsynced file per field.
//!
//! # The invariant (stated here and nowhere else)
//!
//! 1. Before an attempt's exact call can be transmitted, [`seal`] writes `seal.record` in the
//!    attempt directory: the exact bytes of every regular file then directly in the directory
//!    (the intent, the challenge, the observation, the plan, the signatures, `call.bin`, the
//!    retained config and manifest). It is staged, fsynced and committed (complete or absent,
//!    [`crate::durable::create_new`]), and its directory is synced before transmission
//!    ([`crate::flow::sync_retained`]). The record is AUTHORITATIVE for every file it names.
//! 2. Those per-field files are CACHES of the record. While an attempt is being prepared
//!    ([`CacheScope`]) they are written without their own fsync (still staged and linked, so a
//!    live process never sees a partial file). After a crash a named file may therefore be missing
//!    or torn on disk until a reader repairs it.
//! 3. Repair: [`crate::fsread::read_regular`] (and through it every bounded reader of the client)
//!    checks a file named by a `seal.record` beside it against the record's SHA-256 and, when the
//!    file is absent or differs, rewrites it from the record (durably) before returning the
//!    record's bytes. [`repair_dir`] does the same for a whole directory; the client runs it when
//!    it reopens a retained attempt (`mini retry`, workspace recovery), before anything (itself, a
//!    one-shot Host, the transport) reads the attempt's files. A script that reads a cache directly
//!    sees the repaired bytes once a `mini` command has read the file or reopened the attempt;
//!    until then, after a crash, it may see a torn cache.
//! 4. A file written before the seal and NOT named by any record belongs to an attempt whose call
//!    was never sealed, so it was never transmitted; nothing reuses such an attempt's files (a new
//!    submit makes a new directory, append recovery retires pre-call files). The answer files
//!    (`outcome.*`, `retry-*`) are written after transmission and keep their own fsync: a torn
//!    answer would read as corruption, not as "look it up".
//!
//! Format: `MINI-ATTEMPT-SEAL/v1\n`, one JSON index line
//! `{"files":[{"name","length","sha256"}...]}\n`, then the files' bytes concatenated in index order.
use std::cell::RefCell;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

use crate::durable::{self, Perm};
use crate::{Error, Result};

/// The record's file name in an attempt directory.
pub const RECORD: &str = "seal.record";
const MAGIC: &[u8] = b"MINI-ATTEMPT-SEAL/v1\n";
/// Bound on the index line.
const INDEX_MAX: usize = 64 * 1024;
/// Bound on one recorded file (`FnEvidenceCodec.maxHostFrameBytes`).
const FILE_MAX: usize = 12_102_760;

thread_local! {
    static SCOPE: RefCell<Option<PathBuf>> = const { RefCell::new(None) };
}

/// While alive, files created directly in `dir` on this thread are caches (invariant 2): staged
/// and linked without their own fsync. Dropped at the seal.
pub struct CacheScope(());

impl CacheScope {
    pub fn enter(dir: &Path) -> Result<Self> {
        let dir = std::path::absolute(dir).map_err(|e| Error(e.to_string()))?;
        SCOPE.with(|s| *s.borrow_mut() = Some(dir));
        Ok(CacheScope(()))
    }

    /// End this thread's cache scope now (the seal does, so nothing written after it, the
    /// answer files included, is a cache). Idempotent; dropping the guard does the same.
    pub fn end() {
        SCOPE.with(|s| *s.borrow_mut() = None);
    }
}

impl Drop for CacheScope {
    fn drop(&mut self) {
        SCOPE.with(|s| *s.borrow_mut() = None);
    }
}

/// Whether `path` is written as a cache (its parent is this thread's cache scope; the record
/// itself never is).
pub(crate) fn is_cache(path: &Path) -> bool {
    if path.file_name().and_then(|n| n.to_str()) == Some(RECORD) {
        return false;
    }
    SCOPE.with(|s| {
        s.borrow().as_ref().is_some_and(|dir| {
            std::path::absolute(path).ok().and_then(|p| p.parent().map(Path::to_path_buf)).as_deref() == Some(dir.as_path())
        })
    })
}

fn sha256_hex(bytes: &[u8]) -> String {
    crate::hex::encode(&crate::sha256(bytes))
}

/// Write `dir/seal.record` over every regular file directly in `dir` (invariant 1). Refuses if a
/// record is already there.
pub fn seal(dir: &Path) -> Result<()> {
    let mut names: Vec<String> = Vec::new();
    for entry in fs::read_dir(dir).map_err(|e| Error(format!("{}: {e}", dir.display())))? {
        let entry = entry.map_err(|e| Error(e.to_string()))?;
        let name = entry.file_name().into_string().map_err(|_| "attempt file name is not UTF-8")?;
        if name == RECORD || name.starts_with('.') {
            continue;
        }
        if entry.file_type().map_err(|e| Error(e.to_string()))?.is_file() {
            names.push(name);
        }
    }
    names.sort();
    let mut index = Vec::new();
    let mut payload = Vec::new();
    for name in &names {
        let bytes = raw(&dir.join(name))?;
        index.push(json!({"name": name, "length": bytes.len(), "sha256": sha256_hex(&bytes)}));
        payload.extend_from_slice(&bytes);
    }
    let mut record = MAGIC.to_vec();
    record.extend(serde_json::to_vec(&json!({"files": index})).map_err(|e| Error(e.to_string()))?);
    record.push(b'\n');
    record.extend(payload);
    let sealed = durable::create_new(&dir.join(RECORD), &record, Perm::Private)
        .map_err(|e| Error(format!("cannot seal {}: {e}", dir.display())));
    // From the seal on nothing is a cache: the answer files keep their own fsync (invariant 4).
    CacheScope::end();
    sealed
}

/// A file's bytes, no repair (for building the record).
fn raw(path: &Path) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    fs::File::open(path)
        .and_then(|f| f.take(FILE_MAX as u64 + 1).read_to_end(&mut bytes))
        .map_err(|e| Error(format!("{}: {e}", path.display())))?;
    if bytes.len() > FILE_MAX {
        return Err(Error(format!("{} exceeds the attempt file bound", path.display())));
    }
    Ok(bytes)
}

struct Entry {
    length: usize,
    sha256: String,
    offset: usize,
}

/// The record's index: name → (length, sha256, payload offset), and where the payload starts.
fn index(record: &Path) -> Result<Option<(Vec<(String, Entry)>, u64)>> {
    let mut file = match fs::File::open(record) {
        Ok(file) => file,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(Error(format!("{}: {e}", record.display()))),
    };
    let mut head = Vec::new();
    (&mut file).take((MAGIC.len() + INDEX_MAX + 1) as u64).read_to_end(&mut head).map_err(|e| Error(e.to_string()))?;
    let rest = head.strip_prefix(MAGIC).ok_or_else(|| Error(format!("{} is not a seal record", record.display())))?;
    let end = rest.iter().position(|b| *b == b'\n').ok_or_else(|| Error(format!("{} index is unbounded", record.display())))?;
    let value: Value = serde_json::from_slice(&rest[..end]).map_err(|e| Error(format!("{} index: {e}", record.display())))?;
    let mut offset = 0usize;
    let mut entries = Vec::new();
    for row in value["files"].as_array().ok_or("seal record index lacks files")? {
        let name = row["name"].as_str().ok_or("seal record row lacks a name")?.to_owned();
        let length = row["length"].as_u64().ok_or("seal record row lacks a length")? as usize;
        let sha256 = row["sha256"].as_str().ok_or("seal record row lacks a sha256")?.to_owned();
        entries.push((name, Entry { length, sha256, offset }));
        offset = offset.checked_add(length).ok_or("seal record overflows")?;
    }
    Ok(Some((entries, (MAGIC.len() + end + 1) as u64)))
}

/// The recorded bytes of one entry.
fn payload(record: &Path, start: u64, entry: &Entry) -> Result<Vec<u8>> {
    use std::io::{Seek, SeekFrom};
    let mut file = fs::File::open(record).map_err(|e| Error(e.to_string()))?;
    file.seek(SeekFrom::Start(start + entry.offset as u64)).map_err(|e| Error(e.to_string()))?;
    let mut bytes = vec![0; entry.length];
    file.read_exact(&mut bytes).map_err(|e| Error(format!("{} is truncated: {e}", record.display())))?;
    if sha256_hex(&bytes) != entry.sha256 {
        return Err(Error(format!("{} payload differs from its index", record.display())));
    }
    Ok(bytes)
}

/// Invariant 3 for one file: `Ok(Some(bytes))` when `path` is named by a `seal.record` beside it
/// (the cache now holds exactly these bytes, repaired durably if it was absent or torn),
/// `Ok(None)` when no record names it (read it as it is).
pub fn repair_file(path: &Path, current: Option<&[u8]>) -> Result<Option<Vec<u8>>> {
    let (Some(dir), Some(name)) = (path.parent(), path.file_name().and_then(|n| n.to_str())) else { return Ok(None) };
    if name == RECORD {
        return Ok(None);
    }
    let record = dir.join(RECORD);
    let Some((entries, start)) = index(&record)? else { return Ok(None) };
    let Some((_, entry)) = entries.iter().find(|(n, _)| n == name) else { return Ok(None) };
    if let Some(bytes) = current {
        if bytes.len() == entry.length && sha256_hex(bytes) == entry.sha256 {
            return Ok(Some(bytes.to_vec()));
        }
    }
    let bytes = payload(&record, start, entry)?;
    durable::replace(path, &bytes, Perm::Umask).map_err(|e| Error(format!("cannot repair {}: {e}", path.display())))?;
    Ok(Some(bytes))
}

/// Invariant 3 for a directory: every file its record names is checked and repaired. Returns how
/// many were repaired. A directory without a record is left as it is.
pub fn repair_dir(dir: &Path) -> Result<usize> {
    let record = dir.join(RECORD);
    let Some((entries, start)) = index(&record)? else { return Ok(0) };
    let mut repaired = 0;
    for (name, entry) in &entries {
        let path = dir.join(name);
        let current = fs::read(&path).ok();
        if current.as_ref().is_some_and(|b| b.len() == entry.length && sha256_hex(b) == entry.sha256) {
            continue;
        }
        let bytes = payload(&record, start, entry)?;
        durable::replace(&path, &bytes, Perm::Umask).map_err(|e| Error(format!("cannot repair {}: {e}", path.display())))?;
        repaired += 1;
    }
    Ok(repaired)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch(tag: &str) -> PathBuf {
        let p = std::env::temp_dir().join(format!("mini-sdk-phase-{tag}-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir_all(&p).unwrap();
        p
    }

    #[test]
    fn a_torn_or_missing_cache_is_repaired_from_the_record_and_unnamed_files_are_left_alone() {
        let dir = scratch("repair");
        fs::write(dir.join("plan.bin"), b"PLAN-BYTES").unwrap();
        fs::write(dir.join("call.bin"), [0u8, 1, 2, 255]).unwrap();
        seal(&dir).unwrap();
        assert!(seal(&dir).is_err(), "one record per attempt");
        // Intact: returned as is.
        assert_eq!(repair_file(&dir.join("plan.bin"), Some(b"PLAN-BYTES")).unwrap().unwrap(), b"PLAN-BYTES");
        // Torn (a crash before the cache's data reached disk): repaired, durably, from the record.
        fs::write(dir.join("plan.bin"), [0u8; 10]).unwrap();
        assert_eq!(repair_file(&dir.join("plan.bin"), Some(&[0u8; 10])).unwrap().unwrap(), b"PLAN-BYTES");
        assert_eq!(fs::read(dir.join("plan.bin")).unwrap(), b"PLAN-BYTES");
        // Missing: recreated.
        fs::remove_file(dir.join("call.bin")).unwrap();
        assert_eq!(repair_dir(&dir).unwrap(), 1);
        assert_eq!(fs::read(dir.join("call.bin")).unwrap(), [0u8, 1, 2, 255]);
        // Written after the seal (an answer): not named, never touched.
        fs::write(dir.join("outcome.json"), b"{}").unwrap();
        assert_eq!(repair_file(&dir.join("outcome.json"), Some(b"{}")).unwrap(), None);
        // No record at all: nothing to repair.
        let bare = scratch("bare");
        fs::write(bare.join("x"), b"x").unwrap();
        assert_eq!(repair_file(&bare.join("x"), Some(b"x")).unwrap(), None);
        assert_eq!(repair_dir(&bare).unwrap(), 0);
        let _ = fs::remove_dir_all(dir);
        let _ = fs::remove_dir_all(bare);
    }

    /// The shared bounded reader repairs: a torn cache (here: emptied, which also fails the size
    /// bound) and a missing one both read back as the record's bytes, and are fixed on disk.
    #[test]
    fn the_shared_reader_returns_the_record_s_bytes_for_a_torn_or_missing_cache() {
        let dir = scratch("reader");
        fs::write(dir.join("plan.bin"), b"PLAN").unwrap();
        fs::write(dir.join("intent.bin"), b"INTENT").unwrap();
        seal(&dir).unwrap();
        fs::write(dir.join("plan.bin"), b"").unwrap();
        assert_eq!(crate::fsread::read_regular(&dir.join("plan.bin"), 1, 100).unwrap(), b"PLAN");
        assert_eq!(fs::read(dir.join("plan.bin")).unwrap(), b"PLAN");
        fs::remove_file(dir.join("intent.bin")).unwrap();
        assert_eq!(crate::fsread::read_regular(&dir.join("intent.bin"), 0, 100).unwrap(), b"INTENT");
        // An unnamed file that is missing stays missing.
        assert!(crate::fsread::read_regular(&dir.join("outcome.json"), 0, 100).unwrap_err().is_not_found());
        let _ = fs::remove_dir_all(dir);
    }

    /// Inside a cache scope a file is staged and linked complete (a live reader never sees part of
    /// it) with no fsync of its own; the record is fsynced; after the seal nothing is a cache.
    #[test]
    fn caches_skip_their_fsync_until_the_seal_and_the_record_never_does() {
        let dir = scratch("scope");
        let scope = CacheScope::enter(&dir).unwrap();
        let before = durable::fsyncs();
        durable::create_new(&dir.join("plan.bin"), b"PLAN", Perm::Umask).unwrap();
        durable::create_new(&dir.join("call.bin"), b"CALL", Perm::Umask).unwrap();
        assert_eq!(durable::fsyncs(), before, "caches issue no fsync");
        assert_eq!(fs::read(dir.join("call.bin")).unwrap(), b"CALL");
        seal(&dir).unwrap();
        let sealed = durable::fsyncs();
        assert!(sealed > before, "the record is fsynced");
        durable::create_new(&dir.join("outcome.json"), b"{}", Perm::Umask).unwrap();
        assert!(durable::fsyncs() > sealed, "the seal ended the scope: answers are synced");
        drop(scope);
        let _ = fs::remove_dir_all(dir);
    }

    #[test]
    fn a_record_whose_payload_disagrees_with_its_index_refuses_rather_than_repairs() {
        let dir = scratch("tamper");
        fs::write(dir.join("call.bin"), b"CALL").unwrap();
        seal(&dir).unwrap();
        let mut record = fs::read(dir.join(RECORD)).unwrap();
        let last = record.len() - 1;
        record[last] ^= 1;
        fs::remove_file(dir.join(RECORD)).unwrap();
        fs::write(dir.join(RECORD), record).unwrap();
        fs::write(dir.join("call.bin"), b"XXXX").unwrap();
        assert!(repair_file(&dir.join("call.bin"), Some(b"XXXX")).is_err());
        let _ = fs::remove_dir_all(dir);
    }
}
