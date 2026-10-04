//! The crate's one door to durable file publication: String-error adapters over
//! `mini_sdk::durable`, which stages every file in a unique sibling, fsyncs it, commits the final
//! name atomically and fsyncs the directory. No custody file in this crate is ever written to its
//! final name directly; a crash leaves the name absent or complete (create) or old or new
//! (replace).
use std::path::Path;

use ed25519_dalek::SigningKey;
use mini_sdk::durable::{self, Perm, RetainError, Retained};
use mini_sdk::secret::{self, Custody};
use zeroize::Zeroizing;

use crate::Result;

/// A new owner-private (0600) file: absent or complete, never replaced. Secrets go through here.
pub(crate) fn create_private(path: &Path, bytes: &[u8]) -> Result<()> {
    durable::create_new(path, bytes, Perm::Private).map_err(|e| format!("cannot create {}: {e}", path.display()))
}

/// A new owner-private JSON file (pretty, newline-terminated), then every ancestor directory
/// synced: retained evidence a recovery may rely on.
pub(crate) fn retain_json(path: &Path, value: &serde_json::Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or_else(|| format!("{} has no parent directory", path.display()))?)
}

/// A new file whose permissions the umask decides (public keys, public outputs).
pub(crate) fn create_public(path: &Path, bytes: &[u8]) -> Result<()> {
    durable::create_new(path, bytes, Perm::Umask).map_err(|e| format!("cannot create {}: {e}", path.display()))
}

/// A new file (permissions by umask) copied from `source`, absent or complete.
pub(crate) fn copy_new(source: &Path, destination: &Path) -> Result<()> {
    let mut input = std::fs::File::open(source).map_err(|e| format!("cannot open {}: {e}", source.display()))?;
    let length = input.metadata().ok().and_then(|m| usize::try_from(m.len()).ok());
    durable::create_new_from(destination, &mut input, length, Perm::Umask, &mut |_| Ok(()))
        .map_err(|e| format!("cannot copy {} to {}: {e}", source.display(), destination.display()))
}

/// Atomically replace (or create) a file whose permissions the umask decides (status and lab outputs).
pub(crate) fn replace_public(path: &Path, bytes: &[u8]) -> Result<()> {
    durable::replace(path, bytes, Perm::Umask).map_err(|e| format!("cannot replace {}: {e}", path.display()))
}

/// Atomically replace (or create) an owner-private file: old bytes or new bytes, never a prefix.
pub(crate) fn replace_private(path: &Path, bytes: &[u8]) -> Result<()> {
    durable::replace(path, bytes, Perm::Private).map_err(|e| format!("cannot replace {}: {e}", path.display()))
}

/// Retain `bytes` at `path` exactly once: created durably if absent; if present they must be
/// identical (and are re-synced), else the refusal is `differs`.
pub(crate) fn retain_exact(path: &Path, bytes: &[u8], differs: impl FnOnce() -> String) -> Result<Retained> {
    durable::retain_exact(path, bytes, Perm::Private).map_err(|e| match e {
        RetainError::Differs => differs(),
        RetainError::Io(e) => format!("cannot retain {}: {e}", path.display()),
    })
}

/// fsync the directory holding `path`.
pub(crate) fn sync_parent(path: &Path) -> Result<()> {
    durable::sync_parent(path).map_err(|e| format!("cannot sync the directory of {}: {e}", path.display()))
}

/// fsync `directory` and every ancestor.
pub(crate) fn sync_directory_ancestors(directory: &Path) -> Result<()> {
    durable::sync_ancestors(directory).map_err(|e| format!("cannot sync directory {}: {e}", directory.display()))
}

/// The crate's one secret-file loader. Custody is checked on the opened descriptor and the file
/// must be owner-private and is never reached through a symlink; the `_in_private_dir` forms
/// also require an owner-private containing directory.
fn seed_with(path: &Path, custody: Custody) -> Result<Zeroizing<[u8; 32]>> {
    secret::read_seed(path, custody).map_err(|e| e.to_string())
}

/// A 32-byte seed file (an Ed25519 signing seed, a symmetric key).
pub(crate) fn read_seed(path: &Path) -> Result<Zeroizing<[u8; 32]>> {
    seed_with(path, Custody::FileNoFollow)
}

/// [`read_seed`], also requiring an owner-private containing directory.
pub(crate) fn read_seed_in_private_dir(path: &Path) -> Result<Zeroizing<[u8; 32]>> {
    seed_with(path, Custody::FileAndDirectory)
}

/// The Ed25519 signing key whose seed is the private file at `path`.
pub(crate) fn read_secret(path: &Path) -> Result<SigningKey> {
    Ok(SigningKey::from_bytes(&*read_seed(path)?))
}

/// [`read_secret`], also requiring an owner-private containing directory.
pub(crate) fn read_secret_in_private_dir(path: &Path) -> Result<SigningKey> {
    Ok(SigningKey::from_bytes(&*read_seed_in_private_dir(path)?))
}

/// A private file of `1..=limit` bytes in an owner-private directory (evidence and custody
/// input that is not necessarily a key).
pub(crate) fn read_private_in_private_dir(path: &Path, limit: usize) -> Result<Vec<u8>> {
    secret::read_private(path, limit, Custody::FileAndDirectory).map(|bytes| bytes.to_vec()).map_err(|e| e.to_string())
}

/// A private file of `0..=limit` bytes (an empty marker is a valid answer), never through a symlink.
pub(crate) fn read_private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    secret::read_private_or_empty(path, limit, Custody::FileNoFollow).map(|bytes| bytes.to_vec()).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn scratch(tag: &str) -> std::path::PathBuf {
        let p = std::env::temp_dir().join(format!("mini-fsio-{tag}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&p);
        std::fs::create_dir_all(&p).unwrap();
        p
    }

    #[test]
    fn private_creation_is_complete_private_and_never_a_replacement() {
        let dir = scratch("create");
        let path = dir.join("seed");
        create_private(&path, &[7; 32]).unwrap();
        assert_eq!(std::fs::read(&path).unwrap(), [7; 32]);
        assert_eq!(std::fs::metadata(&path).unwrap().permissions().mode() & 0o777, 0o600);
        assert!(create_private(&path, &[8; 32]).unwrap_err().contains("cannot create"));
        assert_eq!(std::fs::read(&path).unwrap(), [7; 32], "the first bytes stand");
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1, "no staging file survives");
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn retention_is_idempotent_for_the_same_bytes_and_refuses_different_ones() {
        let dir = scratch("retain");
        let path = dir.join("frame.bin");
        assert_eq!(retain_exact(&path, b"exact", || "differs".into()).unwrap(), Retained::Created);
        assert_eq!(retain_exact(&path, b"exact", || "differs".into()).unwrap(), Retained::Matched);
        assert_eq!(retain_exact(&path, b"other", || "differs".into()).unwrap_err(), "differs");
        assert_eq!(std::fs::read(&path).unwrap(), b"exact");
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn replacement_is_old_or_new_and_leaves_no_staging_file() {
        let dir = scratch("replace");
        let path = dir.join("state.json");
        replace_private(&path, b"one").unwrap();
        replace_private(&path, b"two").unwrap();
        assert_eq!(std::fs::read(&path).unwrap(), b"two");
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1);
        std::fs::remove_dir_all(dir).unwrap();
    }
}
