//! Physical exact-byte continuity. Lean alone interprets seed/record/tag bytes.
use crate::{DurableEntry, PublishPhase, StoreError};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

const MAGIC: &[u8; 8] = b"MINIANC1";
static NEXT: AtomicU64 = AtomicU64::new(0);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Head {
    seed: [u8; 32],
    pub height: u64,
    entry: [u8; 32],
}

impl Head {
    pub fn new(identity: &[u8], seed: &[u8], entry: Option<&DurableEntry>) -> Self {
        let mut genesis = Sha256::new();
        genesis.update(b"mini-opaque-anchor-genesis-v1");
        genesis.update((identity.len() as u64).to_be_bytes());
        genesis.update(identity);
        genesis.update((seed.len() as u64).to_be_bytes());
        genesis.update(seed);
        let mut digest = Sha256::new();
        digest.update(b"mini-opaque-anchor-entry-v1");
        if let Some(e) = entry {
            digest.update(e.height.to_be_bytes());
            digest.update((e.record.len() as u64).to_be_bytes());
            digest.update(&e.record);
            digest.update((e.tag.len() as u64).to_be_bytes());
            digest.update(&e.tag);
        }
        Self {
            seed: genesis.finalize().into(),
            height: entry.map_or(0, |e| e.height),
            entry: digest.finalize().into(),
        }
    }

    fn bytes(&self) -> Vec<u8> {
        [
            MAGIC.as_slice(),
            &self.seed,
            &self.height.to_be_bytes(),
            &self.entry,
        ]
        .concat()
    }

    fn decode(bytes: &[u8]) -> Result<Self, StoreError> {
        if bytes.len() != 80 || &bytes[..8] != MAGIC {
            return Err(StoreError::Anchor("invalid anchor bytes"));
        }
        Ok(Self {
            seed: bytes[8..40].try_into().unwrap(),
            height: u64::from_be_bytes(bytes[40..48].try_into().unwrap()),
            entry: bytes[48..80].try_into().unwrap(),
        })
    }
}

/// Sibling sidecar intentionally remains outside a copied/replaced Store directory.
pub fn path(root: &Path) -> PathBuf {
    let mut name = root.as_os_str().to_owned();
    name.push(".head-anchor");
    PathBuf::from(name)
}

pub(crate) struct Guard {
    path: PathBuf,
    _lock: File,
}

impl Guard {
    pub fn lock(root: &Path) -> Result<Self, StoreError> {
        let path = path(root);
        let mut lock_path = path.as_os_str().to_owned();
        lock_path.push(".lock");
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(lock_path)?;
        if !lock.metadata()?.is_file() {
            return Err(StoreError::Anchor("anchor lock is not a regular file"));
        }
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
        loop {
            // SAFETY: this owned file descriptor remains open throughout the guard.
            if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } == 0 {
                break;
            }
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::WouldBlock
                && std::time::Instant::now() < deadline
            {
                std::thread::sleep(std::time::Duration::from_millis(10));
                continue;
            }
            if error.kind() != std::io::ErrorKind::Interrupted {
                return Err(error.into());
            }
        }
        Ok(Self { path, _lock: lock })
    }

    pub fn read(&self) -> Result<Option<Head>, StoreError> {
        let file = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&self.path)
        {
            Ok(file) => file,
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(e) => return Err(e.into()),
        };
        let metadata = file.metadata()?;
        if !metadata.is_file() || metadata.permissions().mode() & 0o077 != 0 {
            return Err(StoreError::Anchor("anchor must be a private regular file"));
        }
        let mut bytes = Vec::new();
        file.take(81).read_to_end(&mut bytes)?;
        Ok(Some(Head::decode(&bytes)?))
    }

    pub fn publish(&self, head: &Head) -> Result<(), StoreError> {
        self.publish_with_hook(head, &mut |_| {})
    }

    pub fn publish_with_hook(
        &self,
        head: &Head,
        hook: &mut impl FnMut(PublishPhase),
    ) -> Result<(), StoreError> {
        if self.read()?.as_ref() == Some(head) {
            // A previous process may have died after rename but before the
            // directory sync. A retry must finish that durability boundary --
            // once per process: after this process has synced this exact head
            // at this path, the boundary is complete and nothing can undo it.
            if synced(&self.path, head) {
                return Ok(());
            }
            OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW)
                .open(&self.path)?
                .sync_all()?;
            File::open(self.path.parent().ok_or(StoreError::InvalidPath)?)?.sync_all()?;
            remember_synced(&self.path, head);
            return Ok(());
        }
        let mut temporary = self.path.as_os_str().to_owned();
        temporary.push(format!(
            ".{}.{}.tmp",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let temporary = PathBuf::from(temporary);
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&temporary)?;
        file.write_all(&head.bytes())?;
        file.sync_all()?;
        hook(PublishPhase::AnchorPrepared);
        fs::rename(&temporary, &self.path)?;
        hook(PublishPhase::AnchorRenamed);
        File::open(self.path.parent().ok_or(StoreError::InvalidPath)?)?.sync_all()?;
        remember_synced(&self.path, head);
        Ok(())
    }
}

/// Anchors this process has published or re-synced (path, head bytes). A
/// long-lived `serve` reads the anchor on every Host refresh; an unchanged
/// head needs its fsyncs once, not on every read.
static SYNCED: std::sync::Mutex<Vec<(PathBuf, Vec<u8>)>> = std::sync::Mutex::new(Vec::new());

fn synced(path: &Path, head: &Head) -> bool {
    let bytes = head.bytes();
    SYNCED.lock().is_ok_and(|seen| seen.iter().any(|(p, h)| p == path && *h == bytes))
}

fn remember_synced(path: &Path, head: &Head) {
    if let Ok(mut seen) = SYNCED.lock() {
        seen.retain(|(p, _)| p != path);
        seen.push((path.to_path_buf(), head.bytes()));
    }
}
