//! The operator-owned monotonic operation-id ledger the launch-bound lifecycle
//! authoring (BEGIN, claim, STOP) allocates from before source planning.

use crate::dispatch_native::private_dir;
use std::fs::File;
use std::fs::OpenOptions;
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

/// The operator-owned ledger allocates one monotonic identity before source
/// planning. A crash consumes an ID; it never reuses or silently retries it.
pub(crate) fn allocate_operation_id(ledger: &Path) -> io::Result<String> {
    let parent = ledger
        .parent()
        .ok_or_else(|| invalid("operation ledger parent absent"))?;
    private_dir(parent)?;
    let mut lock_name = ledger.as_os_str().to_os_string();
    lock_name.push(".lock");
    let lock_path = PathBuf::from(lock_name);
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&lock_path)?;
    let lock_named = std::fs::symlink_metadata(&lock_path)?;
    let lock_meta = lock.metadata()?;
    if !lock_meta.is_file()
        || lock_meta.nlink() != 1
        || lock_meta.uid() != unsafe { libc::geteuid() }
        || lock_meta.permissions().mode() & 0o777 != 0o600
        || (lock_named.dev(), lock_named.ino()) != (lock_meta.dev(), lock_meta.ino())
    {
        return Err(invalid("operation ledger lock identity refused"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX) } != 0 {
        return Err(io::Error::last_os_error());
    }
    let mut file = match OpenOptions::new()
        .read(true)
        .append(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(ledger)
    {
        Ok(mut file) => {
            // The first allocation is ID 1. Persist the next ID before
            // returning it; an interrupted empty creation stays refused.
            file.write_all(b"2\n")?;
            file.sync_all()?;
            File::open(parent)?.sync_all()?;
            return Ok("1".to_owned());
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => OpenOptions::new()
            .read(true)
            .append(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(ledger)?,
        Err(error) => return Err(error),
    };
    let named = std::fs::symlink_metadata(ledger)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > 1_048_576
        || (named.dev(), named.ino()) != (meta.dev(), meta.ino())
    {
        return Err(invalid(
            "operation ledger identity or incomplete write refused",
        ));
    }
    let mut history = String::new();
    file.read_to_string(&mut history)?;
    if history.len() as u64 != meta.len() || !history.ends_with('\n') {
        return Err(invalid("operation ledger incomplete tail refused"));
    }
    let mut expected = 2u64;
    for record in history.lines() {
        if !decimal(record) || record.parse::<u64>().ok() != Some(expected) {
            return Err(invalid("operation ledger sequence refused"));
        }
        expected = expected
            .checked_add(1)
            .ok_or_else(|| invalid("operation ledger exhausted"))?;
    }
    let current = expected - 1;
    writeln!(file, "{expected}")?;
    file.sync_all()?;
    File::open(parent)?.sync_all()?;
    Ok(current.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::DirBuilder;
    use std::os::unix::fs::DirBuilderExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch() -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "spk-operation-ledger-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn interrupted_ledger_creation_or_append_refuses_reuse() {
        let directory = scratch();
        let ledger = directory.join("begin.log");
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&ledger)
            .unwrap();
        assert!(allocate_operation_id(&ledger).is_err());
        std::fs::write(&ledger, b"2").unwrap();
        assert!(allocate_operation_id(&ledger).is_err());
        std::fs::write(&ledger, b"2\n").unwrap();
        assert_eq!(allocate_operation_id(&ledger).unwrap(), "2");
        assert_eq!(std::fs::read(&ledger).unwrap(), b"2\n3\n");
        std::fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn concurrent_allocations_keep_distinct_durable_ids() {
        let directory = scratch();
        let ledger = directory.join("begin.log");
        let joins: Vec<_> = (0..16)
            .map(|_| {
                let ledger = ledger.clone();
                std::thread::spawn(move || {
                    allocate_operation_id(&ledger)
                        .unwrap()
                        .parse::<u64>()
                        .unwrap()
                })
            })
            .collect();
        let mut ids: Vec<_> = joins.into_iter().map(|join| join.join().unwrap()).collect();
        ids.sort_unstable();
        assert_eq!(ids, (1..=16).collect::<Vec<_>>());
        assert_eq!(allocate_operation_id(&ledger).unwrap(), "17");
        std::fs::remove_dir_all(directory).unwrap();
    }
}
