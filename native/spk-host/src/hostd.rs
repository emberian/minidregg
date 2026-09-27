//! Durable physical custody for one Mini-authorized application generation.
//!
//! This is not an admission path. A future adapter must construct `VerifiedBegin`
//! only from the native source-owned lifecycle receiver's original-prefix
//! receipt, exact event, and current pending query. In particular, a generic
//! resource transaction or caller JSON is never enough to start an app.

use crate::sandbox::open_protected_directory;
use crate::spawn_gate::{self, BoundedChild, SpawnSpec};
use serde::{Deserialize, Serialize};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

const VERSION: u32 = 1;
const MAX_RECORD_BYTES: u64 = 16 * 1024;

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Opaque physical identity derived from a future native verified BEGIN.
/// No public constructor exists: private socket input cannot mint one.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(crate) struct VerifiedBegin {
    pub app: u64,
    pub generation: u64,
    pub operation_id: u64,
    pub transaction_id: String,
    pub event_id: String,
    pub package_sha256: String,
    pub image_identity: String,
    pub process_identity: String,
    pub unit: String,
}

impl VerifiedBegin {
    fn validate(&self) -> io::Result<()> {
        if self.app == 0
            || self.generation == 0
            || !hex64(&self.transaction_id)
            || !hex64(&self.event_id)
            || !hex64(&self.package_sha256)
            || self.image_identity.is_empty()
            || self.image_identity.len() > 512
            || self.process_identity.is_empty()
            || self.process_identity.len() > 512
            || self.unit != format!("mini-spk-a{}-g{}.service", self.app, self.generation)
        {
            return Err(invalid("invalid verified BEGIN identity"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Phase {
    Armed,
    LaunchRequested,
    Entered,
    Running,
    Fenced,
    Stopped,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Record {
    version: u32,
    identity: VerifiedBegin,
    pub phase: Phase,
    pub child_pid: Option<u32>,
}

impl Record {
    pub fn app(&self) -> u64 {
        self.identity.app
    }
    pub fn generation(&self) -> u64 {
        self.identity.generation
    }
    pub fn unit(&self) -> &str {
        &self.identity.unit
    }
    pub fn transaction_id(&self) -> &str {
        &self.identity.transaction_id
    }
    pub fn event_id(&self) -> &str {
        &self.identity.event_id
    }

    fn validate(&self) -> io::Result<()> {
        if self.version != VERSION {
            return Err(invalid("unsupported hostd journal version"));
        }
        self.identity.validate()?;
        if matches!(self.phase, Phase::Armed | Phase::LaunchRequested) && self.child_pid.is_some() {
            return Err(invalid("prelaunch journal has child PID"));
        }
        if self.phase == Phase::Running && self.child_pid.is_none() {
            return Err(invalid("running journal lacks child PID"));
        }
        Ok(())
    }
}

/// One operation's protected directory, not a shared mutable app name. Its
/// `record.json` is never removed: a fenced operation cannot be rearmed.
#[derive(Clone, Debug)]
pub struct Journal {
    directory: PathBuf,
}

trait ChildHandle {
    fn pid(&self) -> u32;
    fn abort_under_lock(&mut self) -> io::Result<()>;
}

impl ChildHandle for BoundedChild {
    fn pid(&self) -> u32 {
        self.pid()
    }
    fn abort_under_lock(&mut self) -> io::Result<()> {
        if self.kill_and_reap() {
            Ok(())
        } else {
            Err(invalid(
                "spawned child could not be reaped under journal lock",
            ))
        }
    }
}

// The mutators are intentionally unreachable from the public binary until
// native verified BEGIN admission is wired. Keep the physical state machine
// separately testable without exposing an operator-minted launch command.
#[allow(dead_code)]
impl Journal {
    pub fn open(directory: &Path) -> io::Result<Self> {
        let uid = unsafe { libc::geteuid() };
        if !directory.is_absolute() {
            return Err(invalid("hostd state directory must be absolute"));
        }
        // Only root or this operator may own a path component. In particular,
        // an app UID cannot rename an otherwise private journal ancestor.
        for ancestor in directory.ancestors() {
            let meta = fs::symlink_metadata(ancestor)?;
            if !meta.is_dir()
                || meta.file_type().is_symlink()
                || (meta.uid() != 0 && meta.uid() != uid)
                || meta.permissions().mode() & 0o022 != 0
            {
                return Err(invalid(
                    "hostd journal ancestor is task-writable or symlinked",
                ));
            }
        }
        let protected = File::from(open_protected_directory(directory, u32::MAX, false)?);
        let metadata = fs::metadata(directory)?;
        if metadata.uid() != uid
            || metadata.permissions().mode() & 0o777 != 0o700
            || metadata.dev() != protected.metadata()?.dev()
            || metadata.ino() != protected.metadata()?.ino()
        {
            return Err(invalid(
                "hostd state directory must be owner-private and pinned",
            ));
        }
        Ok(Self {
            directory: directory.to_owned(),
        })
    }

    pub(crate) fn directory(&self) -> &Path {
        &self.directory
    }

    fn with_lock<T>(&self, f: impl FnOnce(&Self) -> io::Result<T>) -> io::Result<T> {
        let path = self.directory.join(".lock");
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path)?;
        let metadata = lock.metadata()?;
        if !metadata.is_file()
            || metadata.nlink() != 1
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.permissions().mode() & 0o777 != 0o600
        {
            return Err(invalid("hostd lock identity or mode drift"));
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX) } != 0 {
            return Err(io::Error::last_os_error());
        }
        // The lock remains held throughout the callback, including the spawn
        // handshake. Fence cannot linearize between gate entry and child spawn.
        let result = f(self);
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) } != 0 {
            return Err(io::Error::last_os_error());
        }
        result
    }

    fn read_unlocked(&self) -> io::Result<Option<Record>> {
        let path = self.directory.join("record.json");
        let file = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path)
        {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error),
        };
        let metadata = file.metadata()?;
        if !metadata.is_file()
            || metadata.nlink() != 1
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.permissions().mode() & 0o777 != 0o600
            || metadata.len() > MAX_RECORD_BYTES
        {
            return Err(invalid("hostd record identity, mode or length drift"));
        }
        let mut bytes = Vec::new();
        file.take(MAX_RECORD_BYTES + 1).read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MAX_RECORD_BYTES {
            return Err(invalid("hostd record grew"));
        }
        let record: Record = serde_json::from_slice(&bytes)?;
        record.validate()?;
        Ok(Some(record))
    }

    fn write_unlocked(&self, record: &Record) -> io::Result<()> {
        record.validate()?;
        let bytes = serde_json::to_vec(record)?;
        if bytes.len() as u64 > MAX_RECORD_BYTES {
            return Err(invalid("hostd record too large"));
        }
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| invalid("clock before epoch"))?
            .as_nanos();
        let temporary = self
            .directory
            .join(format!(".record-{}-{nonce}.tmp", std::process::id()));
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&temporary)?;
        let result = (|| {
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temporary, self.directory.join("record.json"))?;
            File::open(&self.directory)?.sync_all()
        })();
        if result.is_err() {
            let _ = fs::remove_file(&temporary);
        }
        result
    }

    pub fn read(&self) -> io::Result<Option<Record>> {
        self.with_lock(Self::read_unlocked)
    }

    pub(crate) fn arm(&self, begin: VerifiedBegin) -> io::Result<Record> {
        begin.validate()?;
        self.with_lock(|this| {
            if let Some(existing) = this.read_unlocked()? {
                if existing.identity == begin {
                    return Ok(existing);
                }
                return Err(invalid("conflicting BEGIN for durable operation"));
            }
            let record = Record {
                version: VERSION,
                identity: begin,
                phase: Phase::Armed,
                child_pid: None,
            };
            this.write_unlocked(&record)?;
            Ok(record)
        })
    }

    pub(crate) fn request_launch(&self, begin: &VerifiedBegin) -> io::Result<()> {
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if &record.identity != begin || record.phase != Phase::Armed {
                return Err(invalid("launch is not armed for this BEGIN"));
            }
            record.phase = Phase::LaunchRequested;
            this.write_unlocked(&record)
        })
    }

    /// Called as the exact service ExecStart, not as an out-of-unit preflight.
    /// The bounded fork/exec handshake occurs under the same lock as the
    /// Entered and Running fsyncs. On a Running write failure, the direct child
    /// is killed and reaped before releasing the lock. The journal remains
    /// uncertain and never grants an automatic retry.
    pub(crate) fn enter_and_spawn(
        &self,
        begin: &VerifiedBegin,
        spec: &SpawnSpec,
    ) -> io::Result<BoundedChild> {
        self.enter_and_spawn_with(
            begin,
            || spawn_gate::spawn_bounded(spec),
            Self::write_unlocked,
        )
    }

    fn enter_and_spawn_with<H: ChildHandle>(
        &self,
        begin: &VerifiedBegin,
        spawn: impl FnOnce() -> io::Result<H>,
        persist_running: impl FnOnce(&Self, &Record) -> io::Result<()>,
    ) -> io::Result<H> {
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if &record.identity != begin || record.phase != Phase::LaunchRequested {
                return Err(invalid("late or duplicate unit ExecStart refused"));
            }
            record.phase = Phase::Entered;
            this.write_unlocked(&record)?;
            let mut child = spawn()?;
            let pid = child.pid();
            if pid == 0 {
                child.abort_under_lock()?;
                return Err(invalid("spawn returned invalid PID"));
            }
            record.phase = Phase::Running;
            record.child_pid = Some(pid);
            if let Err(error) = persist_running(this, &record) {
                child.abort_under_lock()?;
                return Err(error);
            }
            Ok(child)
        })
    }

    /// Tombstone first; only then call the unit manager. An uncertain manager
    /// response retains Fenced and requires another exact-unit audit.
    pub(crate) fn fence_and_stop(
        &self,
        stop: impl FnOnce(&str) -> io::Result<()>,
        empty_cgroup: impl FnOnce(&str) -> io::Result<bool>,
    ) -> io::Result<()> {
        let unit = self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase == Phase::Stopped {
                return Ok(None);
            }
            record.phase = Phase::Fenced;
            this.write_unlocked(&record)?;
            Ok(Some(record.identity.unit))
        })?;
        let Some(unit) = unit else {
            return Ok(());
        };
        stop(&unit)?;
        if !empty_cgroup(&unit)? {
            return Err(invalid("exact unit cgroup still occupied"));
        }
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase != Phase::Fenced || record.identity.unit != unit {
                return Err(invalid("fence identity changed during stop"));
            }
            record.phase = Phase::Stopped;
            record.child_pid = None;
            this.write_unlocked(&record)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Barrier};
    use std::thread;

    struct MockChild {
        pid: u32,
        aborted: Arc<AtomicBool>,
    }
    impl ChildHandle for MockChild {
        fn pid(&self) -> u32 {
            self.pid
        }
        fn abort_under_lock(&mut self) -> io::Result<()> {
            self.aborted.store(true, Ordering::SeqCst);
            Ok(())
        }
    }
    fn child(pid: u32) -> MockChild {
        MockChild {
            pid,
            aborted: Arc::new(AtomicBool::new(false)),
        }
    }

    fn scratch() -> PathBuf {
        let runtime = std::env::var("XDG_RUNTIME_DIR").expect("Linux user runtime dir");
        let path = Path::new(&runtime).join(format!(
            "mini-spk-hostd-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    fn begin() -> VerifiedBegin {
        VerifiedBegin {
            app: 91,
            generation: 2,
            operation_id: 7,
            transaction_id: "a".repeat(64),
            event_id: "b".repeat(64),
            package_sha256: "c".repeat(64),
            image_identity: "image".into(),
            process_identity: "unit-generation-2".into(),
            unit: "mini-spk-a91-g2.service".into(),
        }
    }

    #[test]
    fn duplicate_conflict_and_fence_are_durable() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        assert_eq!(journal.arm(identity.clone()).unwrap().phase, Phase::Armed);
        let mut conflict = identity.clone();
        conflict.event_id = "d".repeat(64);
        assert!(journal.arm(conflict).is_err());
        journal.request_launch(&identity).unwrap();
        assert!(journal.request_launch(&identity).is_err());
        journal.fence_and_stop(|_| Ok(()), |_| Ok(true)).unwrap();
        assert_eq!(
            Journal::open(&path).unwrap().read().unwrap().unwrap().phase,
            Phase::Stopped
        );
        assert!(journal
            .enter_and_spawn_with(&identity, || Ok(child(123)), Journal::write_unlocked)
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn uncertain_start_and_stop_never_clear_tombstone_early() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                || Err::<MockChild, _>(invalid("injected start fault")),
                Journal::write_unlocked
            )
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Entered);
        assert!(journal
            .enter_and_spawn_with(&identity, || Ok(child(124)), Journal::write_unlocked)
            .is_err());
        assert!(journal
            .fence_and_stop(|_| Err(invalid("injected stop fault")), |_| Ok(true))
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Fenced);
        assert!(journal.fence_and_stop(|_| Ok(()), |_| Ok(false)).is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Fenced);
        journal.fence_and_stop(|_| Ok(()), |_| Ok(true)).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn fence_waits_for_spawn_linearization_then_stops_exact_unit() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        let entered = Arc::new(Barrier::new(2));
        let release = Arc::new(Barrier::new(2));
        let worker = {
            let journal = journal.clone();
            let identity = identity.clone();
            let entered = entered.clone();
            let release = release.clone();
            thread::spawn(move || {
                journal.enter_and_spawn_with(
                    &identity,
                    || {
                        entered.wait();
                        release.wait();
                        Ok(child(456))
                    },
                    Journal::write_unlocked,
                )
            })
        };
        entered.wait();
        let stopper = {
            let journal = journal.clone();
            thread::spawn(move || {
                journal.fence_and_stop(
                    |unit| {
                        assert_eq!(unit, "mini-spk-a91-g2.service");
                        Ok(())
                    },
                    |_| Ok(true),
                )
            })
        };
        release.wait();
        assert_eq!(worker.join().unwrap().unwrap().pid(), 456);
        stopper.join().unwrap().unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn running_fsync_failure_aborts_spawn_before_unlock() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        let aborted = Arc::new(AtomicBool::new(false));
        let observed = aborted.clone();
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                || Ok(MockChild { pid: 457, aborted }),
                |_, _| Err(invalid("injected Running fsync failure"))
            )
            .is_err());
        assert!(observed.load(Ordering::SeqCst));
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Entered);
        assert!(journal
            .enter_and_spawn_with(&identity, || Ok(child(458)), Journal::write_unlocked)
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }
}
