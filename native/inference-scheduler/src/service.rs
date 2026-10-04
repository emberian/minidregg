use crate::{
    core::{Config, Core},
    read_frame, write_frame, Command, Reply, Result,
};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::os::fd::AsRawFd;
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime, UNIX_EPOCH};

pub fn now_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis()
        .try_into()
        .unwrap_or(u64::MAX)
}

pub struct Service {
    pub config: Config,
    core: Core,
    directory: PathBuf,
    _lock: File,
    poisoned: bool,
    receipts: usize,
    receipt_bytes: u64,
    drained_receipts: usize,
}

// Bound one receipt including stale unsent lease guards. Admission reserves
// this much disk for every accepted live job before allowing provider work.
const MAX_RECEIPT_BYTES: u64 = 128 * 1024;
fn receipt_id(id: &str) -> bool {
    id.len() == 64
        && id
            .bytes()
            .all(|v| v.is_ascii_digit() || (b'a'..=b'f').contains(&v))
}

fn private(path: &Path, directory: bool) -> Result<()> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
        || (directory && !meta.is_dir())
        || (!directory && !meta.is_file())
    {
        return Err(format!(
            "scheduler {} must be private and owned by service uid",
            path.display()
        ));
    }
    Ok(())
}

impl Service {
    pub fn open(config: Config, directory: &Path) -> Result<Self> {
        config.validate()?;
        match fs::create_dir(directory) {
            Ok(()) => fs::set_permissions(directory, fs::Permissions::from_mode(0o700))
                .map_err(|e| e.to_string())?,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.to_string()),
        }
        private(directory, true)?;
        let lock_path = directory.join("lock");
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&lock_path)
            .map_err(|e| e.to_string())?;
        private(&lock_path, false)?;
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err("another scheduler owns this state directory".into());
        }
        let state_path = directory.join("state.json");
        let core = match fs::symlink_metadata(&state_path) {
            Ok(meta) => {
                private(&state_path, false)?;
                if meta.len() > 128 * 1024 * 1024 {
                    return Err("scheduler state exceeds bound".into());
                }
                serde_json::from_slice::<Core>(&fs::read(&state_path).map_err(|e| e.to_string())?)
                    .map_err(|e| format!("scheduler state: {e}"))?
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Core::new(&config)?,
            Err(error) => return Err(error.to_string()),
        };
        let archive = directory.join("receipts");
        match fs::create_dir(&archive) {
            Ok(()) => {
                fs::set_permissions(&archive, fs::Permissions::from_mode(0o700))
                    .map_err(|e| e.to_string())?;
                File::open(directory)
                    .and_then(|dir| dir.sync_all())
                    .map_err(|e| e.to_string())?;
            }
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
            Err(error) => return Err(error.to_string()),
        }
        private(&archive, true)?;
        let mut receipts = 0usize;
        let mut receipt_bytes = 0u64;
        for entry in fs::read_dir(&archive).map_err(|e| e.to_string())? {
            let path = entry.map_err(|e| e.to_string())?.path();
            // Only our reusable incomplete write can be ignored. Complete files
            // are immutable; fail closed on foreign names and objects.
            if path.file_name().and_then(|v| v.to_str()) == Some("pending") {
                private(&path, false)?;
                continue;
            }
            let id = path
                .file_name()
                .and_then(|v| v.to_str())
                .ok_or("invalid receipt name")?;
            if !receipt_id(id) {
                return Err("invalid receipt name".into());
            }
            private(&path, false)?;
            let size = fs::metadata(&path).map_err(|e| e.to_string())?.len();
            if size > MAX_RECEIPT_BYTES {
                return Err("terminal receipt exceeds bound".into());
            }
            receipts += 1;
            receipt_bytes = receipt_bytes
                .checked_add(size)
                .ok_or("receipt bytes overflow")?;
        }
        if receipts < core.archived_receipts || receipt_bytes < core.archived_bytes {
            return Err("terminal receipt archive lost evidence; restore complete archive".into());
        }
        let mut drained_receipts = core.archived_drained;
        if receipts != core.archived_receipts || receipt_bytes != core.archived_bytes {
            // A crash during receipt-before-snapshot retirement may leave extra
            // receipts. Rebuild only summary metadata; never discard evidence.
            drained_receipts = 0;
            for entry in fs::read_dir(&archive).map_err(|e| e.to_string())? {
                let path = entry.map_err(|e| e.to_string())?.path();
                if path.file_name().and_then(|v| v.to_str()) == Some("pending") {
                    continue;
                }
                let job: crate::core::Job =
                    serde_json::from_slice(&fs::read(&path).map_err(|e| e.to_string())?)
                        .map_err(|e| e.to_string())?;
                if !matches!(job.state, crate::core::State::Terminal { .. }) {
                    return Err("nonterminal archive record".into());
                }
                drained_receipts += usize::from(matches!(
                    job.state,
                    crate::core::State::Terminal {
                        outcome: crate::core::Outcome::Drained,
                        ..
                    }
                ));
            }
        }
        let mut service = Self {
            config,
            core,
            directory: directory.into(),
            _lock: lock,
            poisoned: false,
            receipts,
            receipt_bytes,
            drained_receipts,
        };
        let mut next = service.core.clone();
        for id in next.jobs.keys().cloned().collect::<Vec<_>>() {
            if let Some(receipt) = service.receipt(&id)? {
                // Completion and its fairness counters must already be in the
                // durable terminal snapshot before this receipt can exist.
                if next.jobs[&id] != receipt {
                    return Err("terminal archive conflicts with unresolved snapshot; restore matching snapshot and archive".into());
                }
            }
        }
        next.recover(&service.config)?;
        service.save(&mut next)?;
        service.core = next;
        Ok(service)
    }

    fn receipt(&self, id: &str) -> Result<Option<crate::core::Job>> {
        if !receipt_id(id) {
            return Err("invalid receipt identity".into());
        }
        let path = self.directory.join("receipts").join(id);
        match fs::symlink_metadata(&path) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error.to_string()),
            Ok(meta) if meta.len() > MAX_RECEIPT_BYTES => {
                return Err("terminal receipt exceeds bound".into())
            }
            Ok(_) => {}
        }
        private(&path, false)?;
        let job: crate::core::Job =
            serde_json::from_slice(&fs::read(&path).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
        if job.request.id != id || !matches!(job.state, crate::core::State::Terminal { .. }) {
            return Err("invalid terminal receipt".into());
        }
        Ok(Some(job))
    }

    fn save(&mut self, state: &mut Core) -> Result<()> {
        // Persist the whole transition, including fairness refunds/elapsed
        // service, before publishing receipts. The second snapshot retires only
        // terminal jobs whose receipts are then fully durable.
        let terminal: Vec<_> = state
            .jobs
            .iter()
            .filter(|(_, job)| matches!(job.state, crate::core::State::Terminal { .. }))
            .map(|(id, job)| (id.clone(), job.clone()))
            .collect();
        if !terminal.is_empty() {
            self.save_snapshot(state)?;
        }
        for (id, job) in terminal {
            if let Some(saved) = self.receipt(&id)? {
                if saved != job {
                    return Err("terminal receipt conflicts with snapshot".into());
                }
            } else {
                let bytes = serde_json::to_vec(&job).map_err(|e| e.to_string())?;
                if bytes.len() as u64 > MAX_RECEIPT_BYTES
                    || self.receipts >= self.config.max_terminal_receipts
                    || self.receipt_bytes.saturating_add(bytes.len() as u64)
                        > self.config.max_receipt_bytes
                {
                    return Err("terminal receipt archive exhausted; preserve state and increase archive budget".into());
                }
                let archive = self.directory.join("receipts");
                let temporary = archive.join("pending");
                if temporary.exists() {
                    private(&temporary, false)?;
                }
                let mut file = OpenOptions::new()
                    .write(true)
                    .create(true)
                    .truncate(true)
                    .mode(0o600)
                    .custom_flags(libc::O_NOFOLLOW)
                    .open(&temporary)
                    .map_err(|e| e.to_string())?;
                file.write_all(&bytes).map_err(|e| e.to_string())?;
                file.sync_all().map_err(|e| e.to_string())?;
                fs::rename(&temporary, archive.join(&id)).map_err(|e| e.to_string())?;
                File::open(&archive)
                    .and_then(|dir| dir.sync_all())
                    .map_err(|e| e.to_string())?;
                self.receipts += 1;
                self.receipt_bytes += bytes.len() as u64;
                self.drained_receipts += usize::from(matches!(
                    job.state,
                    crate::core::State::Terminal {
                        outcome: crate::core::Outcome::Drained,
                        ..
                    }
                ));
            }
            state.jobs.remove(&id);
        }
        state.archived_receipts = self.receipts;
        state.archived_bytes = self.receipt_bytes;
        state.archived_drained = self.drained_receipts;
        self.save_snapshot(state)
    }

    fn save_snapshot(&self, state: &Core) -> Result<()> {
        // The exclusive process lock makes this one reusable temporary name safe.
        // O_NOFOLLOW and file ownership prevent a stale foreign path being followed.
        let temporary = self.directory.join("state.pending");
        if temporary.exists() {
            private(&temporary, false)?;
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&temporary)
            .map_err(|e| e.to_string())?;
        serde_json::to_writer(&mut file, state).map_err(|e| e.to_string())?;
        file.write_all(b"\n").map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        fs::rename(&temporary, self.directory.join("state.json")).map_err(|e| e.to_string())?;
        File::open(&self.directory)
            .and_then(|dir| dir.sync_all())
            .map_err(|e| e.to_string())
    }

    pub fn execute(&mut self, uid: u32, command: Command, now: u64) -> Result<crate::core::Job> {
        if self.poisoned {
            return Err("scheduler durability failed; restart and reconcile".into());
        }
        let controller = command
            .controller()
            .ok_or("operator command requires operator path")?
            .to_owned();
        let registration = self
            .config
            .controllers
            .get(&controller)
            .ok_or("unregistered controller")?;
        if registration.uid != uid {
            return Err("controller peer uid differs from registration".into());
        }
        // Apply to a candidate. No acknowledgement or in-memory admission before fsync.
        let mut next = self.core.clone();
        next.schedule(&self.config, now)?;
        // Load only the addressed exact terminal receipt. Archive history never
        // occupies live admission memory or becomes dispatchable work.
        let requested_id = match &command {
            Command::Enqueue { job, .. } => Some(job.id.as_str()),
            Command::Inspect { id, .. }
            | Command::Dispatch { id, .. }
            | Command::Finish { id, .. }
            | Command::Cancel { id, .. } => Some(id.as_str()),
            _ => None,
        };
        if let Some(id) = requested_id {
            if !next.jobs.contains_key(id) {
                if let Some(job) = self.receipt(id)? {
                    next.jobs.insert(id.into(), job);
                }
            }
        }
        let id = match command {
            Command::Status { .. }
            | Command::StatusGroups { .. }
            | Command::Drain { .. }
            | Command::Resolve { .. } => {
                return Err("operator command requires operator path".into())
            }
            Command::Enqueue { job, .. } => {
                let id = job.id.clone();
                if !next.jobs.contains_key(&id) {
                    let live = next
                        .jobs
                        .values()
                        .filter(|job| !matches!(job.state, crate::core::State::Terminal { .. }))
                        .count();
                    if self.receipts.saturating_add(live).saturating_add(1)
                        > self.config.max_terminal_receipts
                        || self
                            .receipt_bytes
                            .saturating_add((live as u64 + 1).saturating_mul(MAX_RECEIPT_BYTES))
                            > self.config.max_receipt_bytes
                    {
                        return Err("terminal receipt archive admission full; increase archive budget, never delete receipts".into());
                    }
                }
                next.enqueue(&self.config, &controller, job, now)?;
                id
            }
            Command::Inspect { id, .. } => id,
            Command::Dispatch {
                id, lease, attempt, ..
            } => {
                next.dispatch(&controller, &id, lease, attempt, now)?;
                id
            }
            Command::Finish {
                id, lease, outcome, ..
            } => {
                next.finish(&controller, &id, lease, outcome, now)?;
                id
            }
            Command::Cancel { id, .. } => {
                next.cancel(&controller, &id)?;
                id
            }
        };
        next.schedule(&self.config, now)?;
        let reply = next.inspect(&controller, &id)?;
        if next != self.core {
            if let Err(error) = self.save(&mut next) {
                self.poisoned = true;
                return Err(error);
            }
            self.core = next;
        }
        Ok(reply)
    }

    pub fn operator(
        &mut self,
        uid: u32,
        draining: Option<bool>,
        after: Option<&str>,
        limit: u16,
        now: u64,
    ) -> Result<Status> {
        self.operator_page(uid, draining, None, after, limit, None, now)
    }

    pub fn operator_groups(&mut self, uid: u32, after: Option<&str>, now: u64) -> Result<Status> {
        self.operator_page(uid, None, None, None, 32, after, now)
    }

    pub fn operator_resolve(&mut self, uid: u32, id: &str, now: u64) -> Result<Status> {
        self.operator_page(uid, None, Some(id), None, 64, None, now)
    }

    #[allow(clippy::too_many_arguments)]
    fn operator_page(
        &mut self,
        uid: u32,
        draining: Option<bool>,
        resolve: Option<&str>,
        after: Option<&str>,
        limit: u16,
        group_after: Option<&str>,
        now: u64,
    ) -> Result<Status> {
        if uid != 0 && uid != unsafe { libc::geteuid() } {
            return Err("scheduler operator requires root or trusted service uid".into());
        }
        if self.poisoned {
            return Err("scheduler durability failed; restart and reconcile".into());
        }
        if limit == 0 || limit > 64 {
            return Err("status page limit must be 1..64".into());
        }
        let mut next = self.core.clone();
        if let Some(enabled) = draining {
            next.set_draining(enabled);
        }
        if let Some(id) = resolve {
            next.resolve(id, now)?;
        }
        next.schedule(&self.config, now)?;
        if next != self.core {
            if let Err(error) = self.save(&mut next) {
                self.poisoned = true;
                return Err(error);
            }
            self.core = next;
        }
        let mut status = Status::from_core(
            &self.config,
            &self.core,
            after,
            usize::from(limit),
            group_after,
        );
        status.counts.terminal += self.receipts;
        status.counts.drained += self.drained_receipts;
        status.terminal_receipts = self.receipts;
        status.receipt_bytes = self.receipt_bytes;
        status.max_terminal_receipts = self.config.max_terminal_receipts;
        status.max_receipt_bytes = self.config.max_receipt_bytes;
        Ok(status)
    }

    pub fn serve(&mut self, socket_path: &Path) -> Result<()> {
        let parent = socket_path.parent().ok_or("socket has no parent")?;
        private(parent, true)?;
        if let Ok(meta) = fs::symlink_metadata(socket_path) {
            if !meta.file_type().is_socket() || meta.uid() != unsafe { libc::geteuid() } {
                return Err("existing scheduler socket is not service-owned".into());
            }
            match UnixStream::connect(socket_path) {
                Ok(_) => return Err("scheduler socket is already active".into()),
                Err(error) if error.kind() == std::io::ErrorKind::ConnectionRefused => {
                    fs::remove_file(socket_path).map_err(|e| e.to_string())?
                }
                Err(error) => {
                    return Err(format!("cannot establish stale scheduler socket: {error}"))
                }
            }
        }
        let listener = UnixListener::bind(socket_path).map_err(|e| e.to_string())?;
        fs::set_permissions(socket_path, fs::Permissions::from_mode(0o600))
            .map_err(|e| e.to_string())?;
        // One owner serializes allocation and fsync. Frames are small and local;
        // per-frame timeout bounds an abandoned caller, no per-request thread swarm.
        for stream in listener.incoming() {
            let mut stream = stream.map_err(|e| e.to_string())?;
            stream
                .set_read_timeout(Some(Duration::from_secs(2)))
                .map_err(|e| e.to_string())?;
            stream
                .set_write_timeout(Some(Duration::from_secs(2)))
                .map_err(|e| e.to_string())?;
            let result = peer_uid(&stream).and_then(|uid| {
                read_frame(&mut stream).and_then(|command| match command {
                    Command::Status { after, limit } => self
                        .operator(uid, None, after.as_deref(), limit, now_ms())
                        .map(|status| Reply::Status {
                            status: Box::new(status),
                        }),
                    Command::StatusGroups { after } => self
                        .operator_groups(uid, after.as_deref(), now_ms())
                        .map(|status| Reply::Status {
                            status: Box::new(status),
                        }),
                    Command::Drain { enabled } => self
                        .operator(uid, Some(enabled), None, 64, now_ms())
                        .map(|status| Reply::Status {
                            status: Box::new(status),
                        }),
                    Command::Resolve { id } => self
                        .operator_resolve(uid, &id, now_ms())
                        .map(|status| Reply::Status {
                            status: Box::new(status),
                        }),
                    other => self
                        .execute(uid, other, now_ms())
                        .map(|job| Reply::Job { job: Box::new(job) }),
                })
            });
            let reply = result.unwrap_or_else(|reason| Reply::Refused { reason });
            let _ = write_frame(&mut stream, &reply);
        }
        Ok(())
    }
}

fn peer_uid(socket: &UnixStream) -> Result<u32> {
    #[cfg(target_os = "linux")]
    {
        let mut credentials: libc::ucred = unsafe { std::mem::zeroed() };
        let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        if unsafe {
            libc::getsockopt(
                socket.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                &mut credentials as *mut _ as *mut libc::c_void,
                &mut length,
            )
        } != 0
        {
            return Err(std::io::Error::last_os_error().to_string());
        }
        Ok(credentials.uid)
    }
    #[cfg(not(target_os = "linux"))]
    {
        let _ = socket;
        Err("scheduler peer authentication requires Linux".into())
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct Counts {
    pub queued: usize,
    pub placed: usize,
    pub running: usize,
    pub uncertain: usize,
    pub terminal: usize,
    pub drained: usize,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GroupStatus {
    pub capacity: usize,
    pub placed: usize,
    pub running: usize,
    pub uncertain: usize,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JobStatus {
    pub id: String,
    pub controller: String,
    pub principal: String,
    pub model: String,
    pub state: String,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Status {
    pub terminal_receipts: usize,
    pub receipt_bytes: u64,
    pub max_terminal_receipts: usize,
    pub max_receipt_bytes: u64,
    pub draining: bool,
    pub quiescent: bool,
    pub counts: Counts,
    pub groups: BTreeMap<String, GroupStatus>,
    pub jobs: Vec<JobStatus>,
    pub next_after: Option<String>,
    /// Continue groups with status-groups; job and group cursors are independent.
    pub next_group_after: Option<String>,
}
impl Status {
    fn from_core(
        config: &Config,
        core: &Core,
        after: Option<&str>,
        limit: usize,
        group_after: Option<&str>,
    ) -> Self {
        use crate::core::State;
        let mut counts = Counts::default();
        let mut groups: BTreeMap<_, _> = config
            .groups
            .iter()
            .map(|(name, capacity)| {
                (
                    name.clone(),
                    GroupStatus {
                        capacity: *capacity,
                        placed: 0,
                        running: 0,
                        uncertain: 0,
                    },
                )
            })
            .collect();
        let mut jobs = Vec::new();
        let mut has_more = false;
        for (id, job) in &core.jobs {
            let state = match &job.state {
                State::Queued => {
                    counts.queued += 1;
                    "queued"
                }
                State::Placed { group, .. } => {
                    counts.placed += 1;
                    groups.get_mut(group).unwrap().placed += 1;
                    "placed-unsent"
                }
                State::Dispatched {
                    group,
                    stop_requested,
                    ..
                } => {
                    counts.running += 1;
                    groups.get_mut(group).unwrap().running += 1;
                    if *stop_requested {
                        "stop-requested"
                    } else {
                        "running"
                    }
                }
                State::Uncertain { group, .. } => {
                    counts.uncertain += 1;
                    groups.get_mut(group).unwrap().uncertain += 1;
                    "uncertain"
                }
                State::Terminal { outcome, .. } => {
                    counts.terminal += 1;
                    if *outcome == crate::core::Outcome::Drained {
                        counts.drained += 1;
                    }
                    continue;
                }
            };
            if after.is_some_and(|after| id.as_str() <= after) {
                continue;
            }
            if jobs.len() == limit {
                has_more = true;
                continue;
            }
            jobs.push(JobStatus {
                id: id.clone(),
                controller: job.controller.clone(),
                principal: job.principal.clone(),
                model: job.request.model.clone(),
                state: state.into(),
            });
        }
        let mut status = Self {
            terminal_receipts: 0,
            receipt_bytes: 0,
            max_terminal_receipts: config.max_terminal_receipts,
            max_receipt_bytes: config.max_receipt_bytes,
            draining: core.draining,
            quiescent: counts.placed + counts.running + counts.uncertain == 0,
            counts,
            groups: BTreeMap::new(),
            jobs: Vec::new(),
            next_after: None,
            next_group_after: None,
        };
        // Count exact JSON item bytes, including escaped labels and the Reply
        // envelope. 1024 bytes conservatively cover both non-null cursors:
        // group names are <=256 UTF-8 bytes (<=514 JSON bytes), job IDs 64.
        let envelope = serde_json::to_vec(&Reply::Status {
            status: Box::new(status.clone()),
        })
        .expect("status is serializable")
        .len();
        let mut remaining = crate::MAX_FRAME - envelope - 1024;
        let mut groups = groups
            .into_iter()
            .filter(|(name, _)| group_after.is_none_or(|after| name.as_str() > after))
            .peekable();
        let group_bytes = |name: &String, group: &GroupStatus| {
            serde_json::to_vec(name)
                .expect("group name is serializable")
                .len()
                + serde_json::to_vec(group)
                    .expect("group is serializable")
                    .len()
                + 2
        };
        // Always leave room for one group; neither cursor can get stuck because
        // the other collection consumed the complete response budget.
        let group_reserve = groups
            .peek()
            .map(|(name, group)| group_bytes(name, group))
            .unwrap_or(0);
        for job in jobs {
            let bytes = serde_json::to_vec(&job).expect("job is serializable").len() + 1;
            if bytes + group_reserve > remaining {
                has_more = true;
                break;
            }
            remaining -= bytes;
            status.jobs.push(job);
        }
        if has_more {
            status.next_after = status.jobs.last().map(|job| job.id.clone());
        }
        for (name, group) in groups {
            let bytes = group_bytes(&name, &group);
            if bytes > remaining {
                status.next_group_after =
                    status.groups.last_key_value().map(|(name, _)| name.clone());
                break;
            }
            remaining -= bytes;
            status.groups.insert(name, group);
        }
        status
    }
}
