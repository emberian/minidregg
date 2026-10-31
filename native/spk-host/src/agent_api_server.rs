//! Private agent API entrance in the same MainPID as the resident WebSession.
//! The controller's Unix peer is transport identity. Mini's freshly captured
//! op46 event21 committed permit is the only delivery authority.
#![allow(dead_code)] // Resident listener is enabled only with the reverse v2 reserve client.

use crate::io_context::IoContext;
use crate::agent_api_custody::AgentCustody;
use crate::agent_api_native::{authorize_once, hex, ReserveSubmit, RetainedReserve};
use crate::agent_api_wire::{self, FixedBinding, OrdinaryHeader, Reply, Request};
use crate::dispatch_inspection::{app_route_path, HttpProjection, MatchedInspection, Route};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::dispatch_web_input::physical_web_input;
use crate::hostd::{DispatchIdentity, Journal};
use crate::http_response;
use crate::rpc_adapter::{PrequeueGuard, RpcDriver};
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

const PROTOCOL: &str = "mini-spk-agent-api-v1";
const MAX_APP_RESPONSE: usize = 65_536;

fn invalid(message: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

fn socket_lock_path(path: &Path) -> io::Result<PathBuf> {
    let mut name = path.file_name().ok_or_else(|| invalid("agent socket filename absent"))?.to_os_string();
    name.push(".lock");
    Ok(path.with_file_name(name))
}

// Keep this inode after release: unlinking a lock permits two owners of two
// different lock files at the same pathname. Preflight never creates it.
fn socket_lock(path: &Path, create: bool) -> io::Result<Option<File>> {
    let file = match OpenOptions::new().read(true).write(true).create(create)
        .mode(0o600).custom_flags(libc::O_NOFOLLOW).open(socket_lock_path(path)?) {
        Ok(file) => file,
        Err(error) if !create && error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    let meta = file.metadata()?;
    if !meta.is_file() || meta.nlink() != 1 || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o7777 != 0o600 {
        return Err(invalid("agent socket lock identity refused"));
    }
    if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(invalid("agent socket listener lock held"));
    }
    Ok(Some(file))
}

/// An existing endpoint is reusable only when it is exactly our socket/ACL
/// and a bounded connection explicitly reports ECONNREFUSED. Busy, linked,
/// foreign, changed, or otherwise uncertain paths remain untouched.
fn stale_socket(path: &Path, expected_uid: u32) -> io::Result<Option<fs::Metadata>> {
    let meta = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    };
    let owner = unsafe { libc::geteuid() };
    let mode = if expected_uid == owner { 0o600 } else { 0o660 };
    if !meta.file_type().is_socket() || meta.uid() != owner || meta.nlink() != 1
        || meta.mode() & 0o7777 != mode {
        return Err(invalid("agent stale socket identity refused"));
    }
    exact_acl(path, expected_uid, false, false)?;
    match crate::dispatch_native::connect_deadline(path, Instant::now() + Duration::from_millis(250)) {
        Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => Ok(Some(meta)),
        Ok(_) => Err(invalid("agent socket still accepting")),
        Err(error) => Err(error),
    }
}

fn remove_stale_socket(path: &Path, expected_uid: u32) -> io::Result<Option<fs::Metadata>> {
    let old = stale_socket(path, expected_uid)?;
    if let Some(old) = &old {
        let current = fs::symlink_metadata(path)?;
        if (current.dev(), current.ino(), current.ctime(), current.ctime_nsec())
            != (old.dev(), old.ino(), old.ctime(), old.ctime_nsec()) {
            return Err(invalid("agent stale socket changed"));
        }
        fs::remove_file(path)?;
    }
    Ok(old)
}

/// Transport repair for an older pinned resident. This sends no Mini operation,
/// changes no journal/config, and cannot reclaim an accepting listener.
pub(crate) fn reclaim_socket(path: &Path, expected_uid: u32) -> io::Result<Value> {
    if expected_uid == 0 || !path.is_absolute() {
        return Err(invalid("agent socket pin refused"));
    }
    protected_agent_socket_parent(path.parent().ok_or_else(|| invalid("agent socket parent absent"))?, expected_uid, false)?;
    let _lock = socket_lock(path, true)?;
    let old = remove_stale_socket(path, expected_uid)?;
    Ok(serde_json::json!({"protocol":"mini-spk-agent-socket-reclaim-v1", "socket":path,
        "controllerUid":expected_uid,"ownerUid":unsafe {libc::geteuid()},"removed":old.is_some(),
        "previous":old.map(|meta| serde_json::json!({"device":meta.dev(),"inode":meta.ino(),
            "mode":meta.mode() & 0o7777,"uid":meta.uid()})),"nativeOperationSubmitted":false}))
}

fn string<'a>(value: &'a Value, field: &str) -> io::Result<&'a str> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("agent permit field absent"))
}

fn decimal<'a>(value: &'a Value, field: &str) -> io::Result<&'a str> {
    let text = string(value, field)?;
    if !crate::canonical::decimal(text) {
        return Err(invalid("agent permit decimal noncanonical"));
    }
    Ok(text)
}

pub(crate) fn unhex32(value: &str) -> io::Result<[u8; 32]> {
    if !crate::canonical::hex64(&value)
    {
        return Err(invalid("agent identity hex refused"));
    }
    crate::canonical::unhex_array(value).ok_or_else(|| invalid("agent identity hex byte"))
}

pub(crate) fn digest_nat(value: &str) -> io::Result<[u8; 32]> {
    let mut bytes = [0u8; 32];
    for digit in value.bytes() {
        if !digit.is_ascii_digit() {
            return Err(invalid("agent fingerprint decimal"));
        }
        let mut carry = u16::from(digit - b'0');
        for byte in &mut bytes {
            let next = u16::from(*byte) * 10 + carry;
            *byte = next as u8;
            carry = next >> 8;
        }
        if carry != 0 {
            return Err(invalid("agent fingerprint overflow"));
        }
    }
    Ok(bytes)
}

/// The ACL entries of `path` as `getfacl -cpn` lists them (`user::rw-`, `user:1000:rw-`, `group::---`,
/// `mask::rw-`, `other::---`), read from the `system.posix_acl_access` xattr of the path itself (never
/// through a symlink): no process per accepted connection. A file with no extended ACL has the entries
/// its mode bits give.
fn acl_entries(path: &Path) -> io::Result<Vec<String>> {
    use std::os::unix::ffi::OsStrExt;
    let c_path = std::ffi::CString::new(path.as_os_str().as_bytes())
        .map_err(|_| invalid("agent socket ACL path refused"))?;
    let mut buffer = [0u8; 4 + 8 * 32];
    let size = unsafe {
        libc::lgetxattr(
            c_path.as_ptr(),
            c"system.posix_acl_access".as_ptr(),
            buffer.as_mut_ptr().cast(),
            buffer.len(),
        )
    };
    if size < 0 {
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::ENODATA) {
            return Err(invalid("agent socket ACL inspection refused"));
        }
        let mode = fs::symlink_metadata(path).ctx("inspect", &path)?.mode();
        return Ok(vec![
            format!("user::{}", acl_perm(mode >> 6)),
            format!("group::{}", acl_perm(mode >> 3)),
            format!("other::{}", acl_perm(mode)),
        ]);
    }
    parse_posix_acl(&buffer[..size as usize])
}

fn acl_perm(bits: u32) -> String {
    [(4, 'r'), (2, 'w'), (1, 'x')]
        .iter()
        .map(|(bit, letter)| if bits & bit != 0 { *letter } else { '-' })
        .collect()
}

/// The Linux `posix_acl_xattr` image: version 2 (LE u32), then 8-byte entries (tag u16, perm u16, id u32).
fn parse_posix_acl(bytes: &[u8]) -> io::Result<Vec<String>> {
    let refused = || invalid("agent socket ACL inspection encoding");
    let (header, entries) = bytes.split_at_checked(4).ok_or_else(refused)?;
    if header != 2u32.to_le_bytes() || entries.len() % 8 != 0 {
        return Err(refused());
    }
    let mut lines = Vec::new();
    for entry in entries.chunks_exact(8) {
        let tag = u16::from_le_bytes([entry[0], entry[1]]);
        let perm = acl_perm(u32::from(u16::from_le_bytes([entry[2], entry[3]])));
        let id = u32::from_le_bytes([entry[4], entry[5], entry[6], entry[7]]);
        lines.push(match tag {
            0x01 => format!("user::{perm}"),
            0x02 => format!("user:{id}:{perm}"),
            0x04 => format!("group::{perm}"),
            0x08 => format!("group:{id}:{perm}"),
            0x10 => format!("mask::{perm}"),
            0x20 => format!("other::{perm}"),
            _ => return Err(refused()),
        });
    }
    Ok(lines)
}

fn exact_acl(path: &Path, controller_uid: u32, directory: bool, install: bool) -> io::Result<()> {
    let owner_uid = unsafe { libc::geteuid() };
    let owner = if directory { "user::rwx" } else { "user::rw-" };
    let other_uid = if directory { "--x" } else { "rw-" };
    if install && controller_uid != owner_uid {
        let grant = format!("u:{controller_uid}:{other_uid}");
        let status = Command::new("/usr/bin/setfacl")
            .args(["-m", &grant])
            .arg(path)
            .status()?;
        if !status.success() {
            return Err(invalid("agent socket ACL install refused"));
        }
    }
    let mut actual = acl_entries(path)?;
    let mut expected = vec![owner.to_owned(), "group::---".into(), "other::---".into()];
    if controller_uid != owner_uid {
        expected.push(format!("user:{controller_uid}:{other_uid}"));
        expected.push(format!("mask::{other_uid}"));
    }
    expected.sort();
    actual.sort();
    if actual != expected {
        return Err(invalid("agent socket ACL grants unexpected peer"));
    }
    Ok(())
}

fn protected_agent_socket_parent(
    parent: &Path,
    controller_uid: u32,
    install_acl: bool,
) -> io::Result<()> {
    if !parent.is_absolute() {
        return Err(invalid("agent socket parent is not absolute"));
    }
    let owner_uid = unsafe { libc::geteuid() };
    for (depth, ancestor) in parent.ancestors().enumerate() {
        let metadata = fs::symlink_metadata(&ancestor).ctx("inspect", &ancestor)?;
        let root_owned = crate::namespace_identity::root_owned(ancestor, &metadata);
        let sticky_root = depth > 0 && root_owned && metadata.mode() & 0o1000 != 0;
        if !metadata.is_dir()
            || metadata.mode() & 0o022 != 0 && !sticky_root
            || !root_owned
                && metadata.uid() != owner_uid
                && metadata.uid() != controller_uid
        {
            return Err(invalid("agent socket ancestor is not protected"));
        }
        if depth == 0 {
            if metadata.uid() != owner_uid || metadata.mode() & 0o007 != 0 {
                return Err(invalid("agent socket directory owner/mode refused"));
            }
        } else if controller_uid != owner_uid
            && metadata.uid() != controller_uid
            && metadata.mode() & 0o001 == 0
        {
            // A distinct controller must traverse every ancestor. The exact
            // named-UID leaf ACL cannot repair a private host home above it.
            return Err(invalid("controller cannot traverse agent socket ancestor"));
        }
    }
    if install_acl {
        exact_acl(parent, controller_uid, true, true)
    } else if exact_acl(parent, controller_uid, true, false).is_ok() {
        Ok(())
    } else {
        // An operator-private 0700 parent may acquire only the controller's
        // exact named-UID traverse ACL when bind follows START completion.
        exact_acl(parent, owner_uid, true, false)
    }
}

/// Watches the caller's connection for the rest of one request. The watcher thread sleeps in
/// `poll(2)` on the connection and on an eventfd that `Drop` signals: it wakes only when the caller
/// sends, hangs up or errors (what the former 10 ms `MSG_PEEK` loop detected), or when the request
/// ends, so there is no timer and `Drop` joins at once.
pub(crate) struct CallerWatch {
    pub(crate) cancelled: Arc<AtomicBool>,
    done: std::os::fd::OwnedFd,
    thread: Option<JoinHandle<()>>,
}

impl CallerWatch {
    pub(crate) fn start(stream: &UnixStream) -> io::Result<Self> {
        use std::os::fd::{FromRawFd, OwnedFd};
        let stream = stream.try_clone()?;
        let raw = unsafe { libc::eventfd(0, libc::EFD_CLOEXEC) };
        if raw < 0 {
            return Err(io::Error::last_os_error());
        }
        let done = unsafe { OwnedFd::from_raw_fd(raw) };
        let wake = done.try_clone()?;
        let cancelled = Arc::new(AtomicBool::new(false));
        let observed = cancelled.clone();
        let thread = thread::spawn(move || {
            let mut fds = [
                libc::pollfd { fd: stream.as_raw_fd(), events: libc::POLLIN | libc::POLLRDHUP, revents: 0 },
                libc::pollfd { fd: wake.as_raw_fd(), events: libc::POLLIN, revents: 0 },
            ];
            loop {
                let ready = unsafe { libc::poll(fds.as_mut_ptr(), 2, -1) };
                if ready < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                // Anything on the connection (data, EOF, hang-up, error), or a poll failure,
                // means the caller is no longer a silent waiter; a wake with the connection
                // quiet means the request is over.
                if ready < 0 || fds[0].revents != 0 {
                    observed.store(true, Ordering::Release);
                }
                break;
            }
        });
        Ok(Self {
            cancelled,
            done,
            thread: Some(thread),
        })
    }
}

impl Drop for CallerWatch {
    fn drop(&mut self) {
        let one = 1u64.to_ne_bytes();
        unsafe { libc::write(self.done.as_raw_fd(), one.as_ptr().cast(), one.len()) };
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

pub(crate) struct AgentApiListener {
    listener: UnixListener,
    socket: PathBuf,
    socket_identity: (u64, u64),
    expected_uid: u32,
    _lock: File,
}

impl Drop for AgentApiListener {
    fn drop(&mut self) {
        if let Ok(metadata) = fs::symlink_metadata(&self.socket) {
            if metadata.file_type().is_socket()
                && (metadata.dev(), metadata.ino()) == self.socket_identity
            {
                let _ = fs::remove_file(&self.socket).ctx("remove", &self.socket);
            }
        }
    }
}

impl AgentApiListener {
    /// Read-only START preflight. Bind may add only the exact controller ACL
    /// after START completion; the protected parent and ancestors are fixed.
    /// A dead exact socket may survive SIGKILL. Inspect it without removing it.
    pub(crate) fn preflight_parent(path: &Path, expected_uid: u32) -> io::Result<()> {
        if expected_uid == 0 || !path.is_absolute() {
            return Err(invalid("agent socket preflight pin refused"));
        }
        protected_agent_socket_parent(
            path.parent()
                .ok_or_else(|| invalid("agent socket parent absent"))?,
            expected_uid,
            false,
        )?;
        let _lock = socket_lock(path, false)?;
        stale_socket(path, expected_uid)?;
        Ok(())
    }

    pub(crate) fn as_raw_fd(&self) -> std::os::fd::RawFd {
        self.listener.as_raw_fd()
    }

    /// Bind only within an already protected operator directory. The socket
    /// owner/permission is checked again on every accepted connection.
    pub(crate) fn bind(path: &Path, expected_uid: u32) -> io::Result<Self> {
        let parent = path
            .parent()
            .ok_or_else(|| invalid("agent socket parent absent"))?;
        if expected_uid == 0 || !path.is_absolute() {
            return Err(invalid("agent socket pin refused"));
        }
        protected_agent_socket_parent(parent, expected_uid, true)?;
        let lock = socket_lock(path, true)?.ok_or_else(|| invalid("agent socket lock absent"))?;
        remove_stale_socket(path, expected_uid)?;
        let listener = UnixListener::bind(&path).ctx("bind", &path)?;
        let bound = fs::symlink_metadata(&path).ctx("inspect", &path)?;
        let setup = (|| {
            fs::set_permissions(path, fs::Permissions::from_mode(0o600)).ctx("set permissions", &path)?;
            exact_acl(path, expected_uid, false, true)?;
            listener.set_nonblocking(true)?;
            let metadata = fs::symlink_metadata(&path).ctx("inspect", &path)?;
            if !metadata.file_type().is_socket()
                || metadata.uid() != unsafe { libc::geteuid() }
                || (metadata.dev(), metadata.ino()) != (bound.dev(), bound.ino())
            {
                return Err(invalid("bound agent socket identity refused"));
            }
            Ok(metadata)
        })();
        let metadata = match setup {
            Ok(metadata) => metadata,
            Err(error) => {
                if fs::symlink_metadata(path).is_ok_and(|current| {
                    current.file_type().is_socket()
                        && (current.dev(), current.ino()) == (bound.dev(), bound.ino())
                }) {
                    let _ = fs::remove_file(&path).ctx("remove", &path);
                }
                return Err(error);
            }
        };
        Ok(Self {
            listener,
            socket: path.to_owned(),
            socket_identity: (metadata.dev(), metadata.ino()),
            expected_uid,
            _lock: lock,
        })
    }

    /// One bounded accept. The resident event loop remains the sole owner of
    /// its mutable RpcDriver and calls this alongside human entrances.
    pub(crate) fn poll_once(&self, resident: &mut ResidentAgent<'_>) -> io::Result<bool> {
        let Some(mut stream) = self.accept_authenticated()? else {
            return Ok(false);
        };
        // Nothing below writes a reason to the agent beyond its reply; the resident's stderr (the
        // operator's log) keeps every refusal, uncertainty and dropped connection by its reason.
        let frame = match agent_api_wire::read_frame(&mut stream) {
            Ok(frame) => frame,
            Err(error) => {
                eprintln!("spk-host: agent connection closed unread: {error}");
                return Ok(true);
            }
        };
        let request = match Request::parse(&frame) {
            Ok(request) => request,
            Err(error) => {
                eprintln!("spk-host: agent request refused unparsed: {error}");
                return Ok(true);
            }
        };
        let operation_id = match &request {
            Request::Dispatch { operation_id, .. } | Request::Inspect { operation_id, .. } => {
                Some(operation_id.clone())
            }
            Request::Hello { .. } => None,
        };
        let watch = match CallerWatch::start(&stream) {
            Ok(watch) => watch,
            Err(error) => {
                eprintln!("spk-host: agent operation {} not started: caller watch: {error}", operation_id.as_deref().unwrap_or("hello"));
                return Ok(true);
            }
        };
        let result = resident.handle_once(&stream, request, &watch.cancelled);
        let response = match result {
            Ok(reply) => {
                match &reply {
                    Reply::Refused { operation_id, code, .. } => eprintln!("spk-host: agent operation {operation_id} refused: {code}"),
                    Reply::Uncertain { operation_id, phase, .. } => eprintln!("spk-host: agent operation {operation_id} uncertain at {phase}"),
                    _ => {}
                }
                reply
            }
            Err(error) => match operation_id {
                Some(operation_id) => {
                    eprintln!("spk-host: agent operation {operation_id} failed, answered uncertain: {error}");
                    Reply::Uncertain {
                    protocol: PROTOCOL.into(),
                    operation_id,
                    binding_sha256: resident
                        .binding()
                        .and_then(|binding| binding.fingerprint())
                        .unwrap_or_else(|_| "0".repeat(64)),
                    phase: "retained-attempt".into(),
                    }
                }
                None => {
                    eprintln!("spk-host: agent hello failed: {error}");
                    return Ok(true);
                }
            },
        };
        if let Ok(bytes) = serde_json::to_vec(&response) {
            let _ = agent_api_wire::write_frame(&mut stream, &bytes);
        }
        Ok(true)
    }

    /// Shared v2/v3 transport check. The protocol parser runs only after the
    /// protected socket identity and exact controller UID have been checked.
    pub(crate) fn accept_authenticated(&self) -> io::Result<Option<UnixStream>> {
        let (stream, _) = match self.listener.accept() {
            Ok(pair) => pair,
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => return Ok(None),
            Err(error) => return Err(error),
        };
        let metadata = fs::symlink_metadata(&self.socket).ctx("inspect", &self.socket)?;
        if !metadata.file_type().is_socket()
            || metadata.uid() != unsafe { libc::geteuid() }
            || (metadata.dev(), metadata.ino()) != self.socket_identity
            || metadata.permissions().mode() & 0o777
                != if self.expected_uid == unsafe { libc::geteuid() } {
                    0o600
                } else {
                    0o660
                }
        {
            return Err(invalid("agent socket identity drift"));
        }
        exact_acl(&self.socket, self.expected_uid, false, false)?;
        let mut credentials: libc::ucred = unsafe { std::mem::zeroed() };
        let mut size = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        if unsafe {
            libc::getsockopt(
                stream.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_PEERCRED,
                (&mut credentials as *mut libc::ucred).cast(),
                &mut size,
            )
        } != 0
            || size as usize != std::mem::size_of::<libc::ucred>()
            || credentials.uid != self.expected_uid
        {
            return Ok(None);
        }
        Ok(Some(stream))
    }
}

pub(crate) struct ResidentAgent<'a> {
    pub operator: &'a PrivateOperator,
    pub custody: &'a AgentCustody,
    pub journal: &'a Journal,
    pub rpc: &'a mut RpcDriver,
    pub reverse_reserve: &'a mut dyn ReserveSubmit,
    pub signed_api_path: &'a str,
    pub display_name: &'a str,
    pub preferred_handle: &'a str,
    pub attempt_parent: &'a Path,
}

impl ResidentAgent<'_> {
    fn binding(&self) -> io::Result<FixedBinding> {
        let record = self
            .journal
            .read()?
            .ok_or_else(|| invalid("resident app journal absent"))?;
        record.verify_running_instance()?;
        if record.app().to_string() != self.custody.app
            || record.generation().to_string() != self.custody.app_generation
        {
            return Err(invalid("agent app pin differs from running app"));
        }
        let invocation = record
            .invocation_id()
            .ok_or_else(|| invalid("running invocation absent"))?;
        let binding = FixedBinding {
            protocol: "mini-spk-agent-binding-v1".into(),
            app: self.custody.app.clone(),
            app_generation: record.generation().to_string(),
            session: self.custody.session.clone(),
            session_generation: self.custody.session_generation.clone(),
            subject: self.custody.subject.clone(),
            ticket: self.custody.ticket_resource.clone(),
            parent_task: self.custody.parent_task.clone(),
            parent_generation: self.custody.parent_generation.clone(),
            purse_task: self.custody.purse_task.clone(),
            purse_generation: self.custody.purse_generation.clone(),
            signed_api_path: self.signed_api_path.to_owned(),
            host_unit: record.unit().to_owned(),
            host_invocation: invocation.to_owned(),
        };
        binding.validate()?;
        Ok(binding)
    }

    pub(crate) fn handle_once(
        &mut self,
        stream: &UnixStream,
        request: Request,
        cancelled: &Arc<AtomicBool>,
    ) -> io::Result<Reply> {
        match request {
            Request::Hello { .. } => {
                let binding = self.binding()?;
                let fingerprint = binding.fingerprint()?;
                Ok(Reply::Binding {
                    protocol: PROTOCOL.into(),
                    binding: Box::new(binding),
                    binding_sha256: fingerprint,
                })
            }
            Request::Inspect {
                operation_id,
                binding_sha256,
                ..
            } => {
                let fingerprint = if let Some(pin) = binding_sha256 {
                    let saved = read_saved_binding(self.attempt_parent, &operation_id)?;
                    if saved != pin {
                        return Err(invalid(
                            "historical inspection binding differs from attempt",
                        ));
                    }
                    pin
                } else {
                    self.binding()?.fingerprint()?
                };
                let InspectionResult {
                    state,
                    recovered,
                    retention_error,
                } = inspect_result(self.attempt_parent, &operation_id, &fingerprint);
                Ok(Reply::Inspection {
                    protocol: PROTOCOL.into(),
                    operation_id,
                    binding_sha256: fingerprint,
                    state: state.into(),
                    definite_reply_sha256: recovered.as_ref().map(|(sha, _)| sha.clone()),
                    definite_reply_json_hex: recovered.map(|(_, bytes)| hex(&bytes)),
                    retention_error,
                })
            }
            dispatch @ Request::Dispatch { .. } => {
                let fingerprint = self.binding()?.fingerprint()?;
                self.dispatch_once(stream, dispatch, &fingerprint, cancelled)
            }
        }
    }

    fn dispatch_once(
        &mut self,
        stream: &UnixStream,
        request: Request,
        fingerprint: &str,
        cancelled: &Arc<AtomicBool>,
    ) -> io::Result<Reply> {
        if cancelled.load(Ordering::Acquire) {
            return Err(invalid("agent caller cancelled"));
        }
        let Request::Dispatch {
            ref operation_id,
            ref method,
            ref path,
            ref query,
            ref headers,
            ref body_hex,
            ..
        } = request
        else {
            unreachable!()
        };
        let ordered_headers: Vec<_> = headers
            .iter()
            .map(|h| (h.name.clone(), h.value.clone()))
            .collect();
        let body = crate::canonical::unhex(body_hex).ok_or_else(|| invalid("agent body hex"))?;
        let path_and_query = if query.is_empty() {
            path.clone()
        } else {
            format!("{path}?{query}")
        };
        let http = HttpProjection {
            method,
            path_and_query: &path_and_query,
            ordered_headers: &ordered_headers,
            body: &body,
            route: Route::Api {
                signed_path: self.signed_api_path,
            },
        };
        let (app_path, _) = app_route_path(&http)?;
        private_dir(self.attempt_parent)?;
        let client_dir = self
            .attempt_parent
            .join(format!("agent-client-op-{operation_id}"));
        std::fs::DirBuilder::new().mode(0o700).create(&client_dir)?;
        write_new(
            &client_dir,
            "received.json",
            &serde_json::to_vec(&serde_json::json!({"protocol":PROTOCOL,
                "operationId":operation_id,"bindingSha256":fingerprint}))?,
        )?;
        // The controller allocates and durably records this forward operation
        // before calling the resident. The same ID is Mini's HTTP operation ID;
        // reserveOperationId is a separate controller allocation.
        let allocated = operation_id.clone();
        write_new(
            &client_dir,
            "source-operation.json",
            &serde_json::to_vec(&serde_json::json!({"sourceOperationId":allocated}))?,
        )?;
        let source_request = match &request {
            Request::Dispatch {
                protocol,
                method,
                path,
                query,
                headers,
                body_hex,
                ..
            } => Request::Dispatch {
                protocol: protocol.clone(),
                operation_id: allocated.clone(),
                method: method.clone(),
                path: path.clone(),
                query: query.clone(),
                headers: headers.clone(),
                body_hex: body_hex.clone(),
            },
            _ => unreachable!(),
        };
        let committed = authorize_once(
            self.operator,
            self.custody,
            &source_request,
            &app_path,
            &self
                .attempt_parent
                .join(format!("agent-dispatch-op-{allocated}")),
            self.reverse_reserve,
            cancelled,
        )?;
        write_new(
            &client_dir,
            "submit-requested.json",
            b"event21-op46-submitted",
        )?;
        let matched = match_committed(
            &committed.inspection,
            &source_request,
            &app_path,
            self.custody,
            &self.binding()?,
            &committed.reserve,
        )?;
        let physical =
            physical_web_input(&matched, &http, self.display_name, self.preferred_handle, "")?;
        // A hard caller disconnect is a before-delivery fence. A soft model
        // timeout leaves the controller connection open and retains authority.
        let mut peek = [0u8; 1];
        let count = unsafe {
            libc::recv(
                stream.as_raw_fd(),
                peek.as_mut_ptr().cast(),
                peek.len(),
                libc::MSG_PEEK | libc::MSG_DONTWAIT,
            )
        };
        if cancelled.load(Ordering::Acquire) || count == 0 {
            return Err(invalid("agent caller disconnected before delivery"));
        } else if count > 0 {
            return Err(invalid("agent caller sent trailing request bytes"));
        } else {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::WouldBlock {
                return Err(error);
            }
        }
        let record = self
            .journal
            .read()?
            .ok_or_else(|| invalid("app journal absent"))?;
        record.verify_running_instance()?;
        let identity = DispatchIdentity {
            permit_sha256: hex(&Sha256::digest(&committed.permit)),
            request_digest: matched.physical_request_digest.clone(),
            app: matched.app,
            app_generation: matched.app_generation,
            invocation_id: record
                .invocation_id()
                .ok_or_else(|| invalid("invocation absent"))?
                .to_owned(),
            operation_id: allocated,
            session_resource: matched.session_resource.clone(),
            session_generation: matched.session_generation.clone(),
            dispatch_transaction: matched.dispatch_transaction.clone(),
            dispatch_event: matched.dispatch_event.clone(),
        };
        // Controller custody must durably mark its retained, confirmed reserve
        // as sending before this resident can queue a byte on fd3. A lost ACK
        // is uncertainty: this caller receives no delivery and never retries.
        self.reverse_reserve.mark_send_once(
            &committed.canonical_http_sha256,
            &identity.dispatch_transaction,
            &identity.dispatch_event,
            &identity.permit_sha256,
            cancelled,
        )?;
        let prequeue = self.rpc.prepare_cancellable(identity.clone())?;
        self.journal
            .request_dispatch(identity.clone(), &committed.permit)?;
        let prequeue =
            write_agent_delivery_marker(prequeue, self.journal, &identity, &client_dir, || {
                record.verify_running_instance()
            })?;
        let (web_reply, success_fence) = match prequeue.dispatch(
            physical.binding,
            physical.request,
            MAX_APP_RESPONSE,
            Duration::from_secs(30),
            Arc::clone(cancelled),
        ) {
            Ok(reply) => reply,
            Err(failure) => {
                let (error, fence) = failure.into_parts();
                if let Some(fence) = fence {
                    // Only the typed worker ACK can release this RPC slot.
                    // The per-operation tombstone remains uncertain and
                    // terminal; the app-side effect is never inferred absent.
                    let _ = self
                        .journal
                        .finish_dispatch_uncertain_released(&identity, fence);
                } else {
                    let _ = self.journal.finish_dispatch(&identity, false);
                }
                return Err(error);
            }
        };
        let outcome: io::Result<Reply> = (|| {
            let bytes = http_response::serialize(&web_reply, method == "HEAD")?;
            let reply = http_reply(&bytes, operation_id, fingerprint)?;
            // Retain the exact controller-facing result before declaring
            // the app send definite. A lost socket reply is terminal and
            // inspect returns definite; it never authorizes redelivery.
            let reply_bytes = serde_json::to_vec(&reply)?;
            write_new(&client_dir, "definite.json", &reply_bytes)?;
            write_new(
                &client_dir,
                "definite.sha256",
                hex(&Sha256::digest(&reply_bytes)).as_bytes(),
            )?;
            self.journal.finish_dispatch(&identity, true)?;
            committed.clear_committed_submit_marker()?;
            Ok(reply)
        })();
        match outcome {
            Ok(reply) => Ok(reply),
            Err(error) => {
                // The worker has completed this command, but a host-side
                // response or retention failure cannot certify a controller
                // result. Release only the shared slot; keep this operation
                // uncertain and nonreplayable.
                let _ = self
                    .journal
                    .finish_dispatch_uncertain_released(&identity, success_fence);
                Err(error)
            }
        }
    }
}

/// This exact prequeue branch is shared with the hostd A/B regression fixture.
/// A failed durable marker or liveness check can release the shared slot only
/// while the linear RPC guard still proves this command was never enqueued.
pub(crate) fn write_agent_delivery_marker<'a>(
    prequeue: PrequeueGuard<'a>,
    journal: &Journal,
    identity: &DispatchIdentity,
    client_dir: &Path,
    verify_running: impl FnOnce() -> io::Result<()>,
) -> io::Result<PrequeueGuard<'a>> {
    let outcome = (|| {
        write_new(
            client_dir,
            "delivery-requested.json",
            b"fd3-delivery-requested",
        )?;
        verify_running()
    })();
    match outcome {
        Ok(()) => Ok(prequeue),
        Err(error) => {
            let fence = prequeue.abort_no_enqueue();
            let _ = journal.finish_dispatch_uncertain_released(identity, fence);
            Err(error)
        }
    }
}

fn inspect_state(attempt_parent: &Path, operation_id: &str) -> &'static str {
    let client = attempt_parent.join(format!("agent-client-op-{operation_id}"));
    let native = attempt_parent.join(format!("agent-dispatch-op-{operation_id}"));
    if client.join("definite.json").exists() {
        "definite"
    } else if client.join("delivery-requested.json").exists() {
        "delivery-requested"
    } else if client.join("submit-requested.json").exists()
        || native.join("submit-requested.json").exists()
        || attempt_parent
            .join("native-agent-dispatch-active.json")
            .exists()
        || native.exists()
    {
        // Native reserve/submit may be uncertain even when the caller-side
        // marker was never reached. The original operation must be audited.
        "uncertain"
    } else if client.exists() {
        "received"
    } else {
        "not-seen"
    }
}

struct InspectionResult {
    state: &'static str,
    recovered: Option<(String, Vec<u8>)>,
    retention_error: Option<String>,
}

fn inspect_result(
    attempt_parent: &Path,
    operation_id: &str,
    binding_sha256: &str,
) -> InspectionResult {
    let state = inspect_state(attempt_parent, operation_id);
    if state != "definite" {
        return InspectionResult {
            state,
            recovered: None,
            retention_error: None,
        };
    }
    match recover_definite(attempt_parent, operation_id, binding_sha256).unwrap_or(None) {
        Some(recovered) => InspectionResult {
            state: "definite",
            recovered: Some(recovered),
            retention_error: None,
        },
        None => InspectionResult {
            state: "uncertain",
            recovered: None,
            retention_error: Some("definite-reply-unverified".into()),
        },
    }
}

fn read_saved_binding(attempt_parent: &Path, operation_id: &str) -> io::Result<String> {
    let client = attempt_parent.join(format!("agent-client-op-{operation_id}"));
    private_dir(&client)?;
    let bytes = read_private_recovery(&client.join("received.json"), 1024)?;
    let saved: Value = serde_json::from_slice(&bytes)?;
    if saved.as_object().is_none_or(|fields| fields.len() != 3)
        || string(&saved, "protocol")? != PROTOCOL
        || decimal(&saved, "operationId")? != operation_id
    {
        return Err(invalid("historical inspection attempt anchor drift"));
    }
    let pin = string(&saved, "bindingSha256")?;
    if !crate::canonical::hex64(&pin)
    {
        return Err(invalid("historical inspection binding digest refused"));
    }
    Ok(pin.to_owned())
}

pub(crate) fn read_private_recovery(path: &Path, max: usize) -> io::Result<Vec<u8>> {
    crate::private_file::read(path, max as u64, "private definite reply identity or size")
}

fn recover_definite(
    attempt_parent: &Path,
    operation_id: &str,
    binding_sha256: &str,
) -> io::Result<Option<(String, Vec<u8>)>> {
    let client = attempt_parent.join(format!("agent-client-op-{operation_id}"));
    if private_dir(&client).is_err() {
        return Ok(None);
    }
    let bytes =
        match read_private_recovery(&client.join("definite.json"), agent_api_wire::MAX_FRAME) {
            Ok(bytes) => bytes,
            Err(_) => return Ok(None),
        };
    let stored_sha = match read_private_recovery(&client.join("definite.sha256"), 64) {
        Ok(bytes) => bytes,
        Err(_) => return Ok(None),
    };
    let stored_sha =
        std::str::from_utf8(&stored_sha).map_err(|_| invalid("definite reply digest encoding"))?;
    if stored_sha != hex(&Sha256::digest(&bytes)) {
        return Ok(None);
    }
    let parsed: Reply = serde_json::from_slice(&bytes)?;
    let Reply::Http {
        protocol,
        operation_id: saved_operation,
        binding_sha256: saved_binding,
        ..
    } = parsed
    else {
        return Ok(None);
    };
    if protocol != PROTOCOL || saved_operation != operation_id || saved_binding != binding_sha256 {
        return Ok(None);
    }
    Ok(Some((stored_sha.to_owned(), bytes)))
}

fn match_committed(
    inspection: &Value,
    request: &Request,
    app_path: &str,
    custody: &AgentCustody,
    binding: &FixedBinding,
    reserve: &RetainedReserve,
) -> io::Result<MatchedInspection> {
    let Request::Dispatch {
        operation_id,
        method,
        query,
        headers,
        body_hex,
        ..
    } = request
    else {
        return Err(invalid("agent dispatch required"));
    };
    if string(inspection, "type")? != "application-agent-dispatch-committed-inspection-v2" {
        return Err(invalid("agent committed inspection kind"));
    }
    let app = inspection
        .get("app")
        .ok_or_else(|| invalid("agent app absent"))?;
    let session = inspection
        .get("session")
        .ok_or_else(|| invalid("agent session absent"))?;
    let origin = session
        .get("origin")
        .ok_or_else(|| invalid("agent origin absent"))?;
    let parent = inspection
        .get("parent")
        .ok_or_else(|| invalid("agent parent absent"))?;
    let purse = inspection
        .get("purse")
        .ok_or_else(|| invalid("agent purse absent"))?;
    let original = purse
        .get("originalReceipt")
        .ok_or_else(|| invalid("original reserve receipt absent"))?;
    let source_request = inspection
        .get("request")
        .ok_or_else(|| invalid("agent request absent"))?;
    let receipt = inspection
        .get("receipt")
        .ok_or_else(|| invalid("agent receipt absent"))?;
    if decimal(app, "resource")? != custody.app
        || string(app, "generation")? != binding.app_generation
        || binding.parent_task != custody.parent_task
        || binding.parent_generation != custody.parent_generation
        || binding.purse_task != custody.purse_task
        || binding.purse_generation != custody.purse_generation
        || !minidregg_signed_api_path::is_under(&binding.signed_api_path, app_path)
        || decimal(session, "resource")? != custody.session
        || string(session, "generation")? != binding.session_generation
        || decimal(session, "subject")? != custody.subject
        || string(session, "kind")? != "api"
        || string(origin, "type")? != "agent"
        || decimal(origin, "task")? != custody.parent_task
        || string(origin, "generation")? != custody.parent_generation
        || decimal(parent, "task")? != custody.parent_task
        || string(parent, "generation")? != custody.parent_generation
        || decimal(purse, "task")? != custody.purse_task
        || string(purse, "generation")? != custody.purse_generation
        || decimal(purse, "payerSubject")? != custody.payer_subject
        || string(purse, "reserveAmount")? != custody.reserve_amount
        || string(purse, "maximumCharge")? != custody.maximum_charge
        || decimal(purse, "reserveOperationId")? != reserve.operation_id
        || decimal(purse, "reserveIndex")? != reserve.reserve_index
        || decimal(original, "transactionId")? != reserve.transaction_id
        || decimal(original, "eventId")? != reserve.event_id
        || decimal(original, "acceptedCount")? != reserve.accepted_count
        || decimal(original, "worldRoot")? != reserve.world_root
        || decimal(inspection, "ticketResource")? != custody.ticket_resource
        || decimal(source_request, "operationId")? != operation_id
        || string(source_request, "methodHex")? != hex(method.as_bytes())
        || string(source_request, "pathHex")? != hex(app_path.as_bytes())
        || string(source_request, "queryHex")? != hex(query.as_bytes())
        || string(source_request, "bodyHex")? != body_hex
    {
        return Err(invalid(
            "event21 committed coordinate differs from fixed API request",
        ));
    }
    let source_headers = source_request
        .get("headers")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("agent source headers absent"))?;
    if source_headers.len() != headers.len() {
        return Err(invalid("agent ordered header count drift"));
    }
    for (source, given) in source_headers.iter().zip(headers) {
        if source.get("generated").and_then(Value::as_bool) != Some(false)
            || string(source, "nameHex")? != hex(given.name.as_bytes())
            || string(source, "valueHex")? != hex(given.value.as_bytes())
        {
            return Err(invalid("agent ordered header drift"));
        }
    }
    if decimal(receipt, "transactionId")? != decimal(inspection, "dispatchTransaction")?
        || decimal(receipt, "eventId")? != decimal(inspection, "dispatchEvent")?
    {
        return Err(invalid("event21 committed receipt drift"));
    }
    let identity = inspection
        .get("identity")
        .ok_or_else(|| invalid("agent identity absent"))?;
    let effective_bits = inspection
        .get("effectiveBits")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("agent effective bits absent"))?
        .iter()
        .map(|bit| bit.as_bool().ok_or_else(|| invalid("agent effective bit")))
        .collect::<io::Result<Vec<_>>>()?;
    if effective_bits.len() > 128 {
        return Err(invalid("agent permission width"));
    }
    Ok(MatchedInspection {
        app: custody
            .app
            .parse()
            .map_err(|_| invalid("agent app range"))?,
        app_generation: binding
            .app_generation
            .parse()
            .map_err(|_| invalid("agent generation range"))?,
        session_resource: custody.session.clone(),
        session_generation: binding.session_generation.clone(),
        subject: custody.subject.clone(),
        operation_id: operation_id.clone(),
        physical_request_digest: decimal(inspection, "physicalRequestDigest")?.to_owned(),
        dispatch_transaction: decimal(inspection, "dispatchTransaction")?.to_owned(),
        dispatch_event: decimal(inspection, "dispatchEvent")?.to_owned(),
        session_fingerprint: digest_nat(decimal(inspection, "sessionFingerprint")?)?,
        principal: unhex32(string(identity, "principalHex")?)?,
        before_world_root: decimal(inspection, "currentWorldRoot")?.to_owned(),
        after_world_root: decimal(receipt, "worldRoot")?.to_owned(),
        accepted_count: decimal(receipt, "acceptedCount")?.to_owned(),
        effective_bits,
        app_path_and_query: if query.is_empty() {
            app_path.to_owned()
        } else {
            format!("{app_path}?{query}")
        },
        method: method.clone(),
    })
}

fn http_reply(bytes: &[u8], operation_id: &str, binding_sha256: &str) -> io::Result<Reply> {
    let boundary = bytes
        .windows(4)
        .position(|window| window == b"\r\n\r\n")
        .ok_or_else(|| invalid("app response header boundary"))?;
    let head = std::str::from_utf8(&bytes[..boundary])
        .map_err(|_| invalid("app response header UTF-8"))?;
    let mut lines = head.split("\r\n");
    let status = lines
        .next()
        .and_then(|line| line.split_whitespace().nth(1))
        .and_then(|value| value.parse::<u16>().ok())
        .ok_or_else(|| invalid("app response status"))?;
    let mut headers = Vec::new();
    for line in lines {
        let (name, value) = line
            .split_once(": ")
            .ok_or_else(|| invalid("app response header"))?;
        headers.push(OrdinaryHeader {
            name: name.to_ascii_lowercase(),
            value: value.to_owned(),
        });
    }
    let body = &bytes[boundary + 4..];
    let response = Reply::Http {
        protocol: PROTOCOL.into(),
        operation_id: operation_id.into(),
        binding_sha256: binding_sha256.into(),
        status,
        headers,
        body_hex: hex(body),
    };
    if serde_json::to_vec(&response)?.len() > agent_api_wire::MAX_FRAME {
        return Err(invalid("app API response frame exceeds controller bound"));
    }
    Ok(response)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::sync::atomic::AtomicUsize;

    static NEXT_LISTENER: AtomicUsize = AtomicUsize::new(1);

    #[test]
    fn posix_acl_xattr_lists_as_getfacl_does_and_refuses_other_encodings() {
        let mut image = 2u32.to_le_bytes().to_vec();
        for (tag, perm, id) in [(1u16, 6u16, u32::MAX), (2, 6, 1000), (4, 0, u32::MAX), (0x10, 6, u32::MAX), (0x20, 0, u32::MAX)] {
            image.extend_from_slice(&tag.to_le_bytes());
            image.extend_from_slice(&perm.to_le_bytes());
            image.extend_from_slice(&id.to_le_bytes());
        }
        assert_eq!(
            parse_posix_acl(&image).unwrap(),
            ["user::rw-", "user:1000:rw-", "group::---", "mask::rw-", "other::---"]
        );
        assert!(parse_posix_acl(&image[..image.len() - 1]).is_err());
        assert!(parse_posix_acl(&[1, 0, 0, 0]).is_err());
        let mut unknown = 2u32.to_le_bytes().to_vec();
        unknown.extend_from_slice(&[0x40, 0, 6, 0, 0, 0, 0, 0]);
        assert!(parse_posix_acl(&unknown).is_err());
    }

    #[test]
    fn a_file_without_extended_acl_lists_its_mode_bits() {
        let path = std::env::temp_dir().join(format!(
            "mini-acl-mode-{}-{}",
            std::process::id(),
            NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)
        ));
        fs::write(&path, b"x").unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o640)).unwrap();
        assert_eq!(acl_entries(&path).unwrap(), ["user::rw-", "group::r--", "other::---"]);
        fs::remove_file(&path).unwrap();
    }

    #[test]
    fn inspect_observes_native_uncertainty_before_client_marker() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-inspect-{}-{}",
            std::process::id(),
            NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&directory).unwrap();
        assert_eq!(inspect_state(&directory, "17"), "not-seen");
        let client = directory.join("agent-client-op-17");
        let native = directory.join("agent-dispatch-op-17");
        fs::create_dir(&client).unwrap();
        assert_eq!(inspect_state(&directory, "17"), "received");
        fs::create_dir(&native).unwrap();
        fs::write(native.join("submit-requested.json"), b"op46 attempted").unwrap();
        assert_eq!(inspect_state(&directory, "17"), "uncertain");
        fs::write(client.join("delivery-requested.json"), b"fd3 attempted").unwrap();
        assert_eq!(inspect_state(&directory, "17"), "delivery-requested");
        fs::write(client.join("definite.json"), b"exact reply").unwrap();
        assert_eq!(inspect_state(&directory, "17"), "definite");
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn definite_recovery_requires_exact_saved_reply_digest_operation_and_binding() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-recovery-{}-{}",
            std::process::id(),
            NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let client = directory.join("agent-client-op-17");
        fs::DirBuilder::new().mode(0o700).create(&client).unwrap();
        write_new(
            &client,
            "received.json",
            &serde_json::to_vec(&json!({"protocol":PROTOCOL,"operationId":"17",
                "bindingSha256":"a".repeat(64)}))
            .unwrap(),
        )
        .unwrap();
        assert_eq!(
            read_saved_binding(&directory, "17").unwrap(),
            "a".repeat(64)
        );
        let reply = Reply::Http {
            protocol: PROTOCOL.into(),
            operation_id: "17".into(),
            binding_sha256: "a".repeat(64),
            status: 200,
            headers: vec![OrdinaryHeader {
                name: "content-type".into(),
                value: "application/x-git-upload-pack-result".into(),
            }],
            body_hex: "00ff".into(),
        };
        let bytes = serde_json::to_vec(&reply).unwrap();
        write_new(&client, "definite.json", &bytes).unwrap();
        assert_eq!(inspect_state(&directory, "17"), "definite");
        let incomplete = inspect_result(&directory, "17", &"a".repeat(64));
        assert_eq!(incomplete.state, "uncertain");
        assert!(incomplete.recovered.is_none());
        assert_eq!(
            incomplete.retention_error.as_deref(),
            Some("definite-reply-unverified")
        );
        assert!(recover_definite(&directory, "17", &"a".repeat(64))
            .unwrap()
            .is_none()); // old or interrupted marker: terminal, no result
        write_new(
            &client,
            "definite.sha256",
            hex(&Sha256::digest(&bytes)).as_bytes(),
        )
        .unwrap();
        assert_eq!(
            recover_definite(&directory, "17", &"a".repeat(64))
                .unwrap()
                .unwrap()
                .1,
            bytes
        );
        assert_eq!(
            inspect_result(&directory, "17", &"a".repeat(64)).state,
            "definite"
        );
        assert!(recover_definite(&directory, "18", &"a".repeat(64))
            .unwrap()
            .is_none());
        assert!(recover_definite(&directory, "17", &"b".repeat(64))
            .unwrap()
            .is_none());
        let old_anchor = fs::read(client.join("received.json")).unwrap();
        for (field, replacement) in [
            ("operationId", "18".to_owned()),
            ("bindingSha256", "b".repeat(64)),
        ] {
            let mut altered: Value = serde_json::from_slice(&old_anchor).unwrap();
            altered[field] = Value::String(replacement);
            fs::write(
                client.join("received.json"),
                serde_json::to_vec(&altered).unwrap(),
            )
            .unwrap();
            if field == "operationId" {
                assert!(read_saved_binding(&directory, "17").is_err());
            } else {
                assert_ne!(
                    read_saved_binding(&directory, "17").unwrap(),
                    "a".repeat(64)
                );
            }
        }
        fs::write(client.join("received.json"), old_anchor).unwrap();
        for (field, replacement) in [
            ("operation_id", "18".to_owned()),
            ("binding_sha256", "b".repeat(64)),
        ] {
            let mut altered: Value = serde_json::from_slice(&bytes).unwrap();
            altered[field] = Value::String(replacement);
            let altered = serde_json::to_vec(&altered).unwrap();
            fs::write(client.join("definite.json"), &altered).unwrap();
            fs::write(
                client.join("definite.sha256"),
                hex(&Sha256::digest(&altered)),
            )
            .unwrap();
            assert!(recover_definite(&directory, "17", &"a".repeat(64))
                .unwrap()
                .is_none());
        }
        fs::write(client.join("definite.json"), b"{truncated").unwrap();
        assert_eq!(
            inspect_result(&directory, "17", &"a".repeat(64)).state,
            "uncertain"
        );
        assert!(recover_definite(&directory, "17", &"a".repeat(64))
            .unwrap()
            .is_none());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn listener_drops_only_the_socket_inode_it_bound() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-listener-{}-{}",
            std::process::id(),
            NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("agent.sock");
        let listener = AgentApiListener::bind(&socket, unsafe { libc::geteuid() }).unwrap();
        assert!(socket.exists());
        drop(listener);
        assert!(!socket.exists());
        fs::remove_file(socket_lock_path(&socket).unwrap()).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn preflight_refuses_dangling_socket_symlink_before_one_shot_start() {
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-socket-link-{}-{}",
            std::process::id(),
            NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let socket = directory.join("agent.sock");
        std::os::unix::fs::symlink(directory.join("absent"), &socket).unwrap();
        assert!(AgentApiListener::preflight_parent(&socket, unsafe { libc::geteuid() }).is_err());
        fs::remove_file(socket).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn distinct_controller_uid_gets_exact_traverse_and_socket_acl() {
        // A distinct controller must traverse every ancestor, so this fixture cannot sit under
        // TMPDIR, whose modes are the runner's (dregg-build's /build/t is 0700 and is refused,
        // rightly). It sits directly under /tmp, the root-owned sticky directory the preflight
        // admits as a shared ancestor, and also proves the refusal under a private ancestor.
        let id = format!(
            "{}-{}",
            std::process::id(),
            NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)
        );
        let controller_uid = unsafe { libc::geteuid() } + 10_000;
        let private = Path::new("/tmp").join(format!("mini-agent-acl-private-{id}"));
        fs::create_dir(&private).unwrap();
        fs::set_permissions(&private, fs::Permissions::from_mode(0o700)).unwrap();
        let hidden = private.join("agent");
        fs::create_dir(&hidden).unwrap();
        fs::set_permissions(&hidden, fs::Permissions::from_mode(0o700)).unwrap();
        let refused = AgentApiListener::preflight_parent(&hidden.join("agent.sock"), controller_uid)
            .unwrap_err();
        assert!(
            refused.to_string().contains("controller cannot traverse agent socket ancestor"),
            "{refused}"
        );
        fs::remove_dir(&hidden).unwrap();
        fs::remove_dir(&private).unwrap();
        let directory = Path::new("/tmp").join(format!("mini-agent-acl-{id}"));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        let socket = directory.join("agent.sock");
        AgentApiListener::preflight_parent(&socket, controller_uid).unwrap();
        let listener = AgentApiListener::bind(&socket, controller_uid).unwrap();
        assert_eq!(
            fs::metadata(&directory).unwrap().permissions().mode() & 0o777,
            0o710
        );
        assert_eq!(
            fs::metadata(&socket).unwrap().permissions().mode() & 0o777,
            0o660
        );
        exact_acl(&directory, controller_uid, true, false).unwrap();
        exact_acl(&socket, controller_uid, false, false).unwrap();
        drop(listener);
        fs::remove_file(socket_lock_path(&socket).unwrap()).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn dead_exact_agent_socket_rebinds_without_weakening_live_listener_custody() {
        let directory = Path::new("/tmp").join(format!("mini-agent-rebind-{}-{}",
            std::process::id(), NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)));
        fs::DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let path = directory.join("api.sock");
        let uid = unsafe { libc::geteuid() } + 10_000;
        protected_agent_socket_parent(&directory, uid, true).unwrap();
        // Model an older resident killed without Drop: its exact ACL socket
        // remains, while its kernel listener no longer exists.
        let old = UnixListener::bind(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        exact_acl(&path, uid, false, true).unwrap();
        assert!(AgentApiListener::preflight_parent(&path, uid).is_err());
        assert!(reclaim_socket(&path, uid).is_err());
        drop(old);
        let before = fs::symlink_metadata(&path).unwrap();
        let extra = format!("u:{}:rw-", uid + 1);
        assert!(Command::new("/usr/bin/setfacl").args(["-m", &extra]).arg(&path).status().unwrap().success());
        assert!(reclaim_socket(&path, uid).is_err());
        assert_eq!(fs::symlink_metadata(&path).unwrap().ino(), before.ino());
        let extra = format!("u:{}", uid + 1);
        assert!(Command::new("/usr/bin/setfacl").args(["-x", &extra]).arg(&path).status().unwrap().success());
        AgentApiListener::preflight_parent(&path, uid).unwrap();
        assert_eq!(fs::symlink_metadata(&path).unwrap().ino(), before.ino());
        let listener = AgentApiListener::bind(&path, uid).unwrap();
        exact_acl(&path, uid, false, false).unwrap();
        assert!(AgentApiListener::preflight_parent(&path, uid).is_err());
        assert!(AgentApiListener::bind(&path, uid).is_err());
        assert!(reclaim_socket(&path, uid).is_err());
        drop(listener);
        assert!(!path.exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn explicit_agent_socket_reclaim_preserves_wrong_objects_and_records_exact_inode() {
        let directory = Path::new("/tmp").join(format!("mini-agent-reclaim-{}-{}",
            std::process::id(), NEXT_LISTENER.fetch_add(1, Ordering::SeqCst)));
        fs::DirBuilder::new().mode(0o700).create(&directory).unwrap();
        let path = directory.join("api.sock");
        let uid = unsafe { libc::geteuid() };
        fs::write(&path, b"not a socket").unwrap();
        assert!(reclaim_socket(&path, uid).is_err());
        assert_eq!(fs::read(&path).unwrap(), b"not a socket");
        fs::remove_file(&path).unwrap();
        std::os::unix::fs::symlink(directory.join("missing"), &path).unwrap();
        assert!(reclaim_socket(&path, uid).is_err());
        assert!(fs::symlink_metadata(&path).unwrap().file_type().is_symlink());
        fs::remove_file(&path).unwrap();
        let listener = UnixListener::bind(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o666)).unwrap();
        drop(listener);
        assert!(reclaim_socket(&path, uid).is_err());
        assert!(path.exists());
        fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).unwrap();
        let old = fs::symlink_metadata(&path).unwrap();
        let result = reclaim_socket(&path, uid).unwrap();
        assert_eq!(result["previous"]["inode"], old.ino());
        assert_eq!(result["previous"]["device"], old.dev());
        assert_eq!(result["removed"], true);
        assert_eq!(result["nativeOperationSubmitted"], false);
        assert!(!path.exists());
        assert_eq!(reclaim_socket(&path, uid).unwrap()["removed"], false);
        let lock = socket_lock_path(&path).unwrap();
        fs::remove_file(&lock).unwrap();
        std::os::unix::fs::symlink(directory.join("missing"), &lock).unwrap();
        assert!(reclaim_socket(&path, uid).is_err());
        fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn binary_git_reply_keeps_status_headers_and_body() {
        let bytes = b"HTTP/1.1 200 OK\r\nContent-Type: application/x-git-upload-pack-result\r\nContent-Length: 3\r\n\r\n\0\xff\x01";
        let Reply::Http {
            status,
            headers,
            body_hex,
            ..
        } = http_reply(bytes, "9", &"a".repeat(64)).unwrap()
        else {
            panic!("HTTP reply required")
        };
        assert_eq!(status, 200);
        assert_eq!(headers[0].name, "content-type");
        assert_eq!(body_hex, "00ff01");
    }

    #[test]
    fn event21_projection_requires_original_reserve_and_exact_request() {
        let request = Request::parse(br#"{"type":"dispatch","protocol":"mini-spk-agent-api-v1","operation_id":"7","method":"GET","path":"info/refs","query":"service=git-upload-pack","headers":[{"name":"accept","value":"application/x-git-upload-pack-advertisement"}],"body_hex":""}"#).unwrap();
        let custody: AgentCustody = serde_json::from_value(json!({
            "protocol":"mini-spk-agent-dispatch-custody-v2", "app":"6100", "appGeneration":"2",
            "session":"6209","sessionGeneration":"3","subject":"8","ticketResource":"6408",
            "parentTask":"6500","parentGeneration":"4","purseTask":"6600","purseGeneration":"5",
            "issueIndex":"1","packageManifest":"6101","snapshotManifest":"6102",
            "sessionObserve":"11","manifestObserve":"12","enrollmentObserve":"13",
            "parentCapability":"14","parentObserve":"15","purseCapability":"16",
            "purseObserve":"17","payerSubject":"8","reserveAmount":"20","maximumCharge":"10",
            "appSigners":[],"payerPins":[]
        }))
        .unwrap();
        let binding = FixedBinding {
            protocol: "mini-spk-agent-binding-v1".into(),
            app: "6100".into(),
            app_generation: "2".into(),
            session: "6209".into(),
            session_generation: "3".into(),
            subject: "8".into(),
            ticket: "6408".into(),
            parent_task: "6500".into(),
            parent_generation: "4".into(),
            purse_task: "6600".into(),
            purse_generation: "5".into(),
            signed_api_path: "/repo.git/".into(),
            host_unit: "unit".into(),
            host_invocation: "a".repeat(32),
        };
        let reserve = RetainedReserve {
            attempt_id: "41".into(),
            operation_id: "9".into(),
            fixed_request_hex: "00".into(),
            context_hex: "00".into(),
            reserve_index: "4".into(),
            transaction_id: "100".into(),
            event_id: "101".into(),
            accepted_count: "5".into(),
            world_root: "200".into(),
        };
        let mut inspection = json!({
            "type":"application-agent-dispatch-committed-inspection-v2",
            "app":{"resource":"6100","generation":"2"},
            "session":{"resource":"6209","generation":"3","subject":"8","kind":"api",
                "origin":{"type":"agent","task":"6500","generation":"4"}},
            "parent":{"task":"6500","generation":"4"},
            "purse":{"task":"6600","generation":"5","payerSubject":"8",
                "reserveAmount":"20","maximumCharge":"10","reserveOperationId":"9",
                "reserveIndex":"4","originalReceipt":{"transactionId":"100","eventId":"101",
                    "acceptedCount":"5","worldRoot":"200"}},
            "ticketResource":"6408",
            "request":{"operationId":"7","methodHex":hex(b"GET"),
                "pathHex":hex(b"repo.git/info/refs"),"queryHex":hex(b"service=git-upload-pack"),
                "bodyHex":"","headers":[{"nameHex":hex(b"accept"),
                    "valueHex":hex(b"application/x-git-upload-pack-advertisement"),"generated":false}]},
            "receipt":{"transactionId":"300","eventId":"301","acceptedCount":"6","worldRoot":"400"},
            "dispatchTransaction":"300","dispatchEvent":"301","identity":{"principalHex":"a".repeat(64)},
            "effectiveBits":[true,false],"physicalRequestDigest":"42","sessionFingerprint":"43",
            "currentWorldRoot":"350"
        });
        assert!(match_committed(
            &inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &binding,
            &reserve
        )
        .is_ok());
        let mut root_binding = binding.clone();
        root_binding.signed_api_path = "/".into();
        let mut root_inspection = inspection.clone();
        root_inspection["request"]["pathHex"] = json!(hex(b"info/refs"));
        assert!(match_committed(
            &root_inspection,
            &request,
            "info/refs",
            &custody,
            &root_binding,
            &reserve
        )
        .is_ok());
        assert!(match_committed(
            &root_inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &root_binding,
            &reserve
        )
        .is_err());
        let mut wrong_binding = binding.clone();
        wrong_binding.parent_task = binding.purse_task.clone();
        assert!(match_committed(
            &inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &wrong_binding,
            &reserve
        )
        .is_err());
        let mut wrong_binding = binding.clone();
        wrong_binding.purse_task = binding.parent_task.clone();
        assert!(match_committed(
            &inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &wrong_binding,
            &reserve
        )
        .is_err());
        let mut wrong_binding = binding.clone();
        wrong_binding.signed_api_path = "/other.git/".into();
        assert!(match_committed(
            &inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &wrong_binding,
            &reserve
        )
        .is_err());
        inspection["purse"]["originalReceipt"]["eventId"] = json!("102");
        assert!(match_committed(
            &inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &binding,
            &reserve
        )
        .is_err());
        inspection["purse"]["originalReceipt"]["eventId"] = json!("101");
        inspection["request"]["pathHex"] = json!(hex(b"other.git/info/refs"));
        assert!(match_committed(
            &inspection,
            &request,
            "repo.git/info/refs",
            &custody,
            &binding,
            &reserve
        )
        .is_err());
    }
}
