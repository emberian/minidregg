//! Public ingress for one existing private Host. No Host process, admission
//! rules, retries or operator requests are introduced here. A stopped relay
//! severs public access while private lifecycle operations remain available.
use crate::transport;
use std::fs;
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

static SIGNAL_STOP: AtomicBool = AtomicBool::new(false);
extern "C" fn stop_signal(_: libc::c_int) {
    SIGNAL_STOP.store(true, Ordering::Relaxed);
}

struct Signals(libc::sigaction, libc::sigaction);
impl Signals {
    fn install() -> Result<Self, String> {
        // Installation happens before any worker exists. The handler only
        // stores to an atomic; all cleanup happens on ordinary Rust threads.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = stop_signal as *const () as usize;
            libc::sigemptyset(&mut action.sa_mask);
            let mut term = std::mem::zeroed();
            let mut interrupt = std::mem::zeroed();
            if libc::sigaction(libc::SIGTERM, &action, &mut term) != 0 {
                return Err(format!(
                    "cannot install relay stop handler: {}",
                    io::Error::last_os_error()
                ));
            }
            if libc::sigaction(libc::SIGINT, &action, &mut interrupt) != 0 {
                libc::sigaction(libc::SIGTERM, &term, std::ptr::null_mut());
                return Err(format!(
                    "cannot install relay interrupt handler: {}",
                    io::Error::last_os_error()
                ));
            }
            Ok(Self(term, interrupt))
        }
    }
}
impl Drop for Signals {
    fn drop(&mut self) {
        unsafe {
            libc::sigaction(libc::SIGTERM, &self.0, std::ptr::null_mut());
            libc::sigaction(libc::SIGINT, &self.1, std::ptr::null_mut());
        }
    }
}

#[derive(Clone, Copy)]
struct Bounds {
    controller_uid: Option<u32>,
    public_controller_uid: Option<u32>,
    /// A room resident's own activated operator route: only this uid connects,
    /// and only `transport::RESIDENT_OPERATIONS` pass.
    resident_uid: Option<u32>,
    connections: usize,
    read: Duration,
    connect: Duration,
    write: Duration,
    response: Duration,
}
const BOUNDS: Bounds = Bounds {
    controller_uid: None,
    public_controller_uid: None,
    resident_uid: None,
    connections: 64,
    read: Duration::from_secs(10),
    connect: Duration::from_secs(10),
    write: Duration::from_secs(10),
    response: Duration::from_secs(600),
};

/// Whole-frame deadline, including partial writes and trickling reads. Every
/// wait is interruptible, including a saturated upstream listen backlog.
struct BoundedStream<'a> {
    stream: &'a mut UnixStream,
    stop: &'a AtomicBool,
    deadline: Instant,
}
fn wait_fd(fd: i32, events: i16, stop: &AtomicBool, deadline: Instant) -> io::Result<()> {
    loop {
        if stop.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::ConnectionAborted,
                "public ingress stopping",
            ));
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "public ingress I/O deadline",
            ));
        }
        let mut item = libc::pollfd {
            fd,
            events,
            revents: 0,
        };
        let millis = remaining.as_millis().clamp(1, 100) as i32;
        let ready = unsafe { libc::poll(&mut item, 1, millis) };
        if ready > 0 {
            return Ok(());
        }
        if ready < 0 {
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }
}
impl Read for BoundedStream<'_> {
    fn read(&mut self, bytes: &mut [u8]) -> io::Result<usize> {
        loop {
            wait_fd(
                self.stream.as_raw_fd(),
                libc::POLLIN,
                self.stop,
                self.deadline,
            )?;
            match self.stream.read(bytes) {
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) => {}
                result => return result,
            }
        }
    }
}
impl Write for BoundedStream<'_> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        loop {
            wait_fd(
                self.stream.as_raw_fd(),
                libc::POLLOUT,
                self.stop,
                self.deadline,
            )?;
            match self.stream.write(bytes) {
                Err(e)
                    if matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                    ) => {}
                result => return result,
            }
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

pub(crate) fn connect(path: &Path, stop: &AtomicBool, deadline: Instant) -> io::Result<UnixStream> {
    let bytes = path.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if bytes.is_empty() || bytes.contains(&0) || bytes.len() >= address.sun_path.len() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid Unix socket path",
        ));
    }
    address.sun_family = libc::AF_UNIX as _;
    for (to, from) in address.sun_path.iter_mut().zip(bytes) {
        *to = *from as _;
    }
    #[cfg(any(
        target_os = "macos",
        target_os = "freebsd",
        target_os = "openbsd",
        target_os = "netbsd"
    ))]
    {
        address.sun_len = std::mem::size_of::<libc::sockaddr_un>() as _;
    }
    let fd = unsafe { libc::socket(libc::AF_UNIX, libc::SOCK_STREAM, 0) };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let stream = unsafe { UnixStream::from_raw_fd(fd) };
    if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
        return Err(io::Error::last_os_error());
    }
    stream.set_nonblocking(true)?;
    loop {
        if stop.load(Ordering::Acquire) {
            return Err(io::Error::new(
                io::ErrorKind::ConnectionAborted,
                "public ingress stopping",
            ));
        }
        let result = unsafe {
            libc::connect(
                fd,
                (&address as *const libc::sockaddr_un).cast(),
                std::mem::size_of_val(&address) as _,
            )
        };
        if result == 0 {
            return Ok(stream);
        }
        let error = io::Error::last_os_error();
        match error.raw_os_error() {
            Some(libc::EINPROGRESS | libc::EALREADY) => {
                wait_fd(fd, libc::POLLOUT, stop, deadline)?;
                if let Some(error) = stream.take_error()? {
                    return Err(error);
                }
                // A successful SO_ERROR read is sufficient only after a pending
                // connect. EAGAIN on Unix backlog-full did not start a connect.
                return Ok(stream);
            }
            Some(libc::EISCONN) => return Ok(stream),
            Some(libc::EAGAIN | libc::EINTR) => {
                if Instant::now() >= deadline {
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        "public ingress connect deadline",
                    ));
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            _ => return Err(error),
        }
    }
}

/// The public socket's directory. Owner-private (0700) by default. With a
/// tenant group, the directory may grant that one group search (and list)
/// access — 0710 or 0750, never group-write, never anything to others — so
/// session accounts reach the filtered public relay and nothing else here.
fn public_directory(path: &Path, group: Option<u32>) -> Result<(), String> {
    let Some(group) = group else { return private_directory(path) };
    if !path.is_absolute() {
        return Err("public proxy socket paths must be absolute".into());
    }
    let parent = path.parent().ok_or("socket requires a parent directory")?;
    let metadata =
        fs::symlink_metadata(parent).map_err(|e| format!("cannot inspect {}: {e}", parent.display()))?;
    if !group_directory_custody(&metadata, mini_sdk::private::euid(), group) {
        return Err(format!(
            "socket directory {} must be owned by this user, group {group}, mode 0710 or 0750",
            parent.display()
        ));
    }
    Ok(())
}

fn group_directory_custody(metadata: &fs::Metadata, owner: u32, group: u32) -> bool {
    metadata.is_dir()
        && metadata.uid() == owner
        && metadata.gid() == group
        && metadata.mode() & 0o7777 & !0o750 == 0
        && metadata.mode() & 0o700 == 0o700
}

fn private_directory(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("public proxy socket paths must be absolute".into());
    }
    let parent = path.parent().ok_or("socket requires a parent directory")?;
    crate::fsio::check_private_dir(parent)
}
fn check_upstream(path: &Path, config: &[u8]) -> Result<(), String> {
    private_directory(path)?;
    // Existing operator service pins are read, never created or changed here.
    for (pin, expected) in [
        (path.with_extension("mode"), b"operator-v1".as_slice()),
        (path.with_extension("config"), config),
    ] {
        let metadata =
            fs::symlink_metadata(&pin).map_err(|e| format!("cannot inspect upstream pin: {e}"))?;
        if !mini_sdk::private::file_ok(&metadata) {
            return Err("upstream pin is not an owner-private regular file".into());
        }
        if transport::read_config(&pin)? != expected {
            return Err("upstream operator mode/config pin mismatch".into());
        }
    }
    let metadata =
        fs::symlink_metadata(path).map_err(|e| format!("cannot inspect upstream socket: {e}"))?;
    if !mini_sdk::private::socket_ok(&metadata) {
        return Err("upstream is not an owner-private Unix socket".into());
    }
    Ok(())
}

/// The client receives the 254 frame (its bytes unchanged); the operator's log, this relay's
/// stderr, receives the same reason with the peer that was refused.
fn refusal(stream: &mut UnixStream, stop: &AtomicBool, bounds: Bounds, reason: &str) {
    let peer = transport::peer_uid(stream).map_or_else(|_| "unknown".to_owned(), |uid| uid.to_string());
    eprintln!("mini: public proxy refused uid {peer}: {reason}");
    let mut frame = vec![254];
    frame.extend_from_slice(reason.as_bytes());
    let _ = transport::write_frame(
        &mut BoundedStream {
            stream,
            stop,
            deadline: Instant::now() + bounds.write,
        },
        &frame,
    );
}

fn connection(
    mut public: UnixStream,
    upstream: &Path,
    config: &[u8],
    catalog: bool,
    stop: &AtomicBool,
    bounds: Bounds,
    accepted: Instant,
) {
    if public.set_nonblocking(true).is_err() {
        return;
    }
    if bounds.controller_uid.is_some_and(|uid| transport::peer_uid(&public).ok() != Some(uid)) {
        return refusal(&mut public, stop, bounds, "controller peer UID mismatch");
    }
    if bounds.resident_uid.is_some_and(|uid| transport::peer_uid(&public).ok() != Some(uid)) {
        return refusal(&mut public, stop, bounds, "resident peer UID mismatch");
    }
    if bounds.public_controller_uid.is_some_and(|uid|
        !matches!(transport::peer_uid(&public), Ok(peer) if peer == uid || peer == mini_sdk::private::euid())) {
        return refusal(&mut public, stop, bounds, "public controller peer UID mismatch");
    }
    let frame = match transport::read_frame(&mut BoundedStream {
        stream: &mut public,
        stop,
        deadline: accepted + bounds.read,
    }) {
        Ok(Some(frame)) => frame,
        Ok(None) => return,
        Err(error) => {
            eprintln!("mini: public proxy frame read: {error}");
            return refusal(
                &mut public,
                stop,
                bounds,
                "invalid socket frame or ingress deadline",
            )
        }
    };
    let envelope = if bounds.resident_uid.is_some() {
        transport::resident_operator_envelope(&frame, config, catalog)
    } else if bounds.controller_uid.is_some() {
        transport::agent_operator_envelope(&frame, config).map_err(String::from)
    } else { transport::public_envelope(&frame, config, catalog).map_err(String::from) };
    if let Err(reason) = envelope {
        return refusal(&mut public, stop, bounds, &reason);
    }
    // Recheck retained config/mode on every request: a restarted backend must
    // not silently introduce a new deployment under a still-running relay.
    if check_upstream(upstream, config).is_err() {
        return refusal(
            &mut public,
            stop,
            bounds,
            "upstream operator mode/config pin mismatch",
        );
    }
    let mut private = match connect(upstream, stop, Instant::now() + bounds.connect) {
        Ok(stream) => stream,
        Err(error) => {
            eprintln!("mini: public proxy upstream {} unavailable: {error}", upstream.display());
            return refusal(
                &mut public,
                stop,
                bounds,
                "public ingress upstream unavailable",
            )
        }
    };
    if transport::peer_uid(&private).ok() != Some(mini_sdk::private::euid()) {
        return refusal(&mut public, stop, bounds, "upstream peer UID mismatch");
    }
    // Once the first write starts, failure is uncertain. Never manufacture a
    // 254 refusal after forwarding; an admitted request may have lost its reply.
    if transport::write_frame(
        &mut BoundedStream {
            stream: &mut private,
            stop,
            deadline: Instant::now() + bounds.write,
        },
        &frame,
    )
    .is_err()
    {
        eprintln!("mini: public proxy op {} forward to the upstream failed; the outcome is uncertain", frame.first().copied().unwrap_or(0));
        return;
    }
    let response = match transport::read_frame(&mut BoundedStream {
        stream: &mut private,
        stop,
        deadline: Instant::now() + bounds.response,
    }) {
        Ok(Some(frame)) => frame,
        other => {
            let why = match other { Err(error) => error.to_string(), _ => "the upstream closed without a reply".to_owned() };
            eprintln!("mini: public proxy op {} reply lost; the outcome is uncertain: {why}", frame.first().copied().unwrap_or(0));
            return;
        }
    };
    let _ = transport::write_frame(
        &mut BoundedStream {
            stream: &mut public,
            stop,
            deadline: Instant::now() + bounds.write,
        },
        &response,
    );
}

struct Workers {
    stop: Arc<AtomicBool>,
    handles: Vec<JoinHandle<()>>,
}
impl Drop for Workers {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::Release);
        for handle in self.handles.drain(..) {
            let _ = handle.join();
        }
    }
}
fn run(
    listener: UnixListener,
    upstream: PathBuf,
    config: Vec<u8>,
    stop: Arc<AtomicBool>,
    bounds: Bounds,
    signals: bool,
) -> Result<(), String> {
    listener
        .set_nonblocking(true)
        .map_err(|e| format!("cannot bound public accept: {e}"))?;
    let catalog = transport::catalog_enabled(&config)?;
    let config = Arc::new(config);
    let upstream = Arc::new(upstream);
    let mut workers = Workers {
        stop: stop.clone(),
        handles: Vec::new(),
    };
    while !stop.load(Ordering::Acquire) && !(signals && SIGNAL_STOP.load(Ordering::Relaxed)) {
        let mut index = 0;
        while index < workers.handles.len() {
            if workers.handles[index].is_finished() {
                let _ = workers.handles.swap_remove(index).join();
            } else {
                index += 1;
            }
        }
        match listener.accept() {
            Ok((mut stream, _)) => {
                let accepted = Instant::now();
                stream
                    .set_nonblocking(true)
                    .map_err(|e| format!("cannot bound public connection: {e}"))?;
                if workers.handles.len() >= bounds.connections {
                    // Tiny refusal, one nonblocking attempt: overload must not
                    // stall acceptance or delay observing SIGTERM.
                    eprintln!("mini: public proxy refused a connection: busy: public ingress connection limit ({})", bounds.connections);
                    let _ = transport::write_frame(
                        &mut stream,
                        b"\xfebusy: public ingress connection limit",
                    );
                    continue;
                }
                let (config, upstream, stop) = (config.clone(), upstream.clone(), stop.clone());
                let handle = std::thread::Builder::new()
                    .name("mini-public-client".into())
                    .stack_size(256 * 1024)
                    .spawn(move || {
                        connection(stream, &upstream, &config, catalog, &stop, bounds, accepted)
                    })
                    .map_err(|e| format!("cannot start public client reader: {e}"))?;
                workers.handles.push(handle);
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                mini_sdk::private::wait_readable(std::os::fd::AsRawFd::as_raw_fd(&listener), std::time::Duration::from_millis(10))
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(format!("public accept failed: {e}")),
        }
    }
    // Close the listener before joining workers; the RAII guard cancels and
    // joins all of them. No detached task can retain a socket after exit.
    drop(listener);
    drop(workers);
    Ok(())
}

struct SocketGuard<'a>(&'a Path, u64, u64);
impl Drop for SocketGuard<'_> {
    fn drop(&mut self) {
        if let Ok(metadata) = fs::symlink_metadata(self.0) {
            if metadata.file_type().is_socket()
                && (metadata.dev(), metadata.ino()) == (self.1, self.2)
            {
                let _ = fs::remove_file(self.0);
            }
        }
    }
}
/// Linux POSIX ACL v2, with exactly one named user and no named groups. Exact
/// encoding also refuses masked-away permissions, duplicates and unknown entries.
#[cfg(target_os = "linux")]
fn controller_acl(uid: u32, owner: u16, user: u16, group: u16, other: u16) -> Vec<u8> {
    let mut bytes = 2u32.to_le_bytes().to_vec();
    for (tag, permissions, id) in [(1u16, owner, u32::MAX), (2, user, uid),
        (4, group, u32::MAX), (16, user | group, u32::MAX), (32, other, u32::MAX)] {
        bytes.extend_from_slice(&tag.to_le_bytes());
        bytes.extend_from_slice(&permissions.to_le_bytes());
        bytes.extend_from_slice(&id.to_le_bytes());
    }
    bytes
}

#[cfg(target_os = "linux")]
fn directory_acl(fd: i32, default: bool) -> Result<Option<Vec<u8>>, String> {
    // O_PATH descriptors work even through search-only ancestors. The proc fd
    // names the already-open directory, so a rename cannot redirect this read.
    let path = std::ffi::CString::new(format!("/proc/self/fd/{fd}")).unwrap();
    let name = if default { c"system.posix_acl_default" } else { c"system.posix_acl_access" };
    let mut bytes = vec![0u8; 4096];
    let size = unsafe { libc::getxattr(path.as_ptr(), name.as_ptr(), bytes.as_mut_ptr().cast(), bytes.len()) };
    if size < 0 {
        let error = io::Error::last_os_error();
        return match error.raw_os_error() {
            Some(libc::ENODATA | libc::EOPNOTSUPP) => Ok(None),
            _ => Err(format!("cannot inspect controller ingress ACL: {error}")),
        };
    }
    bytes.truncate(size as usize);
    Ok(Some(bytes))
}

#[cfg(target_os = "linux")]
fn controller_directory_ok(metadata: &fs::Metadata, access: Option<&[u8]>, defaults: Option<&[u8]>, uid: u32, parent: bool) -> bool {
    let owner = mini_sdk::private::euid();
    if !metadata.is_dir() || ![0, owner].contains(&metadata.uid())
        || metadata.mode() & 0o7022 != 0 || defaults.is_some() {
        return false;
    }
    if parent {
        return metadata.uid() == owner && metadata.mode() & 0o7777 == 0o710
            && access == Some(controller_acl(uid, 7, 1, 0, 0).as_slice());
    }
    match access {
        None => true,
        Some(bytes) if bytes.len() == 44 => {
            let group = u16::from_le_bytes([bytes[22], bytes[23]]);
            group & !5 == 0 && bytes == controller_acl(uid,
                ((metadata.mode() >> 6) & 7) as u16, 1, group, (metadata.mode() & 7) as u16)
        }
        Some(_) => false,
    }
}

/// Retain every verified ancestor until the service stops. All socket and
/// sidecar mutations then resolve through the final descriptor, not a pathname
/// reopened after checking it. No symlinks, `..`, foreign owners, writable
/// group/other entries, default ACLs or additional named identities are allowed.
#[cfg(target_os = "linux")]
struct ControllerDirectory {
    _ancestors: Vec<fs::File>,
    socket: PathBuf,
}
#[cfg(target_os = "linux")]
impl ControllerDirectory {
    fn open(socket: &Path, uid: u32) -> Result<Self, String> {
        use std::path::Component;
        if uid == 0 || uid == mini_sdk::private::euid() { return Err("controller ingress requires a distinct non-root UID".into()); }
        let components = socket.components().collect::<Vec<_>>();
        if components.len() < 2 || components[0] != Component::RootDir
            || components[1..].iter().any(|c| !matches!(c, Component::Normal(_))) {
            return Err("controller ingress requires an absolute normal socket path".into());
        }
        let root = unsafe { libc::open(c"/".as_ptr(), libc::O_PATH | libc::O_DIRECTORY | libc::O_CLOEXEC) };
        if root < 0 { return Err(io::Error::last_os_error().to_string()); }
        let mut ancestors = vec![unsafe { fs::File::from_raw_fd(root) }];
        for index in 0..components.len()-1 {
            if index > 0 {
                let name = std::ffi::CString::new(components[index].as_os_str().as_bytes()).map_err(|_| "NUL directory component")?;
                let fd = unsafe { libc::openat(ancestors.last().unwrap().as_raw_fd(), name.as_ptr(),
                    libc::O_PATH | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC) };
                if fd < 0 { return Err(format!("cannot open controller ingress ancestor: {}", io::Error::last_os_error())); }
                ancestors.push(unsafe { fs::File::from_raw_fd(fd) });
            }
            let directory = ancestors.last().unwrap();
            let metadata = directory.metadata().map_err(|e| e.to_string())?;
            let access = directory_acl(directory.as_raw_fd(), false)?;
            let defaults = directory_acl(directory.as_raw_fd(), true)?;
            if !controller_directory_ok(&metadata, access.as_deref(), defaults.as_deref(), uid, index == components.len()-2) {
                return Err("controller ingress ancestor/parent ownership, mode or exact ACL mismatch".into());
            }
        }
        let path = PathBuf::from(format!("/proc/self/fd/{}", ancestors.last().unwrap().as_raw_fd()))
            .join(socket.file_name().ok_or("controller socket has no filename")?);
        Ok(Self { _ancestors: ancestors, socket: path })
    }
    fn validate(&self, uid: u32) -> Result<(), String> {
        for (index, directory) in self._ancestors.iter().enumerate() {
            let metadata = directory.metadata().map_err(|e| e.to_string())?;
            let access = directory_acl(directory.as_raw_fd(), false)?;
            let defaults = directory_acl(directory.as_raw_fd(), true)?;
            if !controller_directory_ok(&metadata, access.as_deref(), defaults.as_deref(), uid, index + 1 == self._ancestors.len()) {
                return Err("controller ingress custody changed before service lock acquisition".into());
            }
        }
        Ok(())
    }
}

#[cfg(target_os = "linux")]
fn install_controller_socket_acl(socket: &Path, identity: (u64, u64), uid: u32) -> Result<(), String> {
    let inspect = || -> Result<(), String> {
        let metadata = fs::symlink_metadata(socket).map_err(|e| e.to_string())?;
        if !metadata.file_type().is_socket() || metadata.uid() != mini_sdk::private::euid()
            || (metadata.dev(), metadata.ino()) != identity { return Err("controller socket changed during ACL installation".into()); }
        Ok(())
    };
    inspect()?;
    fs::set_permissions(socket, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
    let name = std::ffi::CString::new(socket.as_os_str().as_bytes()).map_err(|_| "NUL socket path")?;
    let acl = controller_acl(uid, 6, 2, 0, 0);
    if unsafe { libc::lsetxattr(name.as_ptr(), c"system.posix_acl_access".as_ptr(), acl.as_ptr().cast(), acl.len(), 0) } != 0 {
        return Err(format!("cannot install exact controller socket ACL: {}", io::Error::last_os_error()));
    }
    inspect()?;
    let mut actual = vec![0u8; 4096];
    let n = unsafe { libc::lgetxattr(name.as_ptr(), c"system.posix_acl_access".as_ptr(), actual.as_mut_ptr().cast(), actual.len()) };
    if n < 0 || &actual[..n as usize] != acl.as_slice() { return Err("controller socket ACL readback mismatch".into()); }
    Ok(())
}

fn pin_public_controller(socket: &Path, controller: Option<u32>) -> Result<(), String> {
    let pin = socket.with_extension("controller");
    match controller {
        Some(uid) => transport::pin_config(&pin, format!("MINI-PUBLIC-CONTROLLER/v1\n{uid}\n").as_bytes()),
        None => match fs::symlink_metadata(pin) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(()),
            _ => Err("public controller selection is retained; --controller-uid must match".into()),
        },
    }
}

pub(crate) fn serve(socket: &Path, upstream: &Path, config: &Path, group: Option<u32>, controller: Option<u32>) -> Result<(), String> {
    let public_address = socket.to_path_buf();
    if group.is_some() && controller.is_some() { return Err("--socket-gid and --controller-uid are mutually exclusive".into()); }
    #[cfg(not(target_os = "linux"))]
    if controller.is_some() { return Err("controller public ingress requires Linux POSIX ACLs".into()); }
    #[cfg(target_os = "linux")]
    let directory = controller.map(|uid| ControllerDirectory::open(socket, uid)).transpose()?;
    #[cfg(target_os = "linux")]
    let socket = directory.as_ref().map_or(socket, |directory| directory.socket.as_path());
    if controller.is_none() { public_directory(socket, group)?; }
    private_directory(upstream)?;
    let resolved = |path: &Path| -> Result<PathBuf, String> {
        Ok(
            fs::canonicalize(path.parent().ok_or("socket has no parent")?)
                .map_err(|e| e.to_string())?
                .join(path.file_name().ok_or("socket has no name")?),
        )
    };
    if resolved(socket)? == resolved(upstream)? {
        return Err("public and upstream sockets must differ".into());
    }
    let config_bytes = transport::read_config(config)?;
    transport::catalog_enabled(&config_bytes)?;
    check_upstream(upstream, &config_bytes)?;
    let stop = Arc::new(AtomicBool::new(false));
    let probe = connect(upstream, &stop, Instant::now() + BOUNDS.connect)
        .map_err(|e| format!("upstream unavailable: {e}"))?;
    if transport::peer_uid(&probe)? != mini_sdk::private::euid() {
        return Err("upstream peer UID mismatch".into());
    }
    drop(probe);
    let _lock = transport::service_lock(&socket.with_extension("lock"))?;
    // Installer teardown holds this same flock. Recheck through retained FDs
    // after taking it, so an earlier directory check never authorizes a rebind.
    #[cfg(target_os = "linux")]
    if let (Some(directory), Some(uid)) = (&directory, controller) { directory.validate(uid)?; }
    pin_public_controller(socket, controller)?;
    transport::pin_service_mode(
        &socket.with_extension("mode"),
        false,
        socket.with_extension("config").exists(),
    )?;
    transport::clear_stale_socket(socket)?;
    transport::pin_config(&socket.with_extension("config"), &config_bytes)?;
    let listener =
        UnixListener::bind(socket).map_err(|e| format!("cannot bind public socket: {e}"))?;
    let metadata = fs::symlink_metadata(socket).map_err(|e| e.to_string())?;
    let _socket_guard = SocketGuard(socket, metadata.dev(), metadata.ino());
    #[cfg(target_os = "linux")]
    if let Some(uid) = controller { install_controller_socket_acl(socket, (metadata.dev(), metadata.ino()), uid)?; }
    if controller.is_none() { match group {
        None => fs::set_permissions(socket, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?,
        Some(group) => {
            std::os::unix::fs::lchown(socket, None, Some(group))
                .map_err(|e| format!("cannot give the public socket to group {group}: {e}"))?;
            fs::set_permissions(socket, fs::Permissions::from_mode(0o660)).map_err(|e| e.to_string())?;
        }
    }
    }
    let _signals = Signals::install()?;
    eprintln!(
        "mini: serving public proxy {} -> {}",
        public_address.display(),
        upstream.display()
    );
    run(
        listener,
        upstream.to_path_buf(),
        config_bytes,
        stop,
        Bounds { public_controller_uid: controller, ..BOUNDS },
        true,
    )
}

/// Systemd supplies a controller-owned private plan listener and optionally
/// a second status-only control listener. Legacy one-listener units retain their
/// exact restricted plan surface. This
/// process runs as the Store operator and never owns controller custody keys.
/// The kernel reports the listener creator's credentials to connecting clients;
/// clients explicitly pin those credentials, independently of our service UID.
#[cfg(target_os = "linux")]
pub(crate) fn serve_agent_activated(socket: &Path, upstream: &Path, config: &Path, controller_uid: u32) -> Result<(), String> {
    if controller_uid == 0 || controller_uid == mini_sdk::private::euid() {
        return Err("agent proxy requires a distinct non-root controller UID".into());
    }
    if std::env::var("LISTEN_PID").ok().as_deref() != Some(std::process::id().to_string().as_str()) {
        return Err("agent proxy requires systemd activation for this process".into());
    }
    let control_enabled=agent_control_enabled(std::env::var("LISTEN_FDS").ok().as_deref())?;
    // SAFETY: ownership of the declared activation descriptors transfers once.
    let listener = unsafe { UnixListener::from_raw_fd(3) };
    validate_activated_listener(&listener, socket)?;
    let control=if control_enabled {
        let control=unsafe { UnixListener::from_raw_fd(4) };
        validate_activated_listener(&control,&socket.with_extension("control"))?;
        Some(control)
    } else {None};
    private_directory(upstream)?;
    let config_bytes = transport::read_config(config)?;
    check_upstream(upstream, &config_bytes)?;
    let stop = Arc::new(AtomicBool::new(false));
    let probe = connect(upstream, &stop, Instant::now() + BOUNDS.connect)
        .map_err(|error| format!("agent proxy upstream unavailable: {error}"))?;
    if transport::peer_uid(&probe)? != mini_sdk::private::euid() {
        return Err("agent proxy upstream peer UID mismatch".into());
    }
    drop(probe);
    let _signals = Signals::install()?;
    let status=control.map(|control| {
        let (stop,upstream)=(stop.clone(),upstream.with_extension("control"));
        std::thread::Builder::new().name("mini-agent-status".into())
            .spawn(move || crate::operator_drain::serve_status_proxy(control,&upstream,controller_uid,&stop))
            .map_err(|e|format!("cannot start agent status proxy: {e}"))
    }).transpose()?;
    let result=run(listener, upstream.to_path_buf(), config_bytes, stop.clone(),
        Bounds { controller_uid: Some(controller_uid), ..BOUNDS }, true);
    stop.store(true,Ordering::Release);
    if let Some(status)=status {let _=status.join();}
    result
}

#[cfg(target_os = "linux")]
fn agent_control_enabled(count:Option<&str>)->Result<bool,String> {
    match count {
        Some("1")=>Ok(false),
        Some("2")=>Ok(true),
        _=>Err("agent proxy requires one plan listener or two listeners (plan, status)".into()),
    }
}

/// A room resident's operator route (deploy/hermes/README.md "One uid per
/// resident"). Systemd supplies two listeners bound in the resident's own
/// 0700 directory with `SocketUser` the resident: fd3 at `socket` (Host
/// frames, `transport::RESIDENT_OPERATIONS` only) and fd4 at
/// `socket.control` (the status action only, never drain). This process runs
/// as the Store operator; the resident pins the listeners' creator (systemd,
/// uid 0) with `--operator-peer-uid` / `MINI_OPERATOR_PEER_UID`.
#[cfg(target_os = "linux")]
pub(crate) fn serve_resident_activated(socket: &Path, upstream: &Path, config: &Path, resident_uid: u32) -> Result<(), String> {
    if resident_uid == 0 || resident_uid == mini_sdk::private::euid() {
        return Err("resident proxy requires a distinct non-root resident UID".into());
    }
    if std::env::var("LISTEN_PID").ok().as_deref() != Some(std::process::id().to_string().as_str())
        || std::env::var("LISTEN_FDS").ok().as_deref() != Some("2") {
        return Err("resident proxy requires exactly two systemd-activated listeners (socket, control) for this process".into());
    }
    // SAFETY: ownership of activation fds 3 and 4 transfers to this process exactly once.
    let (listener, control) = unsafe { (UnixListener::from_raw_fd(3), UnixListener::from_raw_fd(4)) };
    validate_activated_listener(&listener, socket)?;
    validate_activated_listener(&control, &socket.with_extension("control"))?;
    private_directory(upstream)?;
    let config_bytes = transport::read_config(config)?;
    check_upstream(upstream, &config_bytes)?;
    let stop = Arc::new(AtomicBool::new(false));
    let probe = connect(upstream, &stop, Instant::now() + BOUNDS.connect)
        .map_err(|error| format!("resident proxy upstream unavailable: {error}"))?;
    if transport::peer_uid(&probe)? != mini_sdk::private::euid() {
        return Err("resident proxy upstream peer UID mismatch".into());
    }
    drop(probe);
    let _signals = Signals::install()?;
    let status = {
        let (stop, upstream) = (stop.clone(), upstream.with_extension("control"));
        std::thread::Builder::new().name("mini-resident-status".into())
            .spawn(move || crate::operator_drain::serve_status_proxy(control, &upstream, resident_uid, &stop))
            .map_err(|e| format!("cannot start resident status proxy: {e}"))?
    };
    let result = run(listener, upstream.to_path_buf(), config_bytes, stop.clone(),
        Bounds { resident_uid: Some(resident_uid), ..BOUNDS }, true);
    stop.store(true, Ordering::Release);
    let _ = status.join();
    result
}

#[cfg(target_os = "linux")]
pub(crate) fn validate_activated_listener(listener: &UnixListener, socket: &Path) -> Result<(), String> {
    if !socket.is_absolute() || listener.local_addr().map_err(|e| e.to_string())?.as_pathname() != Some(socket) {
        return Err("activated listener path differs from configured controller socket".into());
    }
    let mut accepting: libc::c_int = 0;
    let mut length = std::mem::size_of_val(&accepting) as libc::socklen_t;
    if unsafe { libc::getsockopt(listener.as_raw_fd(), libc::SOL_SOCKET, libc::SO_ACCEPTCONN,
            (&mut accepting as *mut libc::c_int).cast(), &mut length) } != 0 || accepting != 1 {
        return Err("activated descriptor is not a listening Unix socket".into());
    }
    if unsafe { libc::fcntl(listener.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC) } < 0 {
        return Err("cannot protect activated listener descriptor".into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    const CONFIG: &[u8] = br#"{"domain":"7"}"#;

    #[cfg(target_os = "linux")]
    #[test]
    fn public_controller_exact_directory_acl_rejects_extra_rights_and_identities() {
        let dir = std::env::temp_dir().join(format!("mini-controller-acl-{}",std::process::id()));
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir,fs::Permissions::from_mode(0o710)).unwrap();
        let metadata=fs::symlink_metadata(&dir).unwrap();
        let uid=mini_sdk::private::euid().wrapping_add(1);
        let acl=controller_acl(uid,7,1,0,0);
        assert!(controller_directory_ok(&metadata,Some(&acl),None,uid,true));
        assert!(!controller_directory_ok(&metadata,None,None,uid,true));
        for wrong in [controller_acl(uid+1,7,1,0,0),controller_acl(uid,7,3,0,0),
            controller_acl(uid,7,1,1,0),controller_acl(uid,7,1,0,1)] {
            assert!(!controller_directory_ok(&metadata,Some(&wrong),None,uid,true));
        }
        let mut masked=acl.clone();masked[30]=0;masked[31]=0;
        assert!(!controller_directory_ok(&metadata,Some(&masked),None,uid,true));
        let mut extra=acl.clone();extra.extend_from_slice(&[8,0,1,0,9,0,0,0]);
        assert!(!controller_directory_ok(&metadata,Some(&extra),None,uid,true));
        assert!(!controller_directory_ok(&metadata,Some(&acl),Some(&acl),uid,true));
        fs::set_permissions(&dir,fs::Permissions::from_mode(0o730)).unwrap();
        assert!(!controller_directory_ok(&fs::metadata(&dir).unwrap(),Some(&acl),None,uid,true));
        fs::remove_dir(dir).unwrap();
    }
    #[test]
    fn public_controller_selection_cannot_be_dropped_or_changed() {
        let dir=std::env::temp_dir().join(format!("mini-controller-pin-{}",std::process::id()));
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir,fs::Permissions::from_mode(0o700)).unwrap();
        let socket=dir.join("public.sock");
        pin_public_controller(&socket,None).unwrap();
        pin_public_controller(&socket,Some(65533)).unwrap();
        pin_public_controller(&socket,Some(65533)).unwrap();
        assert!(pin_public_controller(&socket,None).is_err());
        assert!(pin_public_controller(&socket,Some(65532)).is_err());
        assert_eq!(fs::read(socket.with_extension("controller")).unwrap(),b"MINI-PUBLIC-CONTROLLER/v1\n65533\n");
        fs::remove_dir_all(dir).unwrap();
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn public_controller_socket_acl_is_recreated_after_rebind() {
        let dir=std::env::temp_dir().join(format!("mini-controller-rebind-{}",std::process::id()));
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir,fs::Permissions::from_mode(0o700)).unwrap();
        let socket=dir.join("public.sock");
        let uid=mini_sdk::private::euid().wrapping_add(1);
        for _ in 0..2 {
            let listener=UnixListener::bind(&socket).unwrap();
            let metadata=fs::symlink_metadata(&socket).unwrap();
            install_controller_socket_acl(&socket,(metadata.dev(),metadata.ino()),uid).unwrap();
            assert_eq!(fs::metadata(&socket).unwrap().mode()&0o777,0o620);
            assert!(install_controller_socket_acl(&socket,(metadata.dev(),metadata.ino().wrapping_add(1)),uid).is_err());
            drop(listener);fs::remove_file(&socket).unwrap();
        }
        fs::remove_dir(dir).unwrap();
    }
    #[test]
    fn public_controller_mode_preserves_public_filter_instead_of_operator_filter() {
        let (fixture,backend)=Fixture::new(Bounds{public_controller_uid:Some(mini_sdk::private::euid().wrapping_add(1)),..bounds()});
        // Owner remains admitted; controller peer admission is an additional public peer,
        // never the activated six-operation operator transport.
        let frame=envelope(CONFIG,&[0]);
        let mut client=fixture.client();
        transport::write_frame(&mut client,&frame).unwrap();
        let mut upstream=accept(&backend);
        assert_eq!(transport::read_frame(&mut upstream).unwrap(),Some(frame));
        transport::write_frame(&mut upstream,&[0,9]).unwrap();
        assert_eq!(transport::read_frame(&mut client).unwrap(),Some(vec![0,9]));
        let mut forbidden=fixture.client();
        transport::write_frame(&mut forbidden,&envelope(CONFIG,&[22,1])).unwrap();
        assert_eq!(transport::read_frame(&mut forbidden).unwrap().unwrap()[0],254);
    }
    #[test]
    fn transport_public_socket_group_directory_admits_only_group_search() {
        let root = std::env::temp_dir().join(format!("mini-public-group-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let me = mini_sdk::private::euid();
        let gid = fs::metadata(&root).unwrap().gid();
        let socket = root.join("mini.sock");
        for (mode, admitted) in [(0o710, true), (0o750, true), (0o700, true), (0o770, false), (0o711, false), (0o755, false), (0o730, false), (0o2750, false), (0o610, false)] {
            fs::set_permissions(&root, fs::Permissions::from_mode(mode)).unwrap();
            let metadata = fs::symlink_metadata(&root).unwrap();
            assert_eq!(group_directory_custody(&metadata, me, gid), admitted, "mode {mode:o}");
            assert_eq!(public_directory(&socket, Some(gid)).is_ok(), admitted, "mode {mode:o}");
            assert!(!group_directory_custody(&metadata, me, gid.wrapping_add(1)));
            assert!(!group_directory_custody(&metadata, me.wrapping_add(1), gid));
        }
        // Without a tenant group the rule is exactly the owner-private one.
        fs::set_permissions(&root, fs::Permissions::from_mode(0o710)).unwrap();
        assert!(public_directory(&socket, None).is_err());
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        assert!(public_directory(&socket, None).is_ok());
        fs::remove_dir_all(&root).unwrap();
    }
    fn envelope(config: &[u8], request: &[u8]) -> Vec<u8> {
        let mut frame = vec![2];
        frame.extend_from_slice(&(config.len() as u32).to_le_bytes());
        frame.extend_from_slice(config);
        frame.extend_from_slice(&[0xab; 32]);
        frame.extend_from_slice(request);
        frame
    }
    fn bounds() -> Bounds {
        Bounds {
            controller_uid: None,
            public_controller_uid: None,
            resident_uid: None,
            connections: 3,
            read: Duration::from_millis(150),
            connect: Duration::from_millis(150),
            write: Duration::from_millis(150),
            response: Duration::from_millis(400),
        }
    }
    struct Fixture {
        directory: PathBuf,
        private: PathBuf,
        public: PathBuf,
        stop: Arc<AtomicBool>,
        thread: Option<JoinHandle<Result<(), String>>>,
    }
    impl Fixture {
        fn new(bounds: Bounds) -> (Self, UnixListener) {
            let directory = std::env::temp_dir().join(format!(
                "mini-ingress-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            fs::create_dir(&directory).unwrap();
            fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
            let private = directory.join("private.sock");
            let public = directory.join("public.sock");
            fs::write(private.with_extension("mode"), b"operator-v1").unwrap();
            fs::write(private.with_extension("config"), CONFIG).unwrap();
            for p in [
                private.with_extension("mode"),
                private.with_extension("config"),
            ] {
                fs::set_permissions(p, fs::Permissions::from_mode(0o600)).unwrap();
            }
            let backend = UnixListener::bind(&private).unwrap();
            backend.set_nonblocking(true).unwrap();
            fs::set_permissions(&private, fs::Permissions::from_mode(0o600)).unwrap();
            let listener = UnixListener::bind(&public).unwrap();
            let stop = Arc::new(AtomicBool::new(false));
            let (path, stopping) = (private.clone(), stop.clone());
            let thread = std::thread::spawn(move || {
                run(listener, path, CONFIG.to_vec(), stopping, bounds, false)
            });
            (
                Self {
                    directory,
                    private,
                    public,
                    stop,
                    thread: Some(thread),
                },
                backend,
            )
        }
        fn client(&self) -> UnixStream {
            let stream = UnixStream::connect(&self.public).unwrap();
            stream
                .set_read_timeout(Some(Duration::from_secs(2)))
                .unwrap();
            stream
                .set_write_timeout(Some(Duration::from_secs(2)))
                .unwrap();
            stream
        }
        fn stop(&mut self) {
            let start = Instant::now();
            self.stop.store(true, Ordering::Release);
            self.thread.take().unwrap().join().unwrap().unwrap();
            assert!(start.elapsed() < Duration::from_secs(1));
            assert!(UnixStream::connect(&self.public).is_err());
        }
    }
    impl Drop for Fixture {
        fn drop(&mut self) {
            if self.thread.is_some() {
                self.stop();
            }
            fs::remove_dir_all(&self.directory).unwrap();
        }
    }
    fn accept(listener: &UnixListener) -> UnixStream {
        let deadline = Instant::now() + Duration::from_secs(2);
        loop {
            match listener.accept() {
                Ok((stream, _)) => {
                    stream
                        .set_read_timeout(Some(Duration::from_secs(2)))
                        .unwrap();
                    return stream;
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock && Instant::now() < deadline => {
                    std::thread::sleep(Duration::from_millis(5))
                }
                Err(e) => panic!("accept: {e}"),
            }
        }
    }
    #[test]
    fn public_recipient_grain_share_lookup_forwards_exact_ingress_and_no_issue_write() {
        let (fixture,backend)=Fixture::new(bounds());
        let request=[vec![55],b"retained exact canonical event22 ingress".to_vec()].concat();
        let frame=envelope(CONFIG,&request);
        let mut client=fixture.client();
        transport::write_frame(&mut client,&frame).unwrap();
        let mut upstream=accept(&backend);
        assert_eq!(transport::read_frame(&mut upstream).unwrap(),Some(frame));
        transport::write_frame(&mut upstream,&[55,1,2,3]).unwrap();
        assert_eq!(transport::read_frame(&mut client).unwrap(),Some(vec![55,1,2,3]));
        for request in [vec![55],vec![54,1],vec![56,1],vec![57,1]] {
            let mut client=fixture.client();
            transport::write_frame(&mut client,&envelope(CONFIG,&request)).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0],254);
            assert_eq!(backend.accept().unwrap_err().kind(),io::ErrorKind::WouldBlock);
        }
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn agent_status_activation_accepts_only_legacy_or_exact_two_listeners() {
        assert_eq!(agent_control_enabled(Some("1")).unwrap(),false);
        assert_eq!(agent_control_enabled(Some("2")).unwrap(),true);
        for count in [None,Some("0"),Some("3"),Some("02"),Some("2 ")] {
            assert!(agent_control_enabled(count).is_err());
        }
        let (fixture,backend)=Fixture::new(bounds());
        assert!(validate_activated_listener(&backend,&fixture.private.with_extension("control")).is_err(),
            "a plan listener cannot be substituted as the status listener");
        let path=fixture.private.with_extension("control");
        let control=UnixListener::bind(&path).unwrap();
        validate_activated_listener(&control,&path).unwrap();
    }
    #[test]
    fn agent_operator_proxy_preserves_only_bounded_source_plans() {
        let (fixture, backend) = Fixture::new(Bounds { controller_uid: Some(mini_sdk::private::euid()), ..bounds() });
        let pair = [1u32.to_le_bytes().as_slice(), &[1, 2]].concat();
        for operation in [48, 58, 59, 78, 80, 81] {
            let request = [vec![operation], if matches!(operation, 59 | 81) { pair.clone() } else { vec![1] }].concat();
            let frame = envelope(CONFIG, &request);
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            let mut private = accept(&backend);
            assert_eq!(transport::read_frame(&mut private).unwrap(), Some(frame));
            transport::write_frame(&mut private, &[operation, 9]).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap(), Some(vec![operation, 9]));
        }
        for operation in [0, 2, 3, 22, 26, 27, 48, 55, 59, 76, 77, 79, 81, 82, 155] {
            // Even allowed opcodes refuse an empty body; submit/lifecycle/grant
            // opcodes refuse irrespective of their payload.
            let frame = envelope(CONFIG, &[operation]);
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
            assert_eq!(backend.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
        }
        let mut unpinned = vec![1];
        unpinned.extend_from_slice(&(CONFIG.len() as u32).to_le_bytes());
        unpinned.extend_from_slice(CONFIG);
        unpinned.extend_from_slice(&[80, 1]);
        for frame in [unpinned, envelope(b"changed", &[80, 1]), envelope(CONFIG, &[76, 1]), envelope(CONFIG, &[55, 1]), envelope(CONFIG, &[81, 1])] {
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
            assert_eq!(backend.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
        }
    }
    #[test]
    fn resident_operator_proxy_forwards_its_operations_and_refuses_the_rest_by_name() {
        let (fixture, backend) = Fixture::new(Bounds { resident_uid: Some(mini_sdk::private::euid()), ..bounds() });
        // The kernel activity ops carry the await bridge (`mini_answer_await`,
        // `bend deliver`): plan, assembly (an exact plan/signature pair),
        // submit, lookup and the public view.
        let mut assembly = vec![211u8];
        assembly.extend_from_slice(&1u32.to_le_bytes());
        assembly.push(1);
        assembly.extend_from_slice(&[0; 64]);
        for request in [vec![2u8, 1], vec![3, 1], vec![5, 1], vec![98, 1], [vec![151], b"{}".to_vec()].concat(),
            vec![210, 1], assembly, vec![212, 1], vec![213, 1], vec![214]] {
            let operation = request[0];
            let frame = envelope(CONFIG, &request);
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            let mut private = accept(&backend);
            assert_eq!(transport::read_frame(&mut private).unwrap(), Some(frame));
            transport::write_frame(&mut private, &[operation, 9]).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap(), Some(vec![operation, 9]));
        }
        // Operator-only operations (lifecycle, dispatch, fn namespace custody
        // signing, fn ACK, agent reserve) and public ones off the resident's
        // route are refused by name before any upstream connection.
        // Public reads a resident never makes (describe, profile, codec ops,
        // application births, fleet topic/head/incoming reads) are off it too.
        for operation in [0u8, 6, 7, 8, 11, 13, 22, 26, 30, 31, 34, 43, 58, 76, 100, 101, 121, 180, 183, 206] {
            let mut client = fixture.client();
            transport::write_frame(&mut client, &envelope(CONFIG, &[operation, 1])).unwrap();
            let reply = transport::read_frame(&mut client).unwrap().unwrap();
            assert_eq!(reply[0], 254);
            assert!(String::from_utf8_lossy(&reply[1..]).contains(&format!("operation {operation} is not on the resident operator route")));
            assert_eq!(backend.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
        }
        // A resident operation still passes the public relay's own checks: a
        // provider usage quote with a malformed body is refused, never forwarded.
        let mut client = fixture.client();
        transport::write_frame(&mut client, &envelope(CONFIG, &[19, 1])).unwrap();
        let reply = transport::read_frame(&mut client).unwrap().unwrap();
        assert_eq!(reply[0], 254);
        assert!(String::from_utf8_lossy(&reply[1..]).starts_with("operation 19: "));
        assert_eq!(backend.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
    }
    #[test]
    fn resident_operator_proxy_refuses_other_uid_before_reading_a_frame() {
        let (fixture, backend) = Fixture::new(Bounds { resident_uid: Some(mini_sdk::private::euid().wrapping_add(1)), ..bounds() });
        let mut client = fixture.client();
        assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
        assert_eq!(backend.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
    }
    #[test]
    fn agent_operator_proxy_refuses_other_uid_before_reading_a_frame() {
        let (fixture, backend) = Fixture::new(Bounds { controller_uid: Some(mini_sdk::private::euid().wrapping_add(1)), ..bounds() });
        let mut client = fixture.client();
        assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
        assert_eq!(backend.accept().unwrap_err().kind(), io::ErrorKind::WouldBlock);
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn agent_operator_activated_listener_requires_exact_named_socket() {
        let (fixture, backend) = Fixture::new(bounds());
        validate_activated_listener(&backend, &fixture.private).unwrap();
        assert!(validate_activated_listener(&backend, &fixture.public).is_err());
        assert!(validate_activated_listener(&backend, Path::new("relative.sock")).is_err());
    }
    #[test]
    fn exact_frames_and_replies_pass_without_rewriting_host_pin() {
        let (fixture, backend) = Fixture::new(bounds());
        for operation in [vec![0], vec![3, 9, 8], vec![12]] {
            let frame = envelope(CONFIG, &operation);
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            let mut private = accept(&backend);
            assert_eq!(transport::read_frame(&mut private).unwrap(), Some(frame));
            transport::write_frame(&mut private, &[operation[0], 99]).unwrap();
            assert_eq!(
                transport::read_frame(&mut client).unwrap(),
                Some(vec![operation[0], 99])
            );
        }
    }
    #[test]
    fn private_ops_and_config_substitution_never_reach_backend() {
        let (fixture, backend) = Fixture::new(bounds());
        for frame in [
            envelope(CONFIG, &[22, 1]),
            envelope(CONFIG, &[152, 1]),
            envelope(b"wrong", &[0]),
            vec![3, 0, 0, 0, 0],
        ] {
            let mut client = fixture.client();
            transport::write_frame(&mut client, &frame).unwrap();
            assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
            assert!(matches!(
                backend.accept().unwrap_err().kind(),
                io::ErrorKind::WouldBlock
            ));
        }
    }
    #[test]
    fn changed_upstream_pin_refuses_before_forwarding() {
        let (fixture, backend) = Fixture::new(bounds());
        fs::write(fixture.private.with_extension("config"), b"{}").unwrap();
        let mut client = fixture.client();
        transport::write_frame(&mut client, &envelope(CONFIG, &[0])).unwrap();
        assert_eq!(transport::read_frame(&mut client).unwrap().unwrap()[0], 254);
        assert_eq!(
            backend.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }
    #[test]
    fn stop_closes_idle_and_inflight_clients_but_private_remains_usable() {
        let (mut fixture, backend) = Fixture::new(bounds());
        let mut idle = fixture.client();
        let mut inflight = fixture.client();
        transport::write_frame(&mut inflight, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        assert!(transport::read_frame(&mut private).unwrap().is_some());
        fixture.stop();
        assert_eq!(transport::read_frame(&mut idle).unwrap(), None);
        assert_eq!(transport::read_frame(&mut inflight).unwrap(), None);
        assert_eq!(transport::read_frame(&mut private).unwrap(), None);
        let mut direct = UnixStream::connect(&fixture.private).unwrap();
        let mut receiver = accept(&backend);
        transport::write_frame(&mut direct, b"still-private").unwrap();
        assert_eq!(
            transport::read_frame(&mut receiver).unwrap(),
            Some(b"still-private".to_vec())
        );
    }
    #[test]
    fn connection_limit_and_whole_frame_deadline_release_capacity() {
        let (fixture, backend) = Fixture::new(Bounds {
            connections: 1,
            read: Duration::from_millis(300),
            ..bounds()
        });
        let mut idle = fixture.client();
        idle.write_all(&100u32.to_le_bytes()).unwrap();
        std::thread::sleep(Duration::from_millis(40));
        let mut excess = fixture.client();
        assert!(
            String::from_utf8_lossy(&transport::read_frame(&mut excess).unwrap().unwrap())
                .contains("connection limit")
        );
        assert_eq!(transport::read_frame(&mut idle).unwrap().unwrap()[0], 254);
        std::thread::sleep(Duration::from_millis(30));
        let mut next = fixture.client();
        transport::write_frame(&mut next, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        assert!(transport::read_frame(&mut private).unwrap().is_some());
        transport::write_frame(&mut private, &[0]).unwrap();
        assert_eq!(transport::read_frame(&mut next).unwrap(), Some(vec![0]));
    }
    #[test]
    fn stalled_response_is_uncertain_and_stalled_reader_does_not_hold_stop() {
        let (mut fixture, backend) = Fixture::new(bounds());
        let mut missing = fixture.client();
        transport::write_frame(&mut missing, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        transport::read_frame(&mut private).unwrap().unwrap();
        assert_eq!(
            transport::read_frame(&mut missing).unwrap(),
            None,
            "no fabricated certain refusal after forwarding"
        );
        let mut no_read = fixture.client();
        transport::write_frame(&mut no_read, &envelope(CONFIG, &[0])).unwrap();
        let mut private = accept(&backend);
        transport::read_frame(&mut private).unwrap().unwrap();
        let (sent, done) = mpsc::channel();
        let host = std::thread::spawn(move || {
            let _ = transport::write_frame(&mut private, &vec![0; 4_000_000]);
            sent.send(()).unwrap();
        });
        done.recv_timeout(Duration::from_secs(2)).unwrap();
        fixture.stop();
        host.join().unwrap();
    }
    #[test]
    fn saturated_upstream_connect_has_a_deadline() {
        let (fixture, backend) = Fixture::new(bounds());
        assert_eq!(unsafe { libc::listen(backend.as_raw_fd(), 0) }, 0);
        let _filled = UnixStream::connect(&fixture.private).unwrap();
        let start = Instant::now();
        let result = connect(
            &fixture.private,
            &AtomicBool::new(false),
            start + Duration::from_millis(100),
        );
        assert!(result.is_err());
        assert!(start.elapsed() < Duration::from_secs(1));
    }
}
