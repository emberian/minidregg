//! Explicit controller-selected full-peer consent. Only framing, peer custody and durable
//! frontier retention live here; the separately pinned Lean process decides every consent.
//! A transport/persistence failure poisons the worker. It never falls back to a new frontier.
use crate::{fsio, transport};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
type Result<T> = std::result::Result<T, String>;
const CAP: usize = 12_102_760;
const TAG: &[u8] = b"MINI-CONTROLLER-CONSENT/v1\0";
const ANCHOR_TAG: &[u8] = b"MINI-CONTROLLER-CONSENT-ANCHOR/v1\0";
const REPLAY: Duration = Duration::from_secs(900);
const IO: Duration = Duration::from_secs(30);

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Selection {
    pub(crate) socket: PathBuf,
    pub(crate) peer: u32,
    pub(crate) executable: [u8; 32],
    pub(crate) config: [u8; 32],
}
pub(crate) fn digest(s: &str) -> Result<[u8; 32]> {
    mini_sdk::hex::decode_fixed(s)
        .map_err(|_| "consent digest must be 64 lowercase hexadecimal characters".into())
}
use mini_sdk::hex::encode as hex;
impl Selection {
    pub(crate) fn from_record(v: &Value) -> Result<Option<Self>> {
        let Some(v) = v.get("delegatedConsent") else {
            return Ok(None);
        };
        let socket = PathBuf::from(
            v.get("socket")
                .and_then(Value::as_str)
                .ok_or("consent socket missing")?,
        );
        if !socket.is_absolute() {
            return Err("consent socket must be absolute".into());
        }
        let peer = u32::try_from(
            v.get("peerUid")
                .and_then(Value::as_u64)
                .ok_or("consent peer UID missing")?,
        )
        .map_err(|_| "invalid consent peer UID")?;
        Ok(Some(Self {
            socket,
            peer,
            executable: digest(
                v.get("executableSha256")
                    .and_then(Value::as_str)
                    .ok_or("consent executable digest missing")?,
            )?,
            config: digest(
                v.get("configSha256")
                    .and_then(Value::as_str)
                    .ok_or("consent config digest missing")?,
            )?,
        }))
    }
    pub(crate) fn from_env() -> Result<Option<Self>> {
        let names = [
            "MINI_CONSENT_SOCKET",
            "MINI_CONSENT_PEER_UID",
            "MINI_CONSENT_SHA256",
            "MINI_CONSENT_CONFIG_SHA256",
        ];
        Self::from_values(names.map(std::env::var_os))
    }
    fn from_values(values: [Option<std::ffi::OsString>; 4]) -> Result<Option<Self>> {
        if values.iter().all(Option::is_none) {
            return Ok(None);
        }
        let [Some(socket), Some(peer), Some(executable), Some(config)] = values else {
            return Err("all four delegated consent selections are required".into());
        };
        let socket = socket
            .into_string()
            .map_err(|_| "consent socket selection is not UTF-8")?;
        let peer = peer
            .into_string()
            .map_err(|_| "consent peer selection is not UTF-8")?;
        let executable = executable
            .into_string()
            .map_err(|_| "consent executable selection is not UTF-8")?;
        let config = config
            .into_string()
            .map_err(|_| "consent config selection is not UTF-8")?;
        let peer: u32 = peer.parse().map_err(|_| "invalid consent peer UID")?;
        Self::from_record(
            &json!({"delegatedConsent":{"socket":socket,"peerUid":peer,"executableSha256":executable,"configSha256":config}}),
        )
    }
    pub(crate) fn record(&self) -> Value {
        json!({"socket":self.socket,"peerUid":self.peer,"executableSha256":hex(&self.executable),"configSha256":hex(&self.config)})
    }
    fn hello(&self) -> Vec<u8> {
        [TAG, self.executable.as_slice(), self.config.as_slice()].concat()
    }
}

/// Whole-operation deadline shared by a reader/writer pair. Any I/O error permanently closes
/// both halves, including partial writes/reads; no later call can use a desynchronized stream.
struct Channel {
    socket: UnixStream,
    deadline: Arc<Mutex<Instant>>,
    failed: Arc<AtomicBool>,
    writer: bool,
    client: bool,
}
impl Channel {
    fn fail<T>(&self, error: io::Error) -> io::Result<T> {
        self.failed.store(true, Ordering::Release);
        let _ = self.socket.shutdown(std::net::Shutdown::Both);
        Err(error)
    }
    fn wait(&self, event: i16) -> io::Result<()> {
        if self.failed.load(Ordering::Acquire) {
            return Err(io::Error::other("consent transport is poisoned"));
        }
        let deadline = *self
            .deadline
            .lock()
            .map_err(|_| io::Error::other("consent deadline lock"))?;
        loop {
            let now = Instant::now();
            if now >= deadline {
                return self.fail(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "consent frame deadline",
                ));
            }
            let mut fd = libc::pollfd {
                fd: self.socket.as_raw_fd(),
                events: event,
                revents: 0,
            };
            let n = unsafe {
                libc::poll(
                    &mut fd,
                    1,
                    (deadline - now).as_millis().min(i32::MAX as u128).max(1) as i32,
                )
            };
            if n > 0 {
                return Ok(());
            }
            if n < 0 && io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                return self.fail(io::Error::last_os_error());
            }
        }
    }
}
impl Read for Channel {
    fn read(&mut self, b: &mut [u8]) -> io::Result<usize> {
        self.wait(libc::POLLIN)?;
        match self.socket.read(b) {
            Ok(0) => self.fail(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "consent closed",
            )),
            Ok(n) => Ok(n),
            Err(e) => self.fail(e),
        }
    }
}
impl Write for Channel {
    fn write(&mut self, b: &[u8]) -> io::Result<usize> {
        if self.writer && self.client {
            // SDK starts each exchange with the four-byte length.
            *self
                .deadline
                .lock()
                .map_err(|_| io::Error::other("consent deadline lock"))? =
                Instant::now() + REPLAY + IO;
            self.writer = false;
        }
        self.wait(libc::POLLOUT)?;
        match self.socket.write(b) {
            Ok(n) => Ok(n),
            Err(e) => self.fail(e),
        }
    }
    fn flush(&mut self) -> io::Result<()> {
        self.writer = true;
        Ok(())
    }
}
/// Whether a connection made by [`connect_with_lifeline`] can still carry the next request. The
/// worker ends a connection that has been idle for `REPLAY`, and ends itself when idle with no
/// connection; a body that keeps one connection for hours must notice before it sends, not after:
/// a frame written into a dead connection is lost, and a half-sent frame is never replayed.
pub(crate) struct Lifeline {
    socket: UnixStream,
    failed: Arc<AtomicBool>,
}
/// Linux reports a half-closed peer as POLLRDHUP; elsewhere the peer's EOF is readable (POLLIN)
/// and POLLHUP is always reported, so POLLIN alone sees the same death.
#[cfg(any(target_os = "linux", target_os = "android"))]
const HANGUP: libc::c_short = libc::POLLRDHUP;
#[cfg(not(any(target_os = "linux", target_os = "android")))]
const HANGUP: libc::c_short = 0;

impl Lifeline {
    /// Watch a connection this module did not make: a resident consent provider's
    /// (`mini_sdk::consent::connect_resident_watched`), which ends the same way when its process does.
    pub(crate) fn watching(socket: UnixStream) -> Self {
        Lifeline { socket, failed: Arc::new(AtomicBool::new(false)) }
    }
    pub(crate) fn alive(&self) -> bool {
        if self.failed.load(Ordering::Acquire) {
            return false;
        }
        let mut fd = libc::pollfd {
            fd: self.socket.as_raw_fd(),
            events: libc::POLLIN | HANGUP,
            revents: 0,
        };
        // Between requests nothing is owed to us: readable or hung up means EOF (the worker or
        // its deadline closed the connection) or stray bytes (desynchronized); either is unusable.
        unsafe { libc::poll(&mut fd, 1, 0) == 0 }
    }
}

pub(crate) fn connect(
    selection: &Selection,
    config: &[u8],
) -> Result<(Box<dyn Write + Send>, Box<dyn Read + Send>)> {
    connect_with_lifeline(selection, config).map(|(input, output, _)| (input, output))
}

pub(crate) fn connect_with_lifeline(
    selection: &Selection,
    config: &[u8],
) -> Result<(Box<dyn Write + Send>, Box<dyn Read + Send>, Lifeline)> {
    if <[u8; 32]>::from(Sha256::digest(config)) != selection.config {
        return Err("delegated consent exact config digest mismatch".into());
    }
    fsio::check_private_socket(&selection.socket)?;
    let stop = AtomicBool::new(false);
    let socket = crate::public_proxy::connect(&selection.socket, &stop, Instant::now() + IO)
        .map_err(|e| e.to_string())?;
    if transport::peer_uid(&socket)? != selection.peer {
        return Err("delegated consent endpoint peer UID mismatch".into());
    }
    fsio::check_private_socket(&selection.socket)?;
    let deadline = Arc::new(Mutex::new(Instant::now() + REPLAY + IO));
    let failed = Arc::new(AtomicBool::new(false));
    let lifeline = Lifeline {
        socket: socket.try_clone().map_err(|e| e.to_string())?,
        failed: failed.clone(),
    };
    let mut input = Channel {
        socket: socket.try_clone().map_err(|e| e.to_string())?,
        deadline: deadline.clone(),
        failed: failed.clone(),
        writer: true,
        client: true,
    };
    let mut output = Channel {
        socket,
        deadline,
        failed,
        writer: false,
        client: true,
    };
    transport::write_frame(&mut input, &selection.hello()).map_err(|e| e.to_string())?;
    let reply = transport::read_frame_bounded(&mut output, TAG.len() + 64)
        .map_err(|e| e.to_string())?
        .ok_or("consent handshake absent")?;
    if reply != selection.hello() {
        return Err("delegated consent service binding mismatch".into());
    }
    Ok((Box::new(input), Box::new(output), lifeline))
}

fn allowed(frame: &[u8]) -> bool {
    if frame.first() == Some(&mini_sdk::host_operations::CONSENT_FULL_READY) {
        return frame.len() == 1;
    }
    matches!(
        frame.first().copied(),
        Some(
            mini_sdk::host_operations::CONSENT_INTENT
                | mini_sdk::host_operations::CONSENT_OBSERVATION
                | mini_sdk::host_operations::CONSENT_PLAN
                | mini_sdk::host_operations::CONSENT_OPERATOR_PLAN
                | mini_sdk::host_operations::CONSENT_POSSESSION
                | mini_sdk::host_operations::CONSENT_OBJECTIVE
        )
    ) && frame.len() <= CAP
}
fn anchor_bytes(binding: &[u8], anchor: Option<&[u8]>) -> Vec<u8> {
    match anchor {
        Some(a) => [ANCHOR_TAG, binding, &[1], a].concat(),
        None => [ANCHOR_TAG, binding, &[0]].concat(),
    }
}
fn decode_anchor(bytes: &[u8], binding: &[u8]) -> Result<Option<Vec<u8>>> {
    let prefix = [ANCHOR_TAG, binding].concat();
    let anchor = bytes
        .strip_prefix(prefix.as_slice())
        .ok_or("consent durable anchor binding/corruption mismatch")?;
    match anchor {
        [0] => Ok(None),
        [1, rest @ ..] if !rest.is_empty() => Ok(Some(rest.to_vec())),
        _ => Err("consent durable anchor is corrupt".into()),
    }
}
struct Worker {
    child: transport::HostProcess,
    anchor: PathBuf,
    binding: Vec<u8>,
    failed: bool,
    admitted: bool,
    _lock: File,
}
impl Worker {
    fn exchange(&mut self, frame: &[u8]) -> Result<Vec<u8>> {
        if self.failed {
            return Err("consent verifier is poisoned; operator intervention required".into());
        }
        let result = self.child.exchange_within(frame, REPLAY);
        if result.is_err() {
            self.failed = true
        }
        result
    }
    fn internal(&mut self, op: u8, body: &[u8]) -> Result<Vec<u8>> {
        let reply = self.exchange(&[&[op], body].concat())?;
        if reply.first() != Some(&op) {
            self.failed = true;
            return Err(format!("consent verifier refused internal operation {op}"));
        }
        Ok(reply[1..].to_vec())
    }
    fn retain(&mut self) -> Result<()> {
        let anchor = self.internal(mini_sdk::host_operations::CONSENT_ANCHOR_ADMITTED, &[])?;
        if anchor.is_empty() {
            self.failed = true;
            return Err("verifier returned empty anchor".into());
        }
        let result =
            fsio::replace_private(&self.anchor, &anchor_bytes(&self.binding, Some(&anchor)))
                ;
        if result.is_err() {
            self.failed = true
        }
        result
    }
    fn request(&mut self, frame: &[u8]) -> Result<Vec<u8>> {
        if !allowed(frame) {
            return Err("consent operation is not delegated".into());
        }
        self.internal(mini_sdk::host_operations::CONSENT_STORE_RECHECK, &[])?;
        let answer = self.exchange(frame)?;
        if answer.first() != frame.first() && answer.first() != Some(&mini_sdk::consent::CONSENT_REFUSAL) {
            self.failed = true;
            return Err("unexpected consent verifier response".into());
        }
        // Includes candidate refusal: never discard the independently checked frontier.
        if frame[0] != 226 {
            self.admitted = true;
        }
        if self.admitted {
            self.retain()?;
        }
        Ok(answer)
    }
    fn start(executable: &Path, config: &Path, pins: &Selection, anchors: &Path) -> Result<Self> {
        fsio::check_private_dir(anchors)?;
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
            .open(anchors.join("lock"))
            .map_err(|e| e.to_string())?;
        if !mini_sdk::private::file_ok(&lock.metadata().map_err(|e| e.to_string())?) {
            return Err("unsafe consent lock".into());
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err("consent world already has a verifier".into());
        }
        let binding = pins.hello();
        let marker = anchors.join("binding");
        let anchor = anchors.join("frontier");
        let retained = match fs::symlink_metadata(&marker) {
            Ok(_) => {
                if fsio::read_private(&marker, 1024)? != binding {
                    return Err("consent world provider/config pins changed".into());
                }
                decode_anchor(&fsio::read_private(&anchor, CAP + 1024)?, &binding)?
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                if fs::symlink_metadata(&anchor).is_ok() {
                    return Err("consent anchor without binding".into());
                }
                fsio::create_private(&marker, &binding)?;
                fsio::create_private(&anchor, &anchor_bytes(&binding, None))?;
                None
            }
            Err(e) => return Err(e.to_string()),
        };
        let settings = transport::read_config(config)?;
        if <[u8; 32]>::from(Sha256::digest(&settings)) != pins.config {
            return Err("consent service exact config digest mismatch".into());
        }
        let child =
            transport::HostProcess::start_pinned(executable, config, &pins.executable, &settings)?;
        let mut worker = Self {
            child,
            anchor,
            binding,
            failed: false,
            admitted: false,
            _lock: lock,
        };
        if let Some(retained) = retained {
            worker.internal(mini_sdk::host_operations::CONSENT_ANCHOR_OFFER, &retained)?;
        }
        // 228 only installs the retained comparison point. 233 before first admission
        // is a no-op; only a source-dependent caller frame creates a new frontier.
        Ok(worker)
    }
}

// Waiting for the next command is distinct from accepting a partial command. The Host
// may be busy between signing steps; once a first byte arrives, the whole frame has 30s.
fn ingress(channel: &mut Channel, idle: Duration, frame: Duration) -> Result<Vec<u8>> {
    *channel.deadline.lock().map_err(|_| "deadline lock")? = Instant::now() + idle;
    let mut first = [0];
    channel.read_exact(&mut first).map_err(|e| e.to_string())?;
    *channel.deadline.lock().map_err(|_| "deadline lock")? = Instant::now() + frame;
    transport::read_frame_bounded(&mut io::Cursor::new(first).chain(channel), CAP)
        .map_err(|e| e.to_string())?
        .ok_or_else(|| "missing consent frame".into())
}

fn serve_connection(socket: UnixStream, pins: &Selection, worker: &Mutex<Worker>) -> Result<()> {
    if transport::peer_uid(&socket)? != pins.peer {
        return Err("consent controller peer UID mismatch".into());
    }
    socket.set_nonblocking(true).map_err(|e| e.to_string())?;
    let deadline = Arc::new(Mutex::new(Instant::now() + IO));
    let mut channel = Channel {
        socket,
        deadline: deadline.clone(),
        failed: Arc::new(AtomicBool::new(false)),
        writer: false,
        client: false,
    };
    let hello = transport::read_frame_bounded(&mut channel, TAG.len() + 64)
        .map_err(|e| e.to_string())?
        .ok_or("missing consent hello")?;
    if hello != pins.hello() {
        return Err("consent client binding mismatch".into());
    }
    transport::write_frame(&mut channel, &hello).map_err(|e| e.to_string())?;
    loop {
        let frame = ingress(&mut channel, REPLAY, IO)?;
        if !allowed(&frame) {
            return Err("consent operation is not delegated".into());
        }
        let queue_deadline = Instant::now() + IO;
        let mut guard = loop {
            match worker.try_lock() {
                Ok(g) => break g,
                Err(std::sync::TryLockError::Poisoned(_)) => {
                    return Err("consent worker lock poisoned".into())
                }
                Err(_) => {}
            }
            if Instant::now() >= queue_deadline {
                return Err("consent verifier busy".into());
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        let reply = guard.request(&frame)?;
        drop(guard);
        *deadline.lock().map_err(|_| "deadline lock")? = Instant::now() + IO;
        transport::write_frame(&mut channel, &reply).map_err(|e| e.to_string())?;
    }
}
/// Who answers a member's delegated consent: this worker's own provider child, or the operator's
/// ONE shared consent resident (split tenancy, ember 2026-10-31: the members' workers are thin
/// relays to one verifier per box).
#[derive(Clone)]
enum Backend {
    Own(Arc<Mutex<Worker>>),
    Shared(Arc<SharedVerifier>),
}

/// The operator's shared consent resident in `dir` (owner-private to the operator), reached with a
/// FRESH resident connection per member connection, so the resident re-checks the Store before
/// that connection's first frame (`ConsentAnchor.recheckStore`, frame 233) exactly as it does for
/// every `mini` command, and retains its anchor after every admission. The executable and config
/// are the member's pins: their digests are checked once here, and the executable's file identity
/// before every connection, so a replaced provider is refused, never silently resident.
struct SharedVerifier {
    dir: PathBuf,
    executable: PathBuf,
    config: PathBuf,
    settings: Vec<u8>,
    identity: (u64, u64, u64, i64, i64, i64, i64),
}
fn file_identity(meta: &fs::Metadata) -> (u64, u64, u64, i64, i64, i64, i64) {
    use std::os::unix::fs::MetadataExt;
    (meta.dev(), meta.ino(), meta.size(), meta.mtime(), meta.mtime_nsec(), meta.ctime(), meta.ctime_nsec())
}
impl SharedVerifier {
    fn start(executable: &Path, config: &Path, pins: &Selection, dir: &Path) -> Result<Self> {
        fsio::check_private_dir(dir)?;
        let settings = transport::read_config(config)?;
        if <[u8; 32]>::from(Sha256::digest(&settings)) != pins.config {
            return Err("consent service exact config digest mismatch".into());
        }
        let mut file = File::open(executable).map_err(|e| format!("consent provider {}: {e}", executable.display()))?;
        let before = file_identity(&file.metadata().map_err(|e| e.to_string())?);
        let mut digest = Sha256::new();
        io::copy(&mut file, &mut digest).map_err(|e| e.to_string())?;
        if file_identity(&file.metadata().map_err(|e| e.to_string())?) != before
            || <[u8; 32]>::from(digest.finalize()) != pins.executable
        {
            return Err("consent service exact provider digest mismatch".into());
        }
        Ok(Self { dir: dir.to_path_buf(), executable: executable.to_path_buf(), config: config.to_path_buf(), settings, identity: before })
    }
    fn connect(&self) -> Result<mini_sdk::local::Session> {
        let now = fs::metadata(&self.executable).map_err(|e| e.to_string())?;
        if file_identity(&now) != self.identity {
            return Err("consent provider changed under the delegated worker; restart it".into());
        }
        let mini = std::env::current_exe().map_err(|e| e.to_string())?;
        let mut launch = std::process::Command::new(mini);
        launch.arg("consent-resident").arg("--consent").arg(&self.executable).arg("--settings").arg(&self.config)
            .env("MINI_CONSENT_ANCHOR_DIR", &self.dir);
        Ok(mini_sdk::consent::connect_resident_in(&self.dir, mini_sdk::consent::ResidentKind::Consent,
            &self.executable, self.settings.clone(), launch)?)
    }
}

/// [`serve_connection`] over the shared verifier: the same peer check, handshake, delegated
/// frames and deadlines; each frame is the resident's to answer, on this member connection's own
/// resident connection (opened at its first frame).
fn serve_connection_shared(socket: UnixStream, pins: &Selection, shared: &SharedVerifier) -> Result<()> {
    if transport::peer_uid(&socket)? != pins.peer {
        return Err("consent controller peer UID mismatch".into());
    }
    socket.set_nonblocking(true).map_err(|e| e.to_string())?;
    let deadline = Arc::new(Mutex::new(Instant::now() + IO));
    let mut channel = Channel {
        socket,
        deadline: deadline.clone(),
        failed: Arc::new(AtomicBool::new(false)),
        writer: false,
        client: false,
    };
    let hello = transport::read_frame_bounded(&mut channel, TAG.len() + 64)
        .map_err(|e| e.to_string())?
        .ok_or("missing consent hello")?;
    if hello != pins.hello() {
        return Err("consent client binding mismatch".into());
    }
    transport::write_frame(&mut channel, &hello).map_err(|e| e.to_string())?;
    let mut session: Option<mini_sdk::local::Session> = None;
    loop {
        let frame = ingress(&mut channel, REPLAY, IO)?;
        if !allowed(&frame) {
            return Err("consent operation is not delegated".into());
        }
        if session.is_none() {
            session = Some(shared.connect()?);
        }
        let (answer, body) = session.as_mut().expect("resident session").exchange(frame[0], &frame[1..])?;
        if answer != frame[0] && answer != mini_sdk::consent::CONSENT_REFUSAL {
            return Err("unexpected consent verifier response".into());
        }
        *deadline.lock().map_err(|_| "deadline lock")? = Instant::now() + IO;
        transport::write_frame(&mut channel, &[&[answer], body.as_slice()].concat()).map_err(|e| e.to_string())?;
    }
}

#[cfg(target_os = "linux")]
pub(crate) fn serve(
    socket: &Path,
    executable: &Path,
    config: &Path,
    image: [u8; 32],
    settings: [u8; 32],
    controller: u32,
    anchors: &Path,
    idle: Option<Duration>,
    shared: Option<&Path>,
) -> Result<()> {
    if controller == 0 || controller == mini_sdk::private::euid() {
        return Err("consent requires distinct non-root controller UID".into());
    }
    if !executable.is_absolute() || !config.is_absolute() || !anchors.is_absolute() {
        return Err("consent service paths must be absolute".into());
    }
    if std::env::var("LISTEN_PID").ok() != Some(std::process::id().to_string())
        || std::env::var("LISTEN_FDS").ok().as_deref() != Some("1")
    {
        return Err("consent requires exactly one activated listener".into());
    }
    let listener = unsafe { UnixListener::from_raw_fd(3) };
    crate::public_proxy::validate_activated_listener(&listener, socket)?;
    let pins = Selection {
        socket: socket.to_path_buf(),
        peer: controller,
        executable: image,
        config: settings,
    };
    let backend = match shared {
        Some(dir) => Backend::Shared(Arc::new(SharedVerifier::start(executable, config, &pins, dir)?)),
        None => Backend::Own(Arc::new(Mutex::new(Worker::start(executable, config, &pins, anchors)?))),
    };
    // The worker keeps its warm verifier, as the member-side consent resident does: no idle exit
    // unless `--idle-seconds` asks for one (`idle` Some). Socket activation would start it again on
    // the next connection from the retained frontier, but that start is a provider launch and a
    // Store admission the member waits for.
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let slots = Arc::new(Slots::new(SERVED, WAITING));
    let last = Arc::new(Mutex::new(Instant::now()));
    loop {
        let stream = match listener.accept() {
            Ok((stream, _)) => stream,
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                let quiet = last.lock().map(|t| t.elapsed()).unwrap_or_default();
                if slots.idle() && idle.is_some_and(|idle| quiet > idle) {
                    return Ok(());
                }
                // Wait on the listener itself: a connection is served the moment it arrives.
                mini_sdk::private::wait_readable(listener.as_raw_fd(), Duration::from_secs(1));
                continue;
            }
            Err(e) => return Err(e.to_string()),
        };
        if transport::peer_uid(&stream)? != controller {
            continue;
        }
        if !slots.enter() {
            // The client reads this as a reset before its hello: nothing was sent, so it may retry.
            eprintln!("mini consent connection refused: {SERVED} served and {WAITING} waiting");
            continue;
        }
        if let Ok(mut t) = last.lock() {
            *t = Instant::now();
        }
        let (backend, slots, last, pins) = (backend.clone(), slots.clone(), last.clone(), pins.clone());
        std::thread::spawn(move || {
            if !slots.admit(Instant::now() + ADMISSION) {
                eprintln!("mini consent connection refused: none of {SERVED} served connections ended within {}s", ADMISSION.as_secs());
                return;
            }
            let served = match &backend {
                Backend::Own(worker) => serve_connection(stream, &pins, worker),
                Backend::Shared(shared) => serve_connection_shared(stream, &pins, shared),
            };
            if let Err(e) = served {
                eprintln!("mini consent connection: {e}")
            }
            if let Ok(mut t) = last.lock() {
                *t = Instant::now();
            }
            slots.release();
        });
    }
}

/// Connections served at once, and further connections that may wait for one. A client holds its
/// connection for as long as its process keeps a consent session, so a handful of concurrent
/// `mini` commands plus the standing ones fill a small bound; a connection past it waits (up to
/// `ADMISSION`) rather than being closed unserved, which a client saw as `Connection reset by peer`
/// on its hello and a controller's final write as `never submitted` (H1b).
const SERVED: usize = 16;
const WAITING: usize = 64;
const ADMISSION: Duration = Duration::from_secs(30);

struct Slots {
    served: AtomicUsize,
    waiting: AtomicUsize,
    limit: usize,
    queue: usize,
}

impl Slots {
    fn new(limit: usize, queue: usize) -> Self {
        Self { served: AtomicUsize::new(0), waiting: AtomicUsize::new(0), limit, queue }
    }
    /// A place to wait in; false when `queue` connections already wait.
    fn enter(&self) -> bool {
        if self.waiting.fetch_add(1, Ordering::AcqRel) >= self.queue {
            self.waiting.fetch_sub(1, Ordering::AcqRel);
            return false;
        }
        true
    }
    /// A served slot for a waiting connection, or false once `until` passes.
    fn admit(&self, until: Instant) -> bool {
        let taken = loop {
            let now = self.served.load(Ordering::Acquire);
            if now < self.limit && self.served.compare_exchange(now, now + 1, Ordering::AcqRel, Ordering::Acquire).is_ok() {
                break true;
            }
            if Instant::now() >= until {
                break false;
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        self.waiting.fetch_sub(1, Ordering::AcqRel);
        taken
    }
    fn release(&self) {
        self.served.fetch_sub(1, Ordering::AcqRel);
    }
    fn idle(&self) -> bool {
        self.served.load(Ordering::Acquire) == 0 && self.waiting.load(Ordering::Acquire) == 0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Split tenancy's thin relay: two member connections are answered by ONE shared consent
    /// resident (one provider start), each on its own resident connection, so the resident's Store
    /// re-check (233) precedes each connection's first frame; a client with other pins refuses.
    #[cfg(target_os = "linux")]
    #[test]
    fn shared_verifier_relays_each_member_connection_to_one_resident() {
        use std::os::unix::fs::PermissionsExt;
        let dir = PathBuf::from(format!("/tmp/mcp-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir(&dir).unwrap();
        let anchors = dir.join("a");
        fs::create_dir(&anchors).unwrap();
        fs::set_permissions(&anchors, fs::Permissions::from_mode(0o700)).unwrap();
        // A provider stand-in: logs each start and each operation, answers 233/228 with themselves,
        // 229 with an anchor, and any other frame with its own byte and "ok".
        let provider = dir.join("provider");
        fs::write(&provider, format!("#!/usr/bin/python3 -I\nimport sys,struct\nopen('{d}/starts','a').write('start\\n')\n\
i,o=sys.stdin.buffer,sys.stdout.buffer\nwhile True:\n  w=i.read(4)\n  if len(w)<4: break\n  f=i.read(struct.unpack('<I',w)[0])\n  op=f[0]\n  open('{d}/ops','a').write(str(op)+'\\n')\n  r=bytes([op])+(b'ANCHOR' if op==229 else b'' if op in (228,233) else b'ok')\n  o.write(struct.pack('<I',len(r))+r); o.flush()\n", d = dir.display())).unwrap();
        fs::set_permissions(&provider, fs::Permissions::from_mode(0o700)).unwrap();
        let config = dir.join("config.json");
        fs::write(&config, b"{\"x\":1}").unwrap();
        let pins = Selection {
            socket: dir.join("peer.sock"),
            peer: mini_sdk::private::euid(),
            executable: Sha256::digest(fs::read(&provider).unwrap()).into(),
            config: Sha256::digest(b"{\"x\":1}").into(),
        };
        // The operator's resident, already running (as its own unit would be).
        let (a, p, c) = (anchors.clone(), provider.clone(), config.clone());
        std::thread::spawn(move || mini_sdk::consent::serve_resident(&a, p, c, None));
        for _ in 0..2000 {
            if fs::read_dir(&anchors).unwrap().flatten().any(|e| e.file_name().to_string_lossy().ends_with(".sock")) {
                break;
            }
            std::thread::sleep(Duration::from_millis(5));
        }
        let shared = Arc::new(SharedVerifier::start(&provider, &config, &pins, &anchors).unwrap());
        for _ in 0..2 {
            let (mut client, server) = UnixStream::pair().unwrap();
            let (s, p) = (shared.clone(), pins.clone());
            let served = std::thread::spawn(move || serve_connection_shared(server, &p, &s));
            transport::write_frame(&mut client, &pins.hello()).unwrap();
            assert_eq!(transport::read_frame_bounded(&mut client, 1024).unwrap().unwrap(), pins.hello());
            transport::write_frame(&mut client, &[220, 1, 2, 3]).unwrap();
            assert_eq!(transport::read_frame_bounded(&mut client, 1024).unwrap().unwrap(), b"\xdcok".to_vec());
            drop(client);
            let _ = served.join();
        }
        assert_eq!(fs::read_to_string(dir.join("starts")).unwrap().lines().count(), 1, "one provider for every member");
        let ops: Vec<String> = fs::read_to_string(dir.join("ops")).unwrap().lines().map(str::to_owned).collect();
        assert_eq!(ops.iter().filter(|op| *op == "233").count(), 2, "a Store re-check per member connection: {ops:?}");
        // A member whose pins name another config is refused at the handshake.
        let (mut client, server) = UnixStream::pair().unwrap();
        let (s, p) = (shared.clone(), pins.clone());
        let served = std::thread::spawn(move || serve_connection_shared(server, &p, &s));
        let other = Selection { config: [9; 32], ..pins.clone() };
        transport::write_frame(&mut client, &other.hello()).unwrap();
        assert!(served.join().unwrap().is_err());
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn a_connection_past_the_served_bound_waits_for_a_slot_instead_of_being_dropped() {
        let slots = Slots::new(2, 3);
        for _ in 0..2 {
            assert!(slots.enter() && slots.admit(Instant::now()));
        }
        // The third finds both slots held: it waits its turn, then is admitted when one ends.
        assert!(slots.enter());
        std::thread::scope(|scope| {
            let waiter = scope.spawn(|| slots.admit(Instant::now() + Duration::from_secs(5)));
            std::thread::sleep(Duration::from_millis(50));
            slots.release();
            assert!(waiter.join().unwrap(), "the waiting connection is served once a slot frees");
        });
        // With every slot held again, a waiter that outlasts its admission window is refused.
        assert!(slots.enter());
        assert!(!slots.admit(Instant::now() + Duration::from_millis(30)));
        // Only `queue` connections wait at once; one more is refused at the door.
        assert!(slots.enter() && slots.enter() && slots.enter());
        assert!(!slots.enter());
        assert!(!slots.idle());
    }

    #[test]
    fn consent_proxy_explicit_invalid_environment_never_disappears() {
        use std::os::unix::ffi::OsStringExt;
        let invalid = std::ffi::OsString::from_vec(vec![0xff]);
        assert!(Selection::from_values([Some(invalid.clone()), None, None, None]).is_err());
        assert!(Selection::from_values(std::array::from_fn(|_| Some(invalid.clone()))).is_err());
        assert_eq!(
            Selection::from_values([None, None, None, None]).unwrap(),
            None
        );
    }
    #[test]
    fn consent_proxy_partial_frame_has_deadline_and_poisoned_connection() {
        let (read, mut write) = UnixStream::pair().unwrap();
        read.set_nonblocking(true).unwrap();
        let mut channel = Channel {
            socket: read,
            deadline: Arc::new(Mutex::new(Instant::now() + IO)),
            failed: Arc::new(AtomicBool::new(false)),
            writer: false,
            client: false,
        };
        write.write_all(&[1]).unwrap();
        let start = Instant::now();
        assert!(ingress(
            &mut channel,
            Duration::from_secs(10),
            Duration::from_millis(20)
        )
        .is_err());
        assert!(start.elapsed() < Duration::from_secs(1));
        assert!(channel.failed.load(Ordering::Acquire));
        assert!(channel.read(&mut [0]).is_err());
    }
    #[test]
    fn consent_proxy_only_full_consent_frames() {
        for op in 0..=255 {
            assert_eq!(allowed(&[op]), [220, 221, 222, 224, 226, 227, 236].contains(&op));
        }
        assert!(!allowed(&[236, 1]));
        assert!(!allowed(&[]));
        assert!(!allowed(&vec![220; CAP + 1]));
    }
    #[test]
    fn consent_proxy_anchor_exact_pins_and_nonempty() {
        let b = b"binding";
        let bytes = anchor_bytes(b, Some(b"frontier"));
        assert_eq!(
            decode_anchor(&bytes, b).unwrap(),
            Some(b"frontier".to_vec())
        );
        assert!(decode_anchor(&bytes, b"another").is_err());
        assert!(decode_anchor(&anchor_bytes(b, Some(b"")), b).is_err());
    }
    #[test]
    fn consent_proxy_selection_roundtrip_rejects_incomplete() {
        let p = Selection {
            socket: PathBuf::from("/private/consent.sock"),
            peer: 0,
            executable: [1; 32],
            config: [2; 32],
        };
        assert_eq!(
            Selection::from_record(&json!({"delegatedConsent":p.record()})).unwrap(),
            Some(p)
        );
        assert!(Selection::from_record(&json!({"delegatedConsent":{}})).is_err());
        assert!(digest(&"A".repeat(64)).is_err());
    }
}

#[cfg(test)]
#[path = "consent_proxy_client_tests.rs"]
mod client_tests;
