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
impl Lifeline {
    pub(crate) fn alive(&self) -> bool {
        if self.failed.load(Ordering::Acquire) {
            return false;
        }
        // POLLRDHUP is Linux/Android only; POLLHUP is always reported and a closed peer reads as POLLIN.
        #[cfg(any(target_os = "linux", target_os = "android"))]
        let events = libc::POLLIN | libc::POLLRDHUP;
        #[cfg(not(any(target_os = "linux", target_os = "android")))]
        let events = libc::POLLIN;
        let mut fd = libc::pollfd {
            fd: self.socket.as_raw_fd(),
            events,
            revents: 0,
        };
        // Between requests nothing is owed to us: readable or hung up means EOF (the worker or
        // its deadline closed the connection) or stray bytes (desynchronized); either is unusable.
        let ready = unsafe { libc::poll(&mut fd, 1, 0) };
        ready == 0 && fd.revents & (libc::POLLHUP | libc::POLLERR | libc::POLLNVAL) == 0
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
                .and_then(|_| fsio::sync_parent(&self.anchor));
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
                fsio::sync_parent(&marker)?;
                fsio::create_private(&anchor, &anchor_bytes(&binding, None))?;
                fsio::sync_parent(&anchor)?;
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
#[cfg(target_os = "linux")]
pub(crate) fn serve(
    socket: &Path,
    executable: &Path,
    config: &Path,
    image: [u8; 32],
    settings: [u8; 32],
    controller: u32,
    anchors: &Path,
    idle: Duration,
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
    let worker = Arc::new(Mutex::new(Worker::start(
        executable, config, &pins, anchors,
    )?));
    // Idle exit, as the member-side consent resident has (`mini_sdk::consent::RESIDENT_IDLE_S`):
    // with no connection open and none for `idle`, the service ends and its verifier with it.
    // Socket activation starts it again on the next connection, from the retained frontier
    // (`Worker::retain` after every admission), so one worker per hosted member holds memory
    // only while that member signs.
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let active = Arc::new(AtomicUsize::new(0));
    let last = Arc::new(Mutex::new(Instant::now()));
    loop {
        let stream = match listener.accept() {
            Ok((stream, _)) => stream,
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                let quiet = last.lock().map(|t| t.elapsed()).unwrap_or_default();
                if active.load(Ordering::Acquire) == 0 && quiet > idle {
                    return Ok(());
                }
                std::thread::sleep(Duration::from_millis(20));
                continue;
            }
            Err(e) => return Err(e.to_string()),
        };
        if transport::peer_uid(&stream)? != controller {
            continue;
        }
        if active.fetch_add(1, Ordering::AcqRel) >= 4 {
            active.fetch_sub(1, Ordering::AcqRel);
            continue;
        }
        if let Ok(mut t) = last.lock() {
            *t = Instant::now();
        }
        let (worker, active, last, pins) = (worker.clone(), active.clone(), last.clone(), pins.clone());
        std::thread::spawn(move || {
            if let Err(e) = serve_connection(stream, &pins, &worker) {
                eprintln!("mini consent connection: {e}")
            }
            if let Ok(mut t) = last.lock() {
                *t = Instant::now();
            }
            active.fetch_sub(1, Ordering::AcqRel);
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
            assert_eq!(allowed(&[op]), [220, 221, 222, 224, 226, 227].contains(&op));
        }
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
