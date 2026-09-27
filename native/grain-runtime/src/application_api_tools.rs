//! Bounded model-facing input for one operator-bound application API session.
//!
//! The selected name is a controller catalog entry, not an application ID or
//! authority grant. The controller supplies the fixed app, agent ticket,
//! session, purse and operation ID when it invokes the resident host. Mini's
//! event21 receiver remains the authority for any eventual physical call.
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs;
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, TryRecvError};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const MAX_TOOL_INPUT_BYTES: usize = 65_536;
const MAX_BODY_BYTES: usize = 24 * 1024;
const MAX_PATH_QUERY_BYTES: usize = 8192;
const MAX_HEADERS: usize = 128;
const MAX_FORWARD_FRAME: usize = 262_144;
const PROTOCOL: &str = "mini-spk-agent-api-v1";

const ORDINARY_HEADERS: &[&str] = &[
    "cookie",
    "accept",
    "accept-encoding",
    "content-type",
    "user-agent",
    "if-match",
    "if-none-match",
    "x-requested-with",
    "x-csrftoken",
    "x-csrf-token",
    "oc-total-length",
    "oc-chunk-size",
    "x-oc-mtime",
    "oc-fileid",
    "oc-chunked",
    "oc-checksum",
    "oc-chunk-offset",
    "oc-lazyops",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct HttpInput {
    pub application: String,
    pub method: String,
    pub path: String,
    pub query: String,
    pub ordered_headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        encoded.push(DIGITS[(byte >> 4) as usize] as char);
        encoded.push(DIGITS[(byte & 15) as usize] as char);
    }
    encoded
}

pub(crate) fn hello_request() -> Value {
    json!({"type":"hello","protocol":PROTOCOL})
}

pub(crate) fn inspect_request(operation_id: u64) -> Value {
    json!({"type":"inspect","protocol":PROTOCOL,"operation_id":operation_id.to_string()})
}

pub(crate) fn dispatch_request(operation_id: u64, input: &HttpInput) -> Value {
    json!({"type":"dispatch","protocol":PROTOCOL,"operation_id":operation_id.to_string(),
        "method":input.method,"path":input.path,"query":input.query,
        "headers":input.ordered_headers.iter().map(|(name,value)|
            json!({"name":name,"value":value})).collect::<Vec<_>>(),
        "body_hex":hex(&input.body)})
}

/// An operator-selected forward route to one fixed resident API session.
/// Resource IDs select what Mini must check; none is authority by itself.
/// Current generations, grants and the host invocation are checked at use.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct RoutePin {
    pub name: String,
    pub socket_path: PathBuf,
    pub host_uid: u32,
    pub host_unit: String,
    pub app_resource: String,
    pub app_generation: String,
    pub session_resource: String,
    pub session_generation: String,
    pub ticket_resource: String,
    pub participant_subject: String,
    pub purse_resource: String,
    pub dispatch_generation: String,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedBinding {
    pub protocol: String,
    pub app: String,
    pub app_generation: String,
    pub session: String,
    pub session_generation: String,
    pub subject: String,
    pub ticket: String,
    pub dispatch_task: String,
    pub dispatch_generation: String,
    pub host_unit: String,
    pub host_invocation: String,
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum HostReply {
    Binding {
        protocol: String,
        binding: FixedBinding,
        binding_sha256: String,
    },
    Http {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        status: u16,
        headers: Vec<HostHeader>,
        body_hex: String,
    },
    Refused {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        code: String,
    },
    Uncertain {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        phase: String,
    },
    Inspection {
        protocol: String,
        operation_id: String,
        binding_sha256: String,
        state: String,
    },
}

#[derive(Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub(crate) struct HostHeader {
    pub name: String,
    pub value: String,
}

fn lowercase_hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

impl FixedBinding {
    fn fingerprint(&self) -> Result<String, String> {
        if self.protocol != "mini-spk-agent-binding-v1"
            || ![
                &self.app,
                &self.app_generation,
                &self.session,
                &self.session_generation,
                &self.subject,
                &self.ticket,
                &self.dispatch_task,
                &self.dispatch_generation,
            ]
            .iter()
            .all(|value| canonical_decimal(value))
            || self.host_unit.is_empty()
            || self.host_unit.len() > 256
            || !clean_text(&self.host_unit)
            || self.host_invocation.len() != 32
            || !self
                .host_invocation
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err("application API host fixed binding is invalid".into());
        }
        let mut hash = Sha256::new();
        hash.update(b"DREGG/SPK-AGENT-API-BINDING/v1\0");
        hash.update(serde_json::to_vec(self).map_err(|error| error.to_string())?);
        Ok(format!("{:x}", hash.finalize()))
    }
}

/// The operator route pins the expected transport coordinates. A host-provided
/// binding is a transport identity check and never substitutes for event21's
/// fresh native admission of the current generations and request.
pub(crate) fn verify_binding(
    reply: HostReply,
    route: &RoutePin,
) -> Result<(String, String), String> {
    let HostReply::Binding {
        protocol,
        binding,
        binding_sha256,
    } = reply
    else {
        return Err("application API host did not return a binding".into());
    };
    if protocol != PROTOCOL
        || binding.app != route.app_resource
        || binding.app_generation != route.app_generation
        || binding.session != route.session_resource
        || binding.session_generation != route.session_generation
        || binding.subject != route.participant_subject
        || binding.ticket != route.ticket_resource
        || binding.dispatch_task != route.purse_resource
        || binding.dispatch_generation != route.dispatch_generation
        || binding.host_unit != route.host_unit
        || !lowercase_hex64(&binding_sha256)
        || binding.fingerprint()? != binding_sha256
    {
        return Err("application API host binding differs from current operator pins".into());
    }
    Ok((binding_sha256, binding.host_invocation))
}

pub(crate) fn parse_host_reply(value: Value) -> Result<HostReply, String> {
    serde_json::from_value(value).map_err(|error| format!("application API host reply: {error}"))
}

pub(crate) fn verify_operation_reply(
    reply: &HostReply,
    operation_id: u64,
    binding_sha256: &str,
) -> Result<(), String> {
    let (protocol, id, binding) = match reply {
        HostReply::Binding { .. } => {
            return Err("application API operation returned a binding instead of a result".into())
        }
        HostReply::Http {
            protocol,
            operation_id,
            binding_sha256,
            status,
            headers,
            body_hex,
        } => {
            if !(100..=599).contains(status)
                || headers.len() > 128
                || headers.iter().any(|header| {
                    header.name.is_empty()
                        || header.name.len() > 128
                        || !clean_text(&header.name)
                        || header.value.len() > 8192
                        || !clean_text(&header.value)
                })
                || body_hex.len() > MAX_FORWARD_FRAME * 2
                || body_hex.len() % 2 != 0
                || !body_hex
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err("application API HTTP result exceeds protocol bounds".into());
            }
            (protocol, operation_id, binding_sha256)
        }
        HostReply::Refused {
            protocol,
            operation_id,
            binding_sha256,
            code,
        } => {
            if code.is_empty() || code.len() > 128 || !clean_text(code) {
                return Err("application API refusal code is invalid".into());
            }
            (protocol, operation_id, binding_sha256)
        }
        HostReply::Uncertain {
            protocol,
            operation_id,
            binding_sha256,
            phase,
        } => {
            if phase.is_empty() || phase.len() > 128 || !clean_text(phase) {
                return Err("application API uncertainty phase is invalid".into());
            }
            (protocol, operation_id, binding_sha256)
        }
        HostReply::Inspection {
            protocol,
            operation_id,
            binding_sha256,
            state,
        } => {
            if !matches!(
                state.as_str(),
                "not-seen" | "received" | "delivery-requested" | "definite" | "uncertain"
            ) {
                return Err("application API inspection state is invalid".into());
            }
            (protocol, operation_id, binding_sha256)
        }
    };
    let expected_id = operation_id.to_string();
    if protocol != PROTOCOL || id != &expected_id || binding != binding_sha256 {
        return Err("application API operation reply identity differs".into());
    }
    Ok(())
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 20
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
        && value.parse::<u64>().is_ok()
}

pub(crate) fn validate_routes(
    routes: &[RoutePin],
    purse_resource: &str,
    participant_subject: &str,
    host_uid: u32,
) -> Result<(), String> {
    if routes.len() > 16
        || !canonical_decimal(purse_resource)
        || !canonical_decimal(participant_subject)
    {
        return Err("application API route count or dispatch authority is invalid".into());
    }
    for (index, route) in routes.iter().enumerate() {
        if route.name.is_empty()
            || route.name.len() > 64
            || !route.name.ends_with("-app")
            || !route
                .name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            || routes[..index].iter().any(|prior| prior.name == route.name)
            || !route.socket_path.is_absolute()
            || route.host_uid != host_uid
            || route.host_uid == 0
            || route.host_unit.is_empty()
            || route.host_unit.len() > 256
            || !clean_text(&route.host_unit)
            || route.purse_resource != purse_resource
            || route.participant_subject != participant_subject
        {
            return Err("application API route differs from operator dispatch binding".into());
        }
        for value in [
            &route.app_resource,
            &route.session_resource,
            &route.ticket_resource,
            &route.participant_subject,
            &route.purse_resource,
        ] {
            if !canonical_decimal(value) || value == "0" {
                return Err("application API route resource identity is not canonical".into());
            }
        }
        if [
            &route.app_generation,
            &route.session_generation,
            &route.dispatch_generation,
        ]
        .iter()
        .any(|generation| !canonical_decimal(generation))
        {
            return Err("application API route generation is not canonical".into());
        }
    }
    Ok(())
}

/// `BeforeSend` is the only transport result that proves this invocation did
/// not send any request byte. Once a byte crosses the socket, an absent reply
/// is uncertain and must be inspected by the same durable operation ID.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum TransportError {
    BeforeSend(String),
    Uncertain(String),
}

/// A brief first-byte barrier shared with the hard-interrupt callback. If a
/// send has crossed before cancellation, the retained attempt is uncertain;
/// no later invocation gets a second dispatch under that operation ID.
pub(crate) struct ForwardSendGate {
    stopped: Mutex<bool>,
}

impl ForwardSendGate {
    pub(crate) fn new() -> Self {
        Self {
            stopped: Mutex::new(false),
        }
    }

    pub(crate) fn cancel(&self) {
        if let Ok(mut stopped) = self.stopped.lock() {
            *stopped = true;
        }
    }

    pub(crate) fn reset(&self) -> Result<(), String> {
        let mut stopped = self
            .stopped
            .lock()
            .map_err(|_| "application API send gate poisoned")?;
        *stopped = false;
        Ok(())
    }
}

fn first_write(
    stream: &mut UnixStream,
    frame: &[u8],
    gate: &ForwardSendGate,
    cancelled: &AtomicBool,
    deadline: Instant,
) -> Result<usize, TransportError> {
    loop {
        if Instant::now() >= deadline {
            return Err(TransportError::BeforeSend(
                "application API send deadline".into(),
            ));
        }
        let stopped = gate
            .stopped
            .lock()
            .map_err(|_| TransportError::BeforeSend("application API send gate poisoned".into()))?;
        if *stopped || cancelled.load(Ordering::SeqCst) {
            return Err(TransportError::BeforeSend(
                "application API send was cancelled".into(),
            ));
        }
        let result = stream.write(frame);
        drop(stopped);
        match result {
            Ok(0) => {
                return Err(TransportError::BeforeSend(
                    "application API socket closed".into(),
                ))
            }
            Ok(count) => return Ok(count),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                thread::sleep(Duration::from_millis(2));
            }
            Err(error) => {
                return Err(TransportError::BeforeSend(format!(
                    "application API first write: {error}"
                )))
            }
        }
    }
}

fn transfer(
    stream: &mut UnixStream,
    bytes: &mut [u8],
    write: bool,
    deadline: Instant,
    cancelled: Option<&AtomicBool>,
) -> (usize, io::Result<()>) {
    let mut offset = 0;
    while offset < bytes.len() {
        if cancelled.is_some_and(|flag| flag.load(Ordering::SeqCst)) {
            return (
                offset,
                Err(io::Error::new(
                    io::ErrorKind::Interrupted,
                    "application API dispatch cancelled after first byte",
                )),
            );
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return (
                offset,
                Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "application API deadline",
                )),
            );
        }
        let result = if write {
            stream.write(&bytes[offset..])
        } else {
            stream.read(&mut bytes[offset..])
        };
        match result {
            Ok(0) => {
                return (
                    offset,
                    Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "application API socket closed",
                    )),
                )
            }
            Ok(count) => offset += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(2));
            }
            Err(error) => {
                return (
                    offset,
                    Err(io::Error::new(
                        error.kind(),
                        format!("socket transfer: {error}"),
                    )),
                )
            }
        }
    }
    (offset, Ok(()))
}

fn connect_nonblocking(
    socket: &Path,
    deadline: Instant,
    cancelled: Option<&AtomicBool>,
) -> Result<UnixStream, TransportError> {
    if cancelled.is_some_and(|flag| flag.load(Ordering::SeqCst)) {
        return Err(TransportError::BeforeSend(
            "application API host connect cancelled".into(),
        ));
    }
    if Instant::now() >= deadline {
        return Err(TransportError::BeforeSend(
            "application API host connect deadline".into(),
        ));
    }
    let path = socket.as_os_str().as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if path.is_empty() || path.len() >= address.sun_path.len() || path.contains(&0) {
        return Err(TransportError::BeforeSend(
            "application API Unix socket path exceeds native sockaddr".into(),
        ));
    }
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    for (slot, byte) in address.sun_path.iter_mut().zip(path) {
        *slot = *byte as libc::c_char;
    }
    let length = std::mem::offset_of!(libc::sockaddr_un, sun_path) + path.len() + 1;
    #[cfg(target_os = "macos")]
    {
        address.sun_len = u8::try_from(length).map_err(|_| {
            TransportError::BeforeSend("application API Darwin socket address too long".into())
        })?;
    }
    // Linux creates the fd close-on-exec atomically. Darwin has no libc
    // SOCK_CLOEXEC; set FD_CLOEXEC immediately below before connect. Its
    // socket/fcntl gap requires no concurrent child spawn for strict custody.
    #[cfg(target_os = "linux")]
    let socket_type = libc::SOCK_STREAM | libc::SOCK_CLOEXEC;
    #[cfg(target_os = "macos")]
    let socket_type = libc::SOCK_STREAM;
    let raw = unsafe { libc::socket(libc::AF_UNIX, socket_type, 0) };
    if raw < 0 {
        return Err(TransportError::BeforeSend(format!(
            "application API socket create: {}",
            io::Error::last_os_error()
        )));
    }
    let owned = unsafe { OwnedFd::from_raw_fd(raw) };
    #[cfg(target_os = "macos")]
    {
        let descriptor_flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFD) };
        if descriptor_flags < 0
            || unsafe {
                libc::fcntl(
                    owned.as_raw_fd(),
                    libc::F_SETFD,
                    descriptor_flags | libc::FD_CLOEXEC,
                )
            } != 0
        {
            return Err(TransportError::BeforeSend(format!(
                "application API socket close-on-exec: {}",
                io::Error::last_os_error()
            )));
        }
    }
    let flags = unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_GETFL) };
    if flags < 0
        || unsafe { libc::fcntl(owned.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) } != 0
    {
        return Err(TransportError::BeforeSend(format!(
            "application API socket nonblocking mode: {}",
            io::Error::last_os_error()
        )));
    }
    let status = unsafe {
        libc::connect(
            owned.as_raw_fd(),
            (&raw const address).cast(),
            length as libc::socklen_t,
        )
    };
    if status == 0 {
        return Ok(UnixStream::from(owned));
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::EAGAIN) {
        return Err(TransportError::BeforeSend(
            "application API host connect backlog is full".into(),
        ));
    }
    if !matches!(error.raw_os_error(), Some(libc::EINPROGRESS | libc::EINTR)) {
        return Err(TransportError::BeforeSend(format!(
            "application API host connect: {error}"
        )));
    }
    loop {
        if cancelled.is_some_and(|flag| flag.load(Ordering::SeqCst)) {
            return Err(TransportError::BeforeSend(
                "application API host connect cancelled".into(),
            ));
        }
        if Instant::now() >= deadline {
            return Err(TransportError::BeforeSend(
                "application API host connect deadline".into(),
            ));
        }
        let mut ready = libc::pollfd {
            fd: owned.as_raw_fd(),
            events: libc::POLLOUT,
            revents: 0,
        };
        let polled = unsafe { libc::poll(&mut ready, 1, 20) };
        if polled == 0
            || (polled < 0 && io::Error::last_os_error().kind() == io::ErrorKind::Interrupted)
        {
            continue;
        }
        if polled < 0 {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect poll: {}",
                io::Error::last_os_error()
            )));
        }
        let mut socket_error: libc::c_int = 0;
        let mut size = std::mem::size_of::<libc::c_int>() as libc::socklen_t;
        if unsafe {
            libc::getsockopt(
                owned.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_ERROR,
                (&raw mut socket_error).cast(),
                &mut size,
            )
        } != 0
            || size as usize != std::mem::size_of::<libc::c_int>()
        {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect result: {}",
                io::Error::last_os_error()
            )));
        }
        if socket_error != 0 {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect: {}",
                io::Error::from_raw_os_error(socket_error)
            )));
        }
        // A saturated Unix listener can report POLLOUT with SO_ERROR=0 while
        // connect is still pending. Only a named peer proves completion.
        let mut peer: libc::sockaddr_storage = unsafe { std::mem::zeroed() };
        let mut peer_len = std::mem::size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if unsafe { libc::getpeername(owned.as_raw_fd(), (&raw mut peer).cast(), &mut peer_len) }
            == 0
        {
            return Ok(UnixStream::from(owned));
        }
        let error = io::Error::last_os_error();
        if error.raw_os_error() != Some(libc::ENOTCONN) {
            return Err(TransportError::BeforeSend(format!(
                "application API host connect peer: {error}"
            )));
        }
        std::thread::sleep(Duration::from_millis(20));
    }
}

#[cfg(target_os = "linux")]
fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    use std::mem::{size_of, MaybeUninit};
    use std::os::fd::AsRawFd;
    let mut credential = MaybeUninit::<libc::ucred>::uninit();
    let mut len = size_of::<libc::ucred>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            credential.as_mut_ptr().cast(),
            &mut len,
        )
    } != 0
        || len as usize != size_of::<libc::ucred>()
    {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { credential.assume_init() }.uid)
}

#[cfg(target_os = "macos")]
fn peer_uid(stream: &UnixStream) -> io::Result<u32> {
    use std::os::fd::AsRawFd;
    let mut uid = 0;
    let mut gid = 0;
    if unsafe { libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(uid)
}

/// Exactly one request frame and at most one response frame. The caller must
/// durably retain its operation ID and request bytes before entering here.
/// This function performs no retry, including after a lost response.
pub(crate) fn exchange_once(
    socket: &Path,
    expected_host_uid: u32,
    request: &Value,
    deadline: Instant,
) -> Result<Value, TransportError> {
    exchange_once_guarded(socket, expected_host_uid, request, deadline, None, None)
}

fn check_socket_ancestors(socket: &Path, expected_host_uid: u32) -> Result<(), TransportError> {
    let parent = socket
        .parent()
        .ok_or_else(|| TransportError::BeforeSend("application API socket has no parent".into()))?;
    for (depth, ancestor) in parent.ancestors().enumerate() {
        let metadata = fs::symlink_metadata(ancestor).map_err(|error| {
            TransportError::BeforeSend(format!("application API socket ancestor: {error}"))
        })?;
        let safe_sticky = depth > 0 && metadata.uid() == 0 && metadata.mode() & 0o1000 != 0;
        if !metadata.file_type().is_dir()
            || metadata.file_type().is_symlink()
            || (metadata.mode() & 0o022 != 0 && !safe_sticky)
            || !matches!(metadata.uid(), 0)
                && metadata.uid() != expected_host_uid
                && metadata.uid() != unsafe { libc::geteuid() }
        {
            return Err(TransportError::BeforeSend(format!(
                "application API socket ancestor {} is not a protected directory",
                ancestor.display()
            )));
        }
    }
    Ok(())
}

fn exchange_once_guarded(
    socket: &Path,
    expected_host_uid: u32,
    request: &Value,
    deadline: Instant,
    send_gate: Option<(&ForwardSendGate, &AtomicBool)>,
    cancelled: Option<&AtomicBool>,
) -> Result<Value, TransportError> {
    let encoded = serde_json::to_vec(request)
        .map_err(|error| TransportError::BeforeSend(error.to_string()))?;
    if encoded.is_empty() || encoded.len() > MAX_FORWARD_FRAME {
        return Err(TransportError::BeforeSend(
            "application API forward request exceeds frame bound".into(),
        ));
    }
    check_socket_ancestors(socket, expected_host_uid)?;
    let before = fs::symlink_metadata(socket)
        .map_err(|error| TransportError::BeforeSend(format!("host socket: {error}")))?;
    if !before.file_type().is_socket() {
        return Err(TransportError::BeforeSend(
            "application API forward path is not a socket".into(),
        ));
    }
    let mut stream = connect_nonblocking(socket, deadline, cancelled)?;
    if peer_uid(&stream)
        .map_err(|error| TransportError::BeforeSend(format!("host peer UID: {error}")))?
        != expected_host_uid
    {
        return Err(TransportError::BeforeSend(
            "application API host peer UID differs".into(),
        ));
    }
    let after = fs::symlink_metadata(socket)
        .map_err(|error| TransportError::BeforeSend(format!("host socket recheck: {error}")))?;
    if !after.file_type().is_socket() || (before.dev(), before.ino()) != (after.dev(), after.ino())
    {
        return Err(TransportError::BeforeSend(
            "application API host socket identity changed".into(),
        ));
    }
    stream
        .set_nonblocking(true)
        .map_err(|error| TransportError::BeforeSend(format!("host socket mode: {error}")))?;
    let mut frame = Vec::with_capacity(encoded.len() + 4);
    frame.extend_from_slice(&(encoded.len() as u32).to_be_bytes());
    frame.extend_from_slice(&encoded);
    let initially_written = if let Some((gate, cancelled)) = send_gate {
        first_write(&mut stream, &frame, gate, cancelled, deadline)?
    } else {
        0
    };
    let (remaining, sent) = if initially_written == frame.len() {
        (0, Ok(()))
    } else {
        if let Some((_, cancelled)) = send_gate {
            if cancelled.load(Ordering::SeqCst) {
                return Err(TransportError::Uncertain(
                    "application API send cancelled after first byte".into(),
                ));
            }
        }
        transfer(
            &mut stream,
            &mut frame[initially_written..],
            true,
            deadline,
            cancelled,
        )
    };
    let written = initially_written + remaining;
    if let Err(error) = sent {
        return Err(if written == 0 {
            TransportError::BeforeSend(format!("host request was not sent: {error}"))
        } else {
            TransportError::Uncertain(format!("host request delivery uncertain: {error}"))
        });
    }
    let mut size = [0_u8; 4];
    transfer(&mut stream, &mut size, false, deadline, cancelled)
        .1
        .map_err(|error| TransportError::Uncertain(format!("host reply header: {error}")))?;
    let size = u32::from_be_bytes(size) as usize;
    if size == 0 || size > MAX_FORWARD_FRAME {
        return Err(TransportError::Uncertain(
            "host reply exceeds frame bound".into(),
        ));
    }
    let mut payload = vec![0_u8; size];
    transfer(&mut stream, &mut payload, false, deadline, cancelled)
        .1
        .map_err(|error| {
            TransportError::Uncertain(format!("host reply payload ({size} bytes): {error}"))
        })?;
    // Decode against the strict tagged wire before admitting a Value. Direct
    // typed decoding rejects duplicate fields that Value would collapse.
    serde_json::from_slice::<HostReply>(&payload)
        .map_err(|error| TransportError::Uncertain(format!("host reply wire: {error}")))?;
    serde_json::from_slice(&payload)
        .map_err(|error| TransportError::Uncertain(format!("host reply JSON: {error}")))
}

/// A forward call runs on an I/O-only thread. It owns no Mini key or Runtime
/// journal, so the controller thread remains free to service the host's
/// reverse dispatch-custody requests while this one-shot call is pending.
pub(crate) struct PendingExchange {
    result: Receiver<Result<Value, TransportError>>,
}

impl PendingExchange {
    pub(crate) fn poll(&self) -> Option<Result<Value, TransportError>> {
        match self.result.try_recv() {
            Ok(result) => Some(result),
            Err(TryRecvError::Empty) => None,
            Err(TryRecvError::Disconnected) => Some(Err(TransportError::Uncertain(
                "application API I/O worker exited without a result".into(),
            ))),
        }
    }
}

pub(crate) fn start_exchange_once(
    socket: &Path,
    expected_host_uid: u32,
    request: Value,
    deadline: Instant,
    cancelled: Arc<AtomicBool>,
) -> Result<PendingExchange, TransportError> {
    let (reply, result) = mpsc::channel();
    let socket = socket.to_owned();
    thread::Builder::new()
        .name("mini-application-api".into())
        .spawn(move || {
            let _ = reply.send(exchange_once_guarded(
                &socket,
                expected_host_uid,
                &request,
                deadline,
                None,
                Some(&cancelled),
            ));
        })
        .map_err(|error| {
            TransportError::BeforeSend(format!("application API worker spawn: {error}"))
        })?;
    Ok(PendingExchange { result })
}

pub(crate) fn start_dispatch_once(
    socket: &Path,
    expected_host_uid: u32,
    request: Value,
    deadline: Instant,
    send_gate: Arc<ForwardSendGate>,
    cancelled: Arc<AtomicBool>,
) -> Result<PendingExchange, TransportError> {
    let (reply, result) = mpsc::channel();
    let socket = socket.to_owned();
    thread::Builder::new()
        .name("mini-application-api-dispatch".into())
        .spawn(move || {
            let outcome = exchange_once_guarded(
                &socket,
                expected_host_uid,
                &request,
                deadline,
                Some((&send_gate, &cancelled)),
                Some(&cancelled),
            );
            let _ = reply.send(outcome);
        })
        .map_err(|error| {
            TransportError::BeforeSend(format!("application API dispatch worker spawn: {error}"))
        })?;
    Ok(PendingExchange { result })
}

fn clean_text(value: &str) -> bool {
    !value
        .bytes()
        .any(|byte| matches!(byte, 0 | 10 | 13 | 127) || (byte < 0x20 && byte != b'\t'))
}

fn decode_hex(value: &str) -> Result<Vec<u8>, String> {
    if !value.len().is_multiple_of(2) || value.len() > 2 * MAX_BODY_BYTES {
        return Err("application API bodyHex exceeds bound or has odd length".into());
    }
    let mut body = Vec::with_capacity(value.len() / 2);
    for pair in value.as_bytes().chunks_exact(2) {
        let digit = |byte: u8| -> Option<u8> {
            match byte {
                b'0'..=b'9' => Some(byte - b'0'),
                b'a'..=b'f' => Some(byte - b'a' + 10),
                _ => None,
            }
        };
        body.push(
            digit(pair[0])
                .zip(digit(pair[1]))
                .map(|(high, low)| high * 16 + low)
                .ok_or("application API bodyHex is not lowercase hex")?,
        );
    }
    Ok(body)
}

/// Parse a single MCP tool call against operator-selected names. This is a
/// preflight bound only; it never authorizes a session, dispatch or charge.
pub(crate) fn parse_input(
    arguments: &Value,
    allowed_applications: &[String],
) -> Result<HttpInput, String> {
    let encoded = serde_json::to_vec(arguments).map_err(|error| error.to_string())?;
    if encoded.len() > MAX_TOOL_INPUT_BYTES {
        return Err("application API tool input exceeds MCP frame bound".into());
    }
    let object = arguments
        .as_object()
        .ok_or("application API arguments must be an object")?;
    if object.len() != 6
        || object.keys().any(|key| {
            !matches!(
                key.as_str(),
                "application" | "method" | "path" | "query" | "headers" | "bodyHex"
            )
        })
    {
        return Err("application API arguments have noncanonical fields".into());
    }
    let string = |key: &str| -> Result<&str, String> {
        object
            .get(key)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("application API {key} must be a string"))
    };
    let application = string("application")?;
    if !allowed_applications.iter().any(|name| name == application) {
        return Err("application API name is not operator-selected".into());
    }
    let method = string("method")?;
    if !matches!(method, "GET" | "HEAD" | "POST" | "PUT" | "PATCH" | "DELETE") {
        return Err("application API method is unavailable".into());
    }
    let path = string("path")?;
    let query = string("query")?;
    if path.starts_with('/')
        || path.contains(['?', '#'])
        || query.contains('#')
        || !clean_text(path)
        || !clean_text(query)
        || path.len() + query.len() > MAX_PATH_QUERY_BYTES
    {
        return Err("application API path or query is outside native profile".into());
    }
    let headers = object
        .get("headers")
        .and_then(Value::as_array)
        .ok_or("application API headers must be an array")?;
    if headers.len() > MAX_HEADERS {
        return Err("application API header count exceeds native profile".into());
    }
    let mut ordered_headers = Vec::with_capacity(headers.len());
    for header in headers {
        let fields = header
            .as_object()
            .ok_or("application API header must be an object")?;
        if fields.len() != 2 || !fields.contains_key("name") || !fields.contains_key("value") {
            return Err("application API header fields are noncanonical".into());
        }
        let name = fields
            .get("name")
            .and_then(Value::as_str)
            .ok_or("application API header name must be a string")?;
        let value = fields
            .get("value")
            .and_then(Value::as_str)
            .ok_or("application API header value must be a string")?;
        if !ORDINARY_HEADERS.contains(&name)
            || name.len() > 128
            || value.len() > 8192
            || !clean_text(value)
        {
            return Err("application API header is outside native ordinary-header profile".into());
        }
        ordered_headers.push((name.to_owned(), value.to_owned()));
    }
    let body = decode_hex(string("bodyHex")?)?;
    if matches!(method, "GET" | "HEAD" | "DELETE") && !body.is_empty() {
        return Err("application API body is unavailable for this method".into());
    }
    Ok(HttpInput {
        application: application.to_owned(),
        method: method.to_owned(),
        path: path.to_owned(),
        query: query.to_owned(),
        ordered_headers,
        body,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::net::UnixListener;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::thread;

    static NEXT_SOCKET: AtomicUsize = AtomicUsize::new(1);

    fn socket_path() -> std::path::PathBuf {
        let directory = std::env::temp_dir().join(format!(
            "mini-application-api-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        fs::create_dir(&directory).unwrap();
        fs::set_permissions(&directory, fs::Permissions::from_mode(0o700)).unwrap();
        fs::canonicalize(directory).unwrap().join("agent.sock")
    }

    fn remove_socket(path: &Path) {
        if path.exists() {
            fs::remove_file(path).unwrap();
        }
        fs::remove_dir(path.parent().unwrap()).unwrap();
    }

    fn request() -> Value {
        json!({"application":"workroom", "method":"POST", "path":"repo.git/git-receive-pack",
            "query":"service=git-receive-pack", "headers":[{"name":"content-type","value":"application/x-git-receive-pack-request"}],
            "bodyHex":"000102ff"})
    }

    #[test]
    fn preserves_exact_bounded_http_input_without_model_authority_fields() {
        let parsed = parse_input(&request(), &["workroom".into()]).unwrap();
        assert_eq!(parsed.body, [0, 1, 2, 255]);
        assert_eq!(parsed.ordered_headers[0].0, "content-type");
        assert_eq!(parsed.path, "repo.git/git-receive-pack");
        assert!(parse_input(&request(), &["other".into()]).is_err());
        let mut extra = request();
        extra["ticketResource"] = json!("17");
        assert!(parse_input(&extra, &["workroom".into()]).is_err());
        let wire = dispatch_request(7, &parsed);
        assert_eq!(wire["protocol"], PROTOCOL);
        assert_eq!(wire["operation_id"], "7");
        assert_eq!(wire["body_hex"], "000102ff");
        assert_eq!(wire["headers"][0]["name"], "content-type");
        assert!(wire.get("ticket").is_none());
        assert_eq!(hello_request()["type"], "hello");
        assert_eq!(inspect_request(7)["operation_id"], "7");
    }

    #[test]
    fn refuses_generated_headers_ambiguous_paths_and_body_mismatch() {
        let mut input = request();
        input["headers"] = json!([{"name":"x-sandstorm-permissions","value":"read,write"}]);
        assert!(parse_input(&input, &["workroom".into()]).is_err());
        input = request();
        input["path"] = json!("/repo.git");
        assert!(parse_input(&input, &["workroom".into()]).is_err());
        input = request();
        input["method"] = json!("GET");
        assert!(parse_input(&input, &["workroom".into()]).is_err());
        input = request();
        input["bodyHex"] = json!("00FF");
        assert!(parse_input(&input, &["workroom".into()]).is_err());
    }

    #[test]
    fn route_requires_fixed_purse_subject_and_unique_named_app() {
        let route = RoutePin {
            name: "workroom-app".into(),
            socket_path: "/tmp/host-agent.sock".into(),
            host_uid: 1001,
            host_unit: "spk-host@example.service".into(),
            app_resource: "6100".into(),
            app_generation: "2".into(),
            session_resource: "6209".into(),
            session_generation: "3".into(),
            ticket_resource: "6408".into(),
            participant_subject: "8".into(),
            purse_resource: "6500".into(),
            dispatch_generation: "4".into(),
        };
        assert!(validate_routes(std::slice::from_ref(&route), "6500", "8", 1001).is_ok());
        assert!(validate_routes(&[route.clone(), route.clone()], "6500", "8", 1001).is_err());
        assert!(validate_routes(std::slice::from_ref(&route), "6501", "8", 1001).is_err());
        let mut changed = route;
        changed.ticket_resource = "06408".into();
        assert!(validate_routes(&[changed], "6500", "8", 1001).is_err());
    }

    #[test]
    fn forward_exchange_sends_one_exact_frame_and_requires_one_reply() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut size = [0_u8; 4];
            stream.read_exact(&mut size).unwrap();
            let mut payload = vec![0_u8; u32::from_be_bytes(size) as usize];
            stream.read_exact(&mut payload).unwrap();
            assert_eq!(
                serde_json::from_slice::<Value>(&payload).unwrap(),
                json!({"type":"dispatch","operation_id":"7"})
            );
            let reply = serde_json::to_vec(&json!({"type":"refused","protocol":PROTOCOL,
                "operation_id":"7","binding_sha256":"0".repeat(64),"code":"disabled"}))
            .unwrap();
            stream
                .write_all(&(reply.len() as u32).to_be_bytes())
                .unwrap();
            stream.write_all(&reply).unwrap();
        });
        let pending = start_exchange_once(
            &path,
            unsafe { libc::geteuid() },
            json!({"type":"dispatch","operation_id":"7"}),
            Instant::now() + Duration::from_secs(2),
            Arc::new(AtomicBool::new(false)),
        )
        .unwrap();
        let reply = loop {
            if let Some(result) = pending.poll() {
                break result.unwrap();
            }
            thread::sleep(Duration::from_millis(2));
        };
        assert_eq!(reply["operation_id"], "7");
        server.join().unwrap();
        remove_socket(&path);
    }

    #[test]
    fn lost_reply_is_uncertain_and_no_connect_is_definite_no_send() {
        let absent = socket_path();
        assert!(matches!(
            exchange_once(
                &absent,
                unsafe { libc::geteuid() },
                &json!({"type":"inspect","operation_id":"8"}),
                Instant::now() + Duration::from_secs(2),
            ),
            Err(TransportError::BeforeSend(_))
        ));
        remove_socket(&absent);
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut size = [0_u8; 4];
            stream.read_exact(&mut size).unwrap();
            let mut payload = vec![0_u8; u32::from_be_bytes(size) as usize];
            stream.read_exact(&mut payload).unwrap();
        });
        assert!(matches!(
            exchange_once(
                &path,
                unsafe { libc::geteuid() },
                &json!({"type":"dispatch","operation_id":"8"}),
                Instant::now() + Duration::from_secs(2),
            ),
            Err(TransportError::Uncertain(_))
        ));
        server.join().unwrap();
        remove_socket(&path);
    }

    #[test]
    fn fixed_binding_hash_and_operation_reply_match_exact_operator_coordinates() {
        let route = RoutePin {
            name: "workroom-app".into(),
            socket_path: "/tmp/host-agent.sock".into(),
            host_uid: 1001,
            host_unit: "spk-host@example.service".into(),
            app_resource: "6100".into(),
            app_generation: "2".into(),
            session_resource: "6209".into(),
            session_generation: "3".into(),
            ticket_resource: "6408".into(),
            participant_subject: "8".into(),
            purse_resource: "6500".into(),
            dispatch_generation: "4".into(),
        };
        let binding = FixedBinding {
            protocol: "mini-spk-agent-binding-v1".into(),
            app: "6100".into(),
            app_generation: "2".into(),
            session: "6209".into(),
            session_generation: "3".into(),
            subject: "8".into(),
            ticket: "6408".into(),
            dispatch_task: "6500".into(),
            dispatch_generation: "4".into(),
            host_unit: "spk-host@example.service".into(),
            host_invocation: "0123456789abcdef0123456789abcdef".into(),
        };
        let digest = binding.fingerprint().unwrap();
        assert_eq!(digest.len(), 64);
        let reply = HostReply::Binding {
            protocol: PROTOCOL.into(),
            binding: binding.clone(),
            binding_sha256: digest.clone(),
        };
        assert_eq!(
            verify_binding(reply, &route).unwrap(),
            (digest.clone(), binding.host_invocation.clone())
        );
        let reply = parse_host_reply(json!({"type":"inspection","protocol":PROTOCOL,
            "operation_id":"7","binding_sha256":digest,"state":"delivery-requested"}))
        .unwrap();
        verify_operation_reply(&reply, 7, &binding.fingerprint().unwrap()).unwrap();
        assert!(verify_operation_reply(&reply, 8, &binding.fingerprint().unwrap()).is_err());
        let wrong = HostReply::Binding {
            protocol: PROTOCOL.into(),
            binding: FixedBinding {
                session_generation: "4".into(),
                ..binding
            },
            binding_sha256: digest,
        };
        assert!(verify_binding(wrong, &route).is_err());
    }

    #[test]
    fn cancelled_forward_gate_prevents_first_request_byte() {
        let (mut sender, mut receiver) = UnixStream::pair().unwrap();
        receiver.set_nonblocking(true).unwrap();
        let gate = ForwardSendGate::new();
        let cancelled = AtomicBool::new(false);
        gate.cancel();
        assert!(matches!(
            first_write(
                &mut sender,
                b"request",
                &gate,
                &cancelled,
                Instant::now() + Duration::from_secs(1)
            ),
            Err(TransportError::BeforeSend(_))
        ));
        let mut one = [0_u8; 1];
        assert_eq!(
            receiver.read(&mut one).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        gate.reset().unwrap();
        cancelled.store(true, Ordering::SeqCst);
        assert!(matches!(
            first_write(
                &mut sender,
                b"request",
                &gate,
                &cancelled,
                Instant::now() + Duration::from_secs(1)
            ),
            Err(TransportError::BeforeSend(_))
        ));
        assert_eq!(
            receiver.read(&mut one).unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
    }

    #[test]
    fn duplicate_reply_fields_remain_uncertain_instead_of_value_collapsing() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut size = [0_u8; 4];
            stream.read_exact(&mut size).unwrap();
            let mut request = vec![0_u8; u32::from_be_bytes(size) as usize];
            stream.read_exact(&mut request).unwrap();
            let reply = br#"{"type":"refused","protocol":"mini-spk-agent-api-v1","operation_id":"7","operation_id":"8","binding_sha256":"0000000000000000000000000000000000000000000000000000000000000000","code":"disabled"}"#;
            stream
                .write_all(&(reply.len() as u32).to_be_bytes())
                .unwrap();
            stream.write_all(reply).unwrap();
        });
        assert!(matches!(
            exchange_once(
                &path,
                unsafe { libc::geteuid() },
                &inspect_request(7),
                Instant::now() + Duration::from_secs(2)
            ),
            Err(TransportError::Uncertain(_))
        ));
        server.join().unwrap();
        remove_socket(&path);
    }

    #[test]
    fn hard_eof_before_dispatch_first_byte_leaves_no_host_request() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        let gate = Arc::new(ForwardSendGate::new());
        let cancelled = Arc::new(AtomicBool::new(false));
        let barrier = gate.stopped.lock().unwrap();
        let pending = start_dispatch_once(
            &path,
            unsafe { libc::geteuid() },
            dispatch_request(9, &parse_input(&request(), &["workroom".into()]).unwrap()),
            Instant::now() + Duration::from_secs(2),
            gate.clone(),
            cancelled.clone(),
        )
        .unwrap();
        // The worker may connect, but the controller's hard interrupt sets
        // cancellation before it can pass the first-byte gate.
        cancelled.store(true, Ordering::SeqCst);
        drop(barrier);
        gate.cancel();
        let outcome = loop {
            if let Some(outcome) = pending.poll() {
                break outcome;
            }
            thread::sleep(Duration::from_millis(2));
        };
        assert!(matches!(outcome, Err(TransportError::BeforeSend(_))));
        listener.set_nonblocking(true).unwrap();
        match listener.accept() {
            Ok((mut stream, _)) => {
                let mut first = [0_u8; 1];
                assert_eq!(stream.read(&mut first).unwrap(), 0);
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {}
            Err(error) => panic!("host accept: {error}"),
        }
        drop(listener);
        remove_socket(&path);
    }

    #[test]
    #[cfg(target_os = "linux")]
    fn nonaccepting_listener_backlog_cannot_block_connect_past_deadline() {
        let path = socket_path();
        let listener = UnixListener::bind(&path).unwrap();
        assert_eq!(unsafe { libc::listen(listener.as_raw_fd(), 0) }, 0);
        let mut occupied = Vec::new();
        let mut saturated = false;
        for _ in 0..64 {
            let start = Instant::now();
            match connect_nonblocking(&path, start + Duration::from_secs(2), None) {
                Ok(stream) => occupied.push(stream),
                Err(TransportError::BeforeSend(_)) => {
                    saturated = true;
                    assert!(start.elapsed() < Duration::from_millis(300));
                    break;
                }
                Err(TransportError::Uncertain(_)) => panic!("connect has no sent bytes"),
            }
        }
        assert!(
            saturated,
            "fixture did not fill the nonaccepting Unix backlog"
        );
        let cancelled = AtomicBool::new(true);
        let start = Instant::now();
        assert!(matches!(
            connect_nonblocking(&path, start + Duration::from_secs(1), Some(&cancelled)),
            Err(TransportError::BeforeSend(_))
        ));
        assert!(start.elapsed() < Duration::from_millis(300));
        drop(occupied);
        drop(listener);
        remove_socket(&path);
    }
}
