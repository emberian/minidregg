//! Controller-owned, bounded Chat Completions receiving edge.
//!
//! This module cannot authorize a provider send. It asks the Mini controller
//! for a durable native reserve and an exact parent witness, then for a
//! durable send-boundary acknowledgement. The controller owns signing and
//! reconciliation; this edge owns only a revocable prompt lease and HTTP I/O.
use serde_json::{json, Value};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::net::{Shutdown, SocketAddr, TcpListener, TcpStream};
use std::os::unix::fs::{FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender, TrySendError};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

const MAX_HEADER: usize = 16_384;
const MAX_REQUEST: usize = 1_048_576;
const MAX_RESPONSE: usize = 8_388_608;
const MAX_TOKEN: usize = 128;
const MAX_BUSY_RESPONDERS: usize = 4;

pub struct GatewayConfig {
    pub bind: SocketAddr,
    /// When set, the worker reaches this private socket through a bind mount
    /// and the host TCP address is used only in its isolated loopback profile.
    pub unix_socket: Option<PathBuf>,
    /// Exact upstream endpoint, including `/v1/chat/completions`.
    pub upstream_url: String,
    pub pinned_model: String,
    /// Never pass this to a worker process, its environment, or an HTTP reply.
    pub provider_key: String,
    pub private_dir: PathBuf,
    pub max_request_bytes: usize,
    pub max_response_bytes: usize,
    pub timeout: Duration,
    /// Operator-pinned hard context ceiling for the selected provider/model.
    /// The provider accounting contract, not JSON byte length, supplies this
    /// premise; the controller checks its tariff against the signed reserve.
    pub max_input_tokens: Option<u32>,
    /// Controller-owned Chat Completions output ceiling. When present the
    /// gateway pins `max_tokens` in the exact forwarded request before Reserve.
    pub max_output_tokens: Option<u32>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LeaseId {
    pub prompt_operation_id: u64,
    pub parent_generation: String,
}

pub struct Lease {
    pub id: LeaseId,
    /// Per-prompt, worker-visible credential; rotate on every activation.
    pub worker_token: String,
}

pub struct ProviderRequest {
    pub lease: LeaseId,
    pub model: String,
    /// Exact bounded JSON body. The controller retains it and computes its
    /// digest before returning a permit; a worker-supplied digest has no role.
    pub exact_body: Vec<u8>,
}

pub enum ForwardPermit {
    Fresh {
        attempt_id: u64,
        lease: LeaseId,
        /// Must equal the request bytes; a permit is never transferable to a
        /// changed model, request, generation, or prompt.
        exact_body: Vec<u8>,
    },
    /// A previously delivered response for these exact request bytes. It
    /// carries no permission to reach the upstream provider again.
    Replay {
        lease: LeaseId,
        exact_body: Vec<u8>,
        status: u16,
        content_type: String,
        exact_response: Vec<u8>,
    },
}

pub enum ProviderOutcome {
    Received {
        status: u16,
        content_type: String,
        /// Exact bounded curl final-response header spool, including any
        /// interim 1xx blocks. The controller retains and hashes these bytes
        /// before using status/Content-Type as metering metadata.
        exact_headers: Vec<u8>,
        exact_body: Vec<u8>,
    },
    /// No network send was started after the permit was issued.
    NotSent { reason: String },
    /// The upstream may have received the request. Never resend it here.
    Uncertain {
        partial_body: Vec<u8>,
        reason: String,
    },
}

pub enum ProviderCommand {
    Reserve {
        request: ProviderRequest,
        reply: Sender<Result<ForwardPermit, String>>,
    },
    BeforeSend {
        attempt_id: u64,
        lease: LeaseId,
        reply: Sender<Result<(), String>>,
    },
    Outcome {
        attempt_id: u64,
        outcome: ProviderOutcome,
        reply: Sender<Result<(), String>>,
    },
    /// `local_write_success` means the local socket write completed. TCP does
    /// not establish whether the worker consumed the response bytes.
    Delivery {
        attempt_id: u64,
        local_write_success: bool,
        reply: Sender<Result<(), String>>,
    },
}

struct LeaseState {
    active: Option<Lease>,
    worker_deadline: Option<Instant>,
    last_token: Option<String>,
}

struct Shared {
    lease: Mutex<LeaseState>,
    revoked: AtomicBool,
    active_request: AtomicBool,
    busy_responders: AtomicUsize,
    last_permit_id: AtomicU64,
    curl: Mutex<Option<Child>>,
    client: Mutex<Option<GatewayStream>>,
    stop: AtomicBool,
}

enum GatewayStream {
    Tcp(TcpStream),
    Unix(UnixStream),
}

impl GatewayStream {
    fn is_unix(&self) -> bool {
        matches!(self, Self::Unix(_))
    }
    fn set_read_timeout(&self, timeout: Option<Duration>) -> io::Result<()> {
        match self {
            Self::Tcp(stream) => stream.set_read_timeout(timeout),
            Self::Unix(stream) => stream.set_read_timeout(timeout),
        }
    }

    fn set_write_timeout(&self, timeout: Option<Duration>) -> io::Result<()> {
        match self {
            Self::Tcp(stream) => stream.set_write_timeout(timeout),
            Self::Unix(stream) => stream.set_write_timeout(timeout),
        }
    }

    fn try_clone(&self) -> io::Result<Self> {
        match self {
            Self::Tcp(stream) => stream.try_clone().map(Self::Tcp),
            Self::Unix(stream) => stream.try_clone().map(Self::Unix),
        }
    }

    fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        match self {
            Self::Tcp(stream) => stream.shutdown(how),
            Self::Unix(stream) => stream.shutdown(how),
        }
    }
}

impl Read for GatewayStream {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Self::Tcp(stream) => stream.read(buf),
            Self::Unix(stream) => stream.read(buf),
        }
    }
}

impl Write for GatewayStream {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        match self {
            Self::Tcp(stream) => stream.write(buf),
            Self::Unix(stream) => stream.write(buf),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        match self {
            Self::Tcp(stream) => stream.flush(),
            Self::Unix(stream) => stream.flush(),
        }
    }
}

enum GatewayListener {
    Tcp(TcpListener),
    Unix(UnixListener),
}

impl GatewayListener {
    fn accept(&self) -> io::Result<GatewayStream> {
        match self {
            Self::Tcp(listener) => listener
                .accept()
                .map(|(stream, _)| GatewayStream::Tcp(stream)),
            Self::Unix(listener) => listener
                .accept()
                .map(|(stream, _)| GatewayStream::Unix(stream)),
        }
    }

    fn set_nonblocking(&self, value: bool) -> io::Result<()> {
        match self {
            Self::Tcp(listener) => listener.set_nonblocking(value),
            Self::Unix(listener) => listener.set_nonblocking(value),
        }
    }
}

#[derive(Clone)]
pub struct GatewayControl {
    shared: Arc<Shared>,
}

impl GatewayControl {
    pub fn activate(&self, lease: Lease, worker_deadline: Instant) -> Result<(), String> {
        let remaining = worker_deadline
            .checked_duration_since(Instant::now())
            .ok_or("worker deadline already passed")?;
        if remaining.is_zero() || remaining > Duration::from_secs(1800) {
            return Err("worker deadline exceeds bounded prompt lifetime".into());
        }
        if lease.id.prompt_operation_id == 0
            || lease.id.parent_generation.is_empty()
            || lease.worker_token.len() < 32
            || lease.worker_token.len() > MAX_TOKEN
            || !lease
                .worker_token
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
        {
            return Err("invalid prompt lease or gateway token".into());
        }
        if self.shared.active_request.load(Ordering::SeqCst) {
            return Err("provider request is still active".into());
        }
        let mut state = self
            .shared
            .lease
            .lock()
            .map_err(|_| "lease lock poisoned")?;
        if state.active.is_some() || state.last_token.as_ref() == Some(&lease.worker_token) {
            return Err("prior lease must be revoked and token rotated".into());
        }
        state.last_token = Some(lease.worker_token.clone());
        state.active = Some(lease);
        state.worker_deadline = Some(worker_deadline);
        self.shared.revoked.store(false, Ordering::SeqCst);
        Ok(())
    }

    /// Call synchronously from the hard-EOF callback, before native Mini I/O.
    /// It never waits for a provider reply or controller command.
    pub fn revoke(&self) {
        self.shared.revoked.store(true, Ordering::SeqCst);
        if let Ok(mut state) = self.shared.lease.lock() {
            state.active = None;
            state.worker_deadline = None;
        }
        if let Ok(mut child) = self.shared.curl.lock() {
            if let Some(child) = child.as_mut() {
                let _ = child.kill();
            }
        }
        if let Ok(client) = self.shared.client.lock() {
            if let Some(client) = client.as_ref() {
                let _ = client.shutdown(Shutdown::Both);
            }
        }
    }

    /// True once no accepted request can enqueue another controller command.
    /// The controller should still drain commands already queued before it
    /// drops its receiver.
    pub fn is_idle(&self) -> bool {
        !self.shared.active_request.load(Ordering::SeqCst)
    }

    fn current(&self, token: &str) -> Option<LeaseId> {
        if self.shared.revoked.load(Ordering::SeqCst) {
            return None;
        }
        let state = self.shared.lease.lock().ok()?;
        if state
            .worker_deadline
            .is_none_or(|deadline| Instant::now() >= deadline)
        {
            return None;
        }
        let lease = state.active.as_ref()?;
        if constant_time_eq(token.as_bytes(), lease.worker_token.as_bytes()) {
            Some(lease.id.clone())
        } else {
            None
        }
    }

    fn still_active(&self, id: &LeaseId) -> bool {
        if self.shared.revoked.load(Ordering::SeqCst) {
            return false;
        }
        self.shared
            .lease
            .lock()
            .ok()
            .and_then(|s| {
                s.active.as_ref().map(|lease| {
                    lease.id == *id
                        && s.worker_deadline
                            .is_some_and(|deadline| Instant::now() < deadline)
                })
            })
            .unwrap_or(false)
    }
}

pub struct GatewayEndpoint {
    address: SocketAddr,
    socket_identity: Option<(PathBuf, u64, u64)>,
    control: GatewayControl,
    listener_thread: Option<JoinHandle<()>>,
}

impl GatewayEndpoint {
    pub fn start(
        config: GatewayConfig,
        commands: SyncSender<ProviderCommand>,
    ) -> Result<Self, String> {
        validate_config(&config)?;
        let (listener, address, socket_identity) = if let Some(path) = &config.unix_socket {
            if path.parent() != Some(config.private_dir.as_path()) {
                return Err("provider socket must be directly in private state".into());
            }
            match fs::symlink_metadata(path) {
                Ok(meta) => {
                    if !meta.file_type().is_socket()
                        || meta.uid() != unsafe { libc::geteuid() }
                        || meta.permissions().mode() & 0o077 != 0
                    {
                        return Err("existing provider socket is not an owned socket".into());
                    }
                    match UnixStream::connect(path) {
                        Ok(_) => {
                            return Err("provider socket is already accepting connections".into())
                        }
                        Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => {}
                        Err(error) => {
                            return Err(format!("existing provider socket probe: {error}"))
                        }
                    }
                    fs::remove_file(path).map_err(|e| format!("stale provider socket: {e}"))?;
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(format!("provider socket metadata: {error}")),
            }
            let listener =
                UnixListener::bind(path).map_err(|e| format!("provider socket bind: {e}"))?;
            fs::set_permissions(path, fs::Permissions::from_mode(0o600))
                .map_err(|e| format!("provider socket permissions: {e}"))?;
            let meta =
                fs::symlink_metadata(path).map_err(|e| format!("provider socket metadata: {e}"))?;
            if !meta.file_type().is_socket() || meta.uid() != unsafe { libc::geteuid() } {
                return Err("provider socket is not owned by controller".into());
            }
            (
                GatewayListener::Unix(listener),
                config.bind,
                Some((path.clone(), meta.dev(), meta.ino())),
            )
        } else {
            let listener =
                TcpListener::bind(config.bind).map_err(|e| format!("provider bind: {e}"))?;
            let address = listener.local_addr().map_err(|e| e.to_string())?;
            (GatewayListener::Tcp(listener), address, None)
        };
        listener.set_nonblocking(true).map_err(|e| e.to_string())?;
        let shared = Arc::new(Shared {
            lease: Mutex::new(LeaseState {
                active: None,
                worker_deadline: None,
                last_token: None,
            }),
            revoked: AtomicBool::new(true),
            active_request: AtomicBool::new(false),
            busy_responders: AtomicUsize::new(0),
            last_permit_id: AtomicU64::new(0),
            curl: Mutex::new(None),
            client: Mutex::new(None),
            stop: AtomicBool::new(false),
        });
        let control = GatewayControl {
            shared: shared.clone(),
        };
        let config = Arc::new(config);
        let listener_thread = thread::spawn(move || {
            while !shared.stop.load(Ordering::SeqCst) {
                match listener.accept() {
                    Ok(mut stream) => {
                        if shared.active_request.swap(true, Ordering::SeqCst) {
                            if shared.busy_responders.fetch_add(1, Ordering::SeqCst)
                                >= MAX_BUSY_RESPONDERS
                            {
                                shared.busy_responders.fetch_sub(1, Ordering::SeqCst);
                                let _ = stream.shutdown(Shutdown::Both);
                                continue;
                            }
                            let busy_shared = shared.clone();
                            let max_request_bytes = config.max_request_bytes;
                            thread::spawn(move || {
                                let _ = stream.set_read_timeout(Some(Duration::from_secs(1)));
                                let _ = stream.set_write_timeout(Some(Duration::from_secs(5)));
                                // Drain one bounded request before replying. Closing with an
                                // unread POST body can turn a valid 503 into a TCP reset.
                                if read_request(&mut stream, max_request_bytes).is_ok() {
                                    error_reply(&mut stream, 503, "provider controller is busy");
                                }
                                busy_shared.busy_responders.fetch_sub(1, Ordering::SeqCst);
                            });
                            continue;
                        }
                        let _ = stream.set_read_timeout(Some(Duration::from_secs(1)));
                        let _ = stream.set_write_timeout(Some(Duration::from_secs(5)));
                        if let Ok(clone) = stream.try_clone() {
                            if let Ok(mut client) = shared.client.lock() {
                                *client = Some(clone);
                            }
                        }
                        let worker_shared = shared.clone();
                        let worker_config = config.clone();
                        let worker_commands = commands.clone();
                        thread::spawn(move || {
                            serve_client(
                                &mut stream,
                                &worker_config,
                                &worker_shared,
                                &worker_commands,
                            );
                            if let Ok(mut client) = worker_shared.client.lock() {
                                *client = None;
                            }
                            worker_shared.active_request.store(false, Ordering::SeqCst);
                        });
                    }
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        thread::sleep(Duration::from_millis(20));
                    }
                    Err(_) => break,
                }
            }
        });
        Ok(Self {
            address,
            socket_identity,
            control,
            listener_thread: Some(listener_thread),
        })
    }

    pub fn local_addr(&self) -> SocketAddr {
        self.address
    }
    pub fn control(&self) -> GatewayControl {
        self.control.clone()
    }
}

impl Drop for GatewayEndpoint {
    fn drop(&mut self) {
        self.control.revoke();
        self.control.shared.stop.store(true, Ordering::SeqCst);
        if let Some(handle) = self.listener_thread.take() {
            let _ = handle.join();
        }
        if let Some((path, dev, ino)) = &self.socket_identity {
            if fs::symlink_metadata(path).is_ok_and(|meta| {
                meta.file_type().is_socket() && meta.dev() == *dev && meta.ino() == *ino
            }) {
                let _ = fs::remove_file(path);
            }
        }
    }
}

fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    let mut difference = a.len() ^ b.len();
    for i in 0..a.len().max(b.len()) {
        difference |= usize::from(a.get(i).copied().unwrap_or(0) ^ b.get(i).copied().unwrap_or(0));
    }
    difference == 0
}

fn validate_config(config: &GatewayConfig) -> Result<(), String> {
    if !config.bind.ip().is_loopback() {
        return Err("provider listener must bind loopback".into());
    }
    if config.max_request_bytes == 0
        || config.max_request_bytes > MAX_REQUEST
        || config.max_response_bytes == 0
        || config.max_response_bytes > MAX_RESPONSE
        || config.timeout.is_zero()
        || config.timeout > Duration::from_secs(600)
    {
        return Err("provider bounds exceed fixed ceiling".into());
    }
    if config.pinned_model.is_empty()
        || config.pinned_model.len() > 256
        || config.pinned_model.chars().any(char::is_control)
    {
        return Err("invalid pinned provider model".into());
    }
    if config.max_input_tokens.is_some() != config.max_output_tokens.is_some()
        || config
            .max_input_tokens
            .is_some_and(|value| !(1..=131_072).contains(&value))
        || config
            .max_output_tokens
            .is_some_and(|value| !(1..=8192).contains(&value))
    {
        return Err("provider token ceilings must be paired and within bounds".into());
    }
    if config.provider_key.is_empty()
        || config.provider_key.len() > 4096
        || config
            .provider_key
            .bytes()
            .any(|b| !(0x21..=0x7e).contains(&b))
    {
        return Err("invalid provider key encoding".into());
    }
    validate_upstream(&config.upstream_url)?;
    let meta = fs::symlink_metadata(&config.private_dir).map_err(|e| e.to_string())?;
    if !config.private_dir.is_absolute()
        || !meta.file_type().is_dir()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err("provider private dir must be owned real 0700".into());
    }
    Ok(())
}

/// Produce the exact bytes that both the native Reserve and the upstream
/// transport will see. Re-serialization intentionally removes duplicate JSON
/// keys: no downstream parser can select a different `max_tokens` or `n`.
/// The input-token ceiling is a pinned provider/model contract checked by the
/// controller against the tariff; this function does not infer tokens from
/// wire bytes.
fn bounded_chat_request(
    mut value: Value,
    output_ceiling: u32,
    max_bytes: usize,
) -> Result<Vec<u8>, String> {
    let object = value
        .as_object_mut()
        .ok_or("Chat Completions request must be an object")?;
    // The retained Hermes fixture uses model/messages/stream/stream_options/
    // tools. Additional names here are standard text Chat Completions controls
    // whose output remains inside the one `max_tokens` ceiling. Unknown vendor
    // extensions may select a fallback model, hidden modality, or extra work.
    const TEXT_FIELDS: &[&str] = &[
        "model",
        "messages",
        "stream",
        "stream_options",
        "tools",
        "max_tokens",
        "temperature",
        "top_p",
        "frequency_penalty",
        "presence_penalty",
        "stop",
        "tool_choice",
        "parallel_tool_calls",
        "response_format",
        "seed",
        "logit_bias",
        "user",
        "n",
        "best_of",
        "modalities",
    ];
    for name in object.keys() {
        if !TEXT_FIELDS.contains(&name.as_str()) {
            return Err(format!("unsupported provider request field {name}"));
        }
    }
    for name in ["n", "best_of"] {
        if object
            .get(name)
            .is_some_and(|value| value.as_u64() != Some(1))
        {
            return Err(format!("provider request {name} must be one"));
        }
    }
    if object.get("modalities").is_some_and(|value| {
        value
            .as_array()
            .is_none_or(|items| items.len() != 1 || items[0] != "text")
    }) {
        return Err("only text modality is supported by the metered profile".into());
    }
    let messages = object
        .get("messages")
        .and_then(Value::as_array)
        .ok_or("metered request needs messages")?;
    if messages.is_empty()
        || messages.iter().any(|message| {
            let Some(message) = message.as_object() else {
                return true;
            };
            message
                .get("content")
                .is_some_and(|content| !content.is_string() && !content.is_null())
                || message.contains_key("audio")
                || message.contains_key("image_url")
        })
    {
        return Err("metered profile supports text messages only".into());
    }
    if object.get("tools").is_some_and(|tools| {
        tools.as_array().is_none_or(|tools| {
            tools
                .iter()
                .any(|tool| tool.get("type").and_then(Value::as_str) != Some("function"))
        })
    }) {
        return Err("metered profile supports function tools only".into());
    }
    if object
        .get("stream")
        .is_some_and(|value| !value.is_boolean())
    {
        return Err("metered stream flag must be boolean".into());
    }
    if object.get("stream_options").is_some_and(|value| {
        value.as_object().is_none_or(|fields| {
            fields.keys().any(|name| name != "include_usage")
                || fields
                    .get("include_usage")
                    .is_some_and(|usage| !usage.is_boolean())
        })
    }) {
        return Err("unsupported metered stream options".into());
    }
    if object.get("stream").and_then(Value::as_bool) == Some(true)
        && object
            .get("stream_options")
            .and_then(|options| options.get("include_usage"))
            .and_then(Value::as_bool)
            != Some(true)
    {
        return Err("metered stream requires terminal usage".into());
    }
    match object.get("max_tokens") {
        Some(value)
            if value
                .as_u64()
                .is_some_and(|tokens| (1..=u64::from(output_ceiling)).contains(&tokens)) => {}
        Some(_) => return Err("requested max_tokens exceeds operator ceiling".into()),
        None => {
            object.insert("max_tokens".into(), json!(output_ceiling));
        }
    }
    let bytes = serde_json::to_vec(&value).map_err(|e| e.to_string())?;
    if bytes.len() > max_bytes {
        return Err("bounded request exceeds byte ceiling after token pinning".into());
    }
    Ok(bytes)
}

fn validate_upstream(url: &str) -> Result<(), String> {
    let (scheme, remainder) = url.split_once("://").ok_or("upstream URL lacks scheme")?;
    let (authority, path) = remainder.split_once('/').ok_or("upstream URL lacks path")?;
    if !matches!(path, "v1/chat/completions" | "api/v1/chat/completions")
        || authority.is_empty()
        || authority
            .bytes()
            .any(|b| !(b.is_ascii_alphanumeric() || b".-:[]".contains(&b)))
        || authority.contains("..")
        || authority.contains('@')
    {
        return Err("upstream must pin one Chat Completions endpoint".into());
    }
    if scheme == "http" {
        if !(authority == "127.0.0.1"
            || authority.starts_with("127.0.0.1:")
            || authority == "[::1]"
            || authority.starts_with("[::1]:"))
        {
            return Err("plain HTTP upstream is permitted only on loopback".into());
        }
    } else if scheme != "https" {
        return Err("provider upstream must use verified HTTPS".into());
    }
    Ok(())
}

struct HttpRequest {
    token: String,
    body: Vec<u8>,
}

fn read_request(stream: &mut GatewayStream, max_body: usize) -> Result<HttpRequest, String> {
    let started = Instant::now();
    let mut bytes = Vec::new();
    let header_end = loop {
        if started.elapsed() >= Duration::from_secs(10) {
            return Err("request read deadline".into());
        }
        let mut chunk = [0u8; 4096];
        match stream.read(&mut chunk) {
            Ok(0) => return Err("request closed before headers".into()),
            Ok(n) => bytes.extend_from_slice(&chunk[..n]),
            Err(error)
                if error.kind() == io::ErrorKind::WouldBlock
                    || error.kind() == io::ErrorKind::TimedOut =>
            {
                continue
            }
            Err(error) => return Err(format!("request read: {error}")),
        }
        if let Some(offset) = bytes.windows(4).position(|w| w == b"\r\n\r\n") {
            break offset + 4;
        }
        if bytes.len() > MAX_HEADER {
            return Err("request headers exceed 16 KiB".into());
        }
    };
    if header_end > MAX_HEADER {
        return Err("request headers exceed 16 KiB".into());
    }
    let header =
        std::str::from_utf8(&bytes[..header_end]).map_err(|_| "request headers not UTF-8")?;
    let mut lines = header[..header.len() - 4].split("\r\n");
    if lines.next() != Some("POST /v1/chat/completions HTTP/1.1") {
        return Err("only POST /v1/chat/completions is accepted".into());
    }
    let mut length = None;
    let mut token = None;
    let mut content_type = None;
    for line in lines {
        let (name, value) = line.split_once(':').ok_or("malformed request header")?;
        let name = name.trim().to_ascii_lowercase();
        let value = value.trim();
        match name.as_str() {
            "content-length" if length.is_none() => {
                if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
                    return Err("invalid content length".into());
                }
                length = Some(
                    value
                        .parse::<usize>()
                        .map_err(|_| "invalid content length")?,
                );
            }
            "authorization" if token.is_none() => {
                token = value.strip_prefix("Bearer ").map(str::to_owned);
            }
            "content-type" if content_type.is_none() => {
                content_type = Some(value.to_ascii_lowercase())
            }
            "transfer-encoding" | "content-encoding" | "expect" => {
                return Err("unsupported request encoding".into())
            }
            "content-length" | "authorization" | "content-type" => {
                return Err("duplicate request authority header".into())
            }
            _ => {}
        }
    }
    if !content_type
        .as_deref()
        .is_some_and(|v| v == "application/json" || v.starts_with("application/json;"))
    {
        return Err("request content type must be JSON".into());
    }
    let length = length.ok_or("request has no content length")?;
    if length == 0 || length > max_body {
        return Err("request body exceeds bound".into());
    }
    let token = token.ok_or("gateway token missing")?;
    if token.len() > MAX_TOKEN {
        return Err("gateway token too long".into());
    }
    let mut body = bytes[header_end..].to_vec();
    if body.len() > length {
        return Err("request body exceeds content length".into());
    }
    while body.len() < length {
        if started.elapsed() >= Duration::from_secs(10) {
            return Err("request body deadline".into());
        }
        let mut chunk = [0u8; 4096];
        let needed = (length - body.len()).min(chunk.len());
        match stream.read(&mut chunk[..needed]) {
            Ok(0) => return Err("request body truncated".into()),
            Ok(n) => body.extend_from_slice(&chunk[..n]),
            Err(error)
                if error.kind() == io::ErrorKind::WouldBlock
                    || error.kind() == io::ErrorKind::TimedOut =>
            {
                continue
            }
            Err(error) => return Err(format!("request body: {error}")),
        }
    }
    Ok(HttpRequest { token, body })
}

fn write_http(
    stream: &mut GatewayStream,
    status: u16,
    content_type: &str,
    body: &[u8],
) -> io::Result<()> {
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        401 => "Unauthorized",
        403 => "Forbidden",
        405 => "Method Not Allowed",
        413 => "Content Too Large",
        429 => "Too Many Requests",
        502 => "Bad Gateway",
        503 => "Service Unavailable",
        _ => "Provider Response",
    };
    write!(stream, "HTTP/1.1 {status} {reason}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", body.len())?;
    stream.write_all(body)
}

fn error_reply(stream: &mut GatewayStream, status: u16, message: &str) {
    let body = json!({"error":{"message":message,"type":"gateway_error"}}).to_string();
    let _ = write_http(stream, status, "application/json", body.as_bytes());
}

fn serve_client(
    stream: &mut GatewayStream,
    config: &GatewayConfig,
    shared: &Arc<Shared>,
    commands: &SyncSender<ProviderCommand>,
) {
    let mut request = match read_request(stream, config.max_request_bytes) {
        Ok(request) => request,
        Err(_) => {
            error_reply(stream, 400, "bounded Chat Completions request required");
            return;
        }
    };
    let control = GatewayControl {
        shared: shared.clone(),
    };
    let Some(lease) = control.current(&request.token) else {
        error_reply(stream, 401, "gateway prompt lease is not active");
        return;
    };
    let value: Value = match serde_json::from_slice(&request.body) {
        Ok(value) => value,
        Err(_) => {
            error_reply(stream, 400, "invalid JSON request");
            return;
        }
    };
    if value.get("model").and_then(Value::as_str) != Some(config.pinned_model.as_str()) {
        error_reply(stream, 403, "model is not pinned for this task");
        return;
    }
    if let Some(output_ceiling) = config.max_output_tokens {
        request.body = match bounded_chat_request(value, output_ceiling, config.max_request_bytes) {
            Ok(body) => body,
            Err(_) => {
                error_reply(
                    stream,
                    400,
                    "metered Chat Completions request exceeds pinned profile",
                );
                return;
            }
        };
    }
    let (tx, rx) = mpsc::channel();
    let reserve = ProviderCommand::Reserve {
        request: ProviderRequest {
            lease: lease.clone(),
            model: config.pinned_model.clone(),
            exact_body: request.body.clone(),
        },
        reply: tx,
    };
    if commands.try_send(reserve).is_err() {
        error_reply(stream, 503, "provider controller is busy");
        return;
    }
    let permit = match wait_reply(&rx, &control, &lease) {
        Ok(permit) => permit,
        Err(_) => {
            error_reply(stream, 503, "provider reserve was refused or interrupted");
            return;
        }
    };
    let permit = match permit {
        ForwardPermit::Replay {
            lease: permit_lease,
            exact_body,
            status,
            content_type,
            exact_response,
        } => {
            if permit_lease != lease
                || exact_body != request.body
                || exact_response.len() > config.max_response_bytes
                || !(100..=599).contains(&status)
                || content_type.len() > 256
                || content_type
                    .bytes()
                    .any(|byte| byte == b'\r' || byte == b'\n')
                || !control.still_active(&lease)
            {
                error_reply(stream, 503, "provider replay did not bind this request");
                return;
            }
            let _ = write_http(stream, status, &content_type, &exact_response);
            return;
        }
        ForwardPermit::Fresh {
            attempt_id,
            lease: permit_lease,
            exact_body,
        } => {
            if attempt_id == 0 || permit_lease != lease || exact_body != request.body {
                error_reply(stream, 503, "provider permit did not bind this request");
                return;
            }
            (attempt_id, exact_body)
        }
    };
    let (attempt_id, exact_body) = permit;
    if shared
        .last_permit_id
        .fetch_max(attempt_id, Ordering::SeqCst)
        >= attempt_id
    {
        error_reply(stream, 503, "provider permit was already consumed");
        return;
    }
    let (tx, rx) = mpsc::channel();
    if commands
        .try_send(ProviderCommand::BeforeSend {
            attempt_id,
            lease: lease.clone(),
            reply: tx,
        })
        .is_err()
        || wait_reply(&rx, &control, &lease).is_err()
    {
        report_outcome(
            commands,
            attempt_id,
            ProviderOutcome::NotSent {
                reason: "send boundary not acknowledged".into(),
            },
            None,
        );
        error_reply(stream, 503, "provider send boundary was not acknowledged");
        return;
    }
    let outcome = forward(config, shared, &control, &lease, attempt_id, &exact_body);
    let reply = match &outcome {
        ProviderOutcome::Received {
            status,
            content_type,
            exact_body,
            ..
        } => Some((*status, content_type.clone(), exact_body.clone())),
        _ => None,
    };
    let wait_for_live_lease = matches!(outcome, ProviderOutcome::Received { .. });
    if !report_outcome(
        commands,
        attempt_id,
        outcome,
        wait_for_live_lease.then_some((&control, &lease)),
    ) {
        error_reply(
            stream,
            503,
            "provider outcome is pending controller recovery",
        );
        return;
    }
    if let Some((status, content_type, body)) = reply {
        let local_write_success = write_http(stream, status, &content_type, &body).is_ok()
            && bridge_delivery_ack(stream, &control, &lease);
        let _ = report_delivery(commands, attempt_id, local_write_success);
    } else {
        error_reply(
            stream,
            502,
            "provider outcome is uncertain; no retry was sent",
        );
    }
}

/// TCP means the gateway wrote directly to Hermes. For the private Unix
/// route, one byte from this connection's worker bridge attests only that its
/// write to the local Hermes socket completed. It cannot prove consumption.
/// Missing acknowledgement retains the provider hold and forbids resend.
fn bridge_delivery_ack(
    stream: &mut GatewayStream,
    control: &GatewayControl,
    lease: &LeaseId,
) -> bool {
    if !stream.is_unix() {
        return true;
    }
    let deadline = Instant::now() + Duration::from_secs(30);
    let mut byte = [0u8; 1];
    loop {
        if Instant::now() >= deadline || !control.still_active(lease) {
            return false;
        }
        match stream.read(&mut byte) {
            Ok(1) => return byte == *b"1" && control.still_active(lease),
            Ok(0) | Ok(_) => return false,
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
                ) =>
            {
                continue
            }
            Err(_) => return false,
        }
    }
}

fn wait_reply<T>(
    rx: &Receiver<Result<T, String>>,
    control: &GatewayControl,
    lease: &LeaseId,
) -> Result<T, String> {
    loop {
        if !control.still_active(lease) {
            return Err("prompt lease revoked or worker deadline passed".into());
        }
        match rx.recv_timeout(Duration::from_millis(20)) {
            Ok(result) => {
                if !control.still_active(lease) {
                    return Err("prompt lease revoked or worker deadline passed".into());
                }
                return result;
            }
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err("controller reply channel closed".into())
            }
        }
    }
}

fn report_outcome(
    commands: &SyncSender<ProviderCommand>,
    attempt_id: u64,
    outcome: ProviderOutcome,
    live_lease: Option<(&GatewayControl, &LeaseId)>,
) -> bool {
    let (tx, rx) = mpsc::channel();
    let mut command = ProviderCommand::Outcome {
        attempt_id,
        outcome,
        reply: tx,
    };
    let started = Instant::now();
    let waiting = || match live_lease {
        // A complete response must wait for the source-owned quote and
        // durable Outcome ack, potentially longer than the old fixed 30s.
        // The active worker deadline (at most 1800s after activation) bounds
        // this wait and hard revoke interrupts it without waiting for Mini.
        Some((control, lease)) => control.still_active(lease),
        None => started.elapsed() < Duration::from_secs(30),
    };
    loop {
        match commands.try_send(command) {
            Ok(()) => break,
            Err(TrySendError::Full(remaining)) => {
                command = remaining;
                if !waiting() {
                    return false;
                }
                thread::sleep(Duration::from_millis(20));
            }
            Err(TrySendError::Disconnected(_)) => return false,
        }
    }
    loop {
        if !waiting() {
            return false;
        }
        match rx.recv_timeout(Duration::from_millis(20)) {
            Ok(result) => return waiting() && result.is_ok(),
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(mpsc::RecvTimeoutError::Disconnected) => return false,
        }
    }
}

/// A response is not considered delivered merely because its upstream bytes
/// were durably recorded. A missing delivery acknowledgement leaves the
/// controller's exact attempt held for reconciliation.
fn report_delivery(
    commands: &SyncSender<ProviderCommand>,
    attempt_id: u64,
    local_write_success: bool,
) -> bool {
    let (tx, rx) = mpsc::channel();
    let mut command = ProviderCommand::Delivery {
        attempt_id,
        local_write_success,
        reply: tx,
    };
    let started = Instant::now();
    loop {
        match commands.try_send(command) {
            Ok(()) => break,
            Err(TrySendError::Full(remaining)) => {
                command = remaining;
                if started.elapsed() >= Duration::from_secs(30) {
                    return false;
                }
                thread::sleep(Duration::from_millis(20));
            }
            Err(TrySendError::Disconnected(_)) => return false,
        }
    }
    rx.recv_timeout(Duration::from_secs(30))
        .is_ok_and(|result| result.is_ok())
}

fn write_private(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|e| format!("provider spool create: {e}"))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| format!("provider spool sync: {e}"))
}

fn create_private(path: &Path) -> Result<(), String> {
    let file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|e| format!("provider spool create: {e}"))?;
    file.sync_all()
        .map_err(|e| format!("provider spool sync: {e}"))
}

fn read_bounded(path: &Path, bound: usize) -> Result<Vec<u8>, String> {
    let mut file = File::open(path).map_err(|e| format!("provider spool read: {e}"))?;
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take(bound as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("provider spool read: {e}"))?;
    if bytes.len() > bound {
        return Err("provider response exceeds bound".into());
    }
    Ok(bytes)
}

/// Re-derive metering metadata from the exact retained header spool after
/// journal recovery. The controller must compare this result with its durable
/// Received fields before presenting bytes to the source-owned quote route.
pub(crate) fn response_headers(bytes: &[u8]) -> Result<(u16, String), String> {
    let text = std::str::from_utf8(bytes).map_err(|_| "provider headers are not UTF-8")?;
    let normalized = text.replace("\r\n", "\n");
    if normalized.contains('\r') || !normalized.ends_with("\n\n") {
        return Err("provider header block is incomplete".into());
    }
    let mut final_response = None;
    let mut blocks = 0usize;
    for block in normalized.split("\n\n").filter(|block| !block.is_empty()) {
        blocks += 1;
        if blocks > 8 || final_response.is_some() {
            return Err("provider response has ambiguous status blocks".into());
        }
        let mut lines = block.split('\n');
        let status_line = lines.next().ok_or("provider status absent")?;
        let mut words = status_line.split_ascii_whitespace();
        let version = words.next().ok_or("provider status absent")?;
        if !matches!(version, "HTTP/1.0" | "HTTP/1.1" | "HTTP/2" | "HTTP/2.0") {
            return Err("provider status protocol invalid".into());
        }
        let code = words.next().ok_or("provider status absent")?;
        if code.len() != 3 || !code.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err("provider status invalid".into());
        }
        let status = code.parse::<u16>().map_err(|_| "provider status invalid")?;
        if !(100..=599).contains(&status) {
            return Err("provider status invalid".into());
        }
        let mut content_type = None;
        let mut content_encoding_seen = false;
        for line in lines {
            if line.starts_with(' ') || line.starts_with('\t') {
                return Err("provider folded response header refused".into());
            }
            let (name, value) = line
                .split_once(':')
                .ok_or("provider response header malformed")?;
            // RFC 9110 §5.6.2: field-name is token, not just alnum/hyphen.
            if name.is_empty()
                || !name.bytes().all(|byte| {
                    byte.is_ascii_alphanumeric()
                        || matches!(
                            byte,
                            b'!' | b'#'
                                | b'$'
                                | b'%'
                                | b'&'
                                | b'\''
                                | b'*'
                                | b'+'
                                | b'-'
                                | b'.'
                                | b'^'
                                | b'_'
                                | b'`'
                                | b'|'
                                | b'~'
                        )
                })
            {
                return Err("provider response header name invalid".into());
            }
            if name.eq_ignore_ascii_case("content-encoding") {
                if content_encoding_seen || !value.trim().eq_ignore_ascii_case("identity") {
                    return Err("provider response used unsupported content encoding".into());
                }
                content_encoding_seen = true;
            }
            if name.eq_ignore_ascii_case("content-type") {
                if content_type.is_some() {
                    return Err("provider response has duplicate Content-Type".into());
                }
                let value = value.trim();
                if value.is_empty()
                    || value.len() > 128
                    || value.bytes().any(|byte| !(0x20..=0x7e).contains(&byte))
                {
                    return Err("provider content type invalid".into());
                }
                content_type = Some(value.to_owned());
            }
        }
        if status >= 200 {
            final_response = Some((status, content_type.ok_or("provider Content-Type absent")?));
        }
    }
    final_response.ok_or("provider final response absent".into())
}

fn curl_header_config(key: &str) -> String {
    let escaped = key.replace('\\', "\\\\").replace('"', "\\\"");
    format!("header = \"Authorization: Bearer {escaped}\"\n")
}

fn forward(
    config: &GatewayConfig,
    shared: &Arc<Shared>,
    control: &GatewayControl,
    lease: &LeaseId,
    attempt_id: u64,
    exact_body: &[u8],
) -> ProviderOutcome {
    if !control.still_active(lease) {
        return ProviderOutcome::NotSent {
            reason: "prompt lease revoked before dispatch".into(),
        };
    }
    let prefix = format!("provider-{attempt_id:016}");
    let request_path = config.private_dir.join(format!("{prefix}.request"));
    let body_path = config.private_dir.join(format!("{prefix}.response"));
    let header_path = config.private_dir.join(format!("{prefix}.headers"));
    if let Err(reason) = write_private(&request_path, exact_body)
        .and_then(|_| create_private(&body_path))
        .and_then(|_| create_private(&header_path))
        .and_then(|_| {
            File::open(&config.private_dir)
                .and_then(|f| f.sync_all())
                .map_err(|e| e.to_string())
        })
    {
        return ProviderOutcome::NotSent { reason };
    }
    let protocol = if config.upstream_url.starts_with("https://") {
        "=https"
    } else {
        "=http"
    };
    let mut command = Command::new("/usr/bin/curl");
    command
        .env_clear()
        .current_dir(&config.private_dir)
        .arg("--disable")
        .args(["--silent", "--http1.1", "--request", "POST"])
        .args(["--proto", protocol, "--noproxy", "*", "--proxy", ""])
        .args(["--max-redirs", "0", "--connect-timeout", "10"])
        .args(["--max-time", &config.timeout.as_secs().max(1).to_string()])
        .args(["--max-filesize", &config.max_response_bytes.to_string()])
        .args(["--header", "Content-Type: application/json"])
        .args(["--header", "Accept-Encoding: identity"])
        .arg("--data-binary")
        .arg(format!("@{}", request_path.display()))
        .arg("--dump-header")
        .arg(&header_path)
        .arg("--output")
        .arg(&body_path)
        .arg("--url")
        .arg(&config.upstream_url)
        .args(["--config", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    // Kernel backstop: even an older curl build or a peer that omits
    // Content-Length cannot grow either output file beyond this bound.
    let file_limit = config.max_response_bytes.max(MAX_HEADER * 2) as libc::rlim_t;
    unsafe {
        command.pre_exec(move || {
            let limit = libc::rlimit {
                rlim_cur: file_limit,
                rlim_max: file_limit,
            };
            let no_core = libc::rlimit {
                rlim_cur: 0,
                rlim_max: 0,
            };
            if libc::setrlimit(libc::RLIMIT_FSIZE, &limit) == 0
                && libc::setrlimit(libc::RLIMIT_CORE, &no_core) == 0
            {
                Ok(())
            } else {
                Err(io::Error::last_os_error())
            }
        });
    }
    // The lease lock is the physical send linearization edge. If revoke gets
    // it first, no curl can start. If spawn gets it first, revoke can kill
    // the registered Child immediately; no PID is signalled after reap.
    let mut child_stdin = {
        let guard = match shared.lease.lock() {
            Ok(guard) => guard,
            Err(_) => {
                return ProviderOutcome::NotSent {
                    reason: "lease lock poisoned".into(),
                }
            }
        };
        if guard.active.as_ref().map(|active| &active.id) != Some(lease)
            || guard
                .worker_deadline
                .is_none_or(|deadline| Instant::now() >= deadline)
        {
            return ProviderOutcome::NotSent {
                reason: "prompt lease revoked before dispatch".into(),
            };
        }
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(error) => {
                return ProviderOutcome::NotSent {
                    reason: format!("provider transport spawn: {error}"),
                }
            }
        };
        let stdin = child.stdin.take();
        if let Ok(mut slot) = shared.curl.lock() {
            *slot = Some(child);
        } else {
            let _ = child.kill();
            return ProviderOutcome::Uncertain {
                partial_body: Vec::new(),
                reason: "transport custody lock poisoned".into(),
            };
        }
        drop(guard);
        stdin
    };
    let credential_written = child_stdin.take().is_some_and(|mut stdin| {
        stdin
            .write_all(curl_header_config(&config.provider_key).as_bytes())
            .is_ok()
    });
    if !credential_written {
        if let Ok(mut slot) = shared.curl.lock() {
            if let Some(child) = slot.as_mut() {
                let _ = child.kill();
            }
        }
    }
    let started = Instant::now();
    let exit = loop {
        let status = {
            let mut slot = match shared.curl.lock() {
                Ok(slot) => slot,
                Err(_) => break None,
            };
            match slot.as_mut().map(Child::try_wait) {
                Some(Ok(Some(status))) => {
                    *slot = None;
                    Some(status)
                }
                Some(Ok(None)) => None,
                Some(Err(_)) | None => {
                    *slot = None;
                    break None;
                }
            }
        };
        if status.is_some() {
            break status;
        }
        let oversized = [
            (&body_path, config.max_response_bytes),
            (&header_path, MAX_HEADER * 2),
        ]
        .iter()
        .any(|(path, bound)| fs::metadata(path).is_ok_and(|meta| meta.len() > *bound as u64));
        if oversized || started.elapsed() > config.timeout || !control.still_active(lease) {
            if let Ok(mut slot) = shared.curl.lock() {
                if let Some(child) = slot.as_mut() {
                    let _ = child.kill();
                }
            }
        }
        thread::sleep(Duration::from_millis(20));
    };
    let partial_body = match read_bounded(&body_path, config.max_response_bytes) {
        Ok(body) => body,
        Err(reason) => {
            return ProviderOutcome::Uncertain {
                partial_body: Vec::new(),
                reason,
            }
        }
    };
    for path in [&body_path, &header_path, &config.private_dir] {
        if let Err(error) = File::open(path).and_then(|file| file.sync_all()) {
            return ProviderOutcome::Uncertain {
                partial_body,
                reason: format!("provider response spool sync: {error}"),
            };
        }
    }
    if !control.still_active(lease) {
        return ProviderOutcome::Uncertain {
            partial_body,
            reason: "prompt lease revoked during provider send".into(),
        };
    }
    if !credential_written || !exit.is_some_and(|status| status.success()) {
        return ProviderOutcome::Uncertain {
            partial_body,
            reason: "provider transport outcome uncertain".into(),
        };
    }
    let headers = match read_bounded(&header_path, MAX_HEADER * 2) {
        Ok(headers) => headers,
        Err(reason) => {
            return ProviderOutcome::Uncertain {
                partial_body,
                reason,
            }
        }
    };
    let (status, content_type) = match response_headers(&headers) {
        Ok(response) => response,
        Err(reason) => {
            return ProviderOutcome::Uncertain {
                partial_body,
                reason,
            }
        }
    };
    if headers
        .windows(config.provider_key.len())
        .any(|part| part == config.provider_key.as_bytes())
        || partial_body
            .windows(config.provider_key.len())
            .any(|part| part == config.provider_key.as_bytes())
        || content_type.contains(&config.provider_key)
    {
        return ProviderOutcome::Uncertain {
            partial_body,
            reason: "upstream response contained a custody secret and was withheld".into(),
        };
    }
    ProviderOutcome::Received {
        status,
        content_type,
        exact_headers: headers,
        exact_body: partial_body,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::fd::AsRawFd;
    use std::sync::atomic::AtomicUsize;

    static TEST_ID: AtomicU64 = AtomicU64::new(1);
    const TOKEN: &str = "gateway_token_0123456789_abcdef_0123456789";

    fn test_dir() -> PathBuf {
        let id = TEST_ID.fetch_add(1, Ordering::SeqCst);
        let path =
            std::env::temp_dir().join(format!("mini-provider-test-{}-{id}", std::process::id()));
        fs::create_dir(&path).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o700)).unwrap();
        path
    }

    fn config(dir: PathBuf, upstream: SocketAddr) -> GatewayConfig {
        GatewayConfig {
            bind: "127.0.0.1:0".parse().unwrap(),
            unix_socket: None,
            upstream_url: format!("http://{upstream}/v1/chat/completions"),
            pinned_model: "operator-model".into(),
            provider_key: "private-provider-key".into(),
            private_dir: dir,
            max_request_bytes: 16_384,
            max_response_bytes: 16_384,
            timeout: Duration::from_secs(5),
            max_input_tokens: None,
            max_output_tokens: None,
        }
    }

    #[test]
    fn metered_request_pins_exact_forwarded_output_ceiling() {
        let original = br#"{"model":"operator-model","messages":[{"role":"user","content":"hello"}],"stream":true,"stream_options":{"include_usage":true}}"#;
        let value: Value = serde_json::from_slice(original).unwrap();
        let exact = bounded_chat_request(value, 64, 16_384).unwrap();
        let normalized: Value = serde_json::from_slice(&exact).unwrap();
        assert_eq!(normalized["max_tokens"], 64);
        assert_eq!(normalized["stream_options"]["include_usage"], true);
        assert_eq!(normalized["messages"][0]["content"], "hello");
        assert!(bounded_chat_request(normalized, 64, exact.len() - 1).is_err());
        let lower = json!({
            "model": "operator-model",
            "messages": [{"role": "user", "content": "hello"}],
            "max_tokens": 12
        });
        let lower_exact = bounded_chat_request(lower, 64, 16_384).unwrap();
        let lower_forwarded: Value = serde_json::from_slice(&lower_exact).unwrap();
        assert_eq!(lower_forwarded["max_tokens"], 12);
    }

    #[test]
    fn metered_request_rejects_multipliers_aliases_and_unmetered_stream() {
        let base = json!({"model":"operator-model","messages":[{"role":"user","content":"hello"}]});
        for (key, value) in [
            ("max_tokens", json!(65)),
            ("max_tokens", json!(0)),
            ("max_completion_tokens", json!(32)),
            ("max_output_tokens", json!(32)),
            ("n", json!(2)),
            ("best_of", json!(2)),
            ("audio", json!({})),
            ("modalities", json!(["text", "audio"])),
            ("stream", json!("true")),
            ("models", json!(["unmetered-fallback-model"])),
            ("provider", json!({"allow_fallbacks": true})),
        ] {
            let mut request = base.clone();
            request[key] = value;
            assert!(bounded_chat_request(request, 64, 16_384).is_err(), "{key}");
        }
        let mut stream = base.clone();
        stream["stream"] = json!(true);
        assert!(bounded_chat_request(stream, 64, 16_384).is_err());
        let mut stream_extension = base;
        stream_extension["stream_options"] = json!({
            "include_usage": true,
            "vendor_extra": true
        });
        assert!(bounded_chat_request(stream_extension, 64, 16_384).is_err());
    }

    #[test]
    fn metered_overlimit_request_never_reaches_reserve_or_upstream() {
        let dir = test_dir();
        let mut settings = config(dir.clone(), "127.0.0.1:1".parse().unwrap());
        settings.max_input_tokens = Some(8192);
        settings.max_output_tokens = Some(64);
        let (commands, requests) = mpsc::sync_channel(1);
        let endpoint = GatewayEndpoint::start(settings, commands).unwrap();
        endpoint
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(5))
            .unwrap();
        let body = br#"{"model":"operator-model","messages":[{"role":"user","content":"hello"}],"max_tokens":65}"#;
        let response = post(endpoint.local_addr(), TOKEN, body);
        assert!(response.starts_with("HTTP/1.1 400 "));
        assert!(requests.try_recv().is_err());
        let extension = br#"{"model":"operator-model","models":["unmetered-fallback"],"messages":[{"role":"user","content":"hello"}]}"#;
        let response = post(endpoint.local_addr(), TOKEN, extension);
        assert!(response.starts_with("HTTP/1.1 400 "));
        assert!(requests.try_recv().is_err());
        drop(endpoint);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn metered_gateway_reserves_the_exact_capped_request() {
        let dir = test_dir();
        let mut settings = config(dir.clone(), "127.0.0.1:1".parse().unwrap());
        settings.max_input_tokens = Some(8192);
        settings.max_output_tokens = Some(64);
        let (commands, requests) = mpsc::sync_channel(1);
        let endpoint = GatewayEndpoint::start(settings, commands).unwrap();
        endpoint
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(5))
            .unwrap();
        let body = br#"{"model":"operator-model","messages":[{"role":"user","content":"hello"}]}"#;
        let client = thread::spawn({
            let address = endpoint.local_addr();
            move || post(address, TOKEN, body)
        });
        let ProviderCommand::Reserve { request, reply } =
            requests.recv_timeout(Duration::from_secs(5)).unwrap()
        else {
            panic!("first command must be Reserve");
        };
        let forwarded: Value = serde_json::from_slice(&request.exact_body).unwrap();
        assert_eq!(forwarded["max_tokens"], 64);
        assert_eq!(forwarded["messages"][0]["content"], "hello");
        reply.send(Err("test refusal".into())).unwrap();
        assert!(client.join().unwrap().starts_with("HTTP/1.1 503 "));
        assert!(requests.try_recv().is_err());
        drop(endpoint);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn private_unix_gateway_keeps_token_check_and_owned_socket_lifecycle() {
        let dir = test_dir();
        let socket = dir.join("provider-gateway.sock");
        let mut settings = config(dir.clone(), "127.0.0.1:1".parse().unwrap());
        settings.bind = "127.0.0.1:18762".parse().unwrap();
        settings.unix_socket = Some(socket.clone());
        let (commands, _requests) = mpsc::sync_channel(1);
        let endpoint = GatewayEndpoint::start(settings, commands).unwrap();
        assert_eq!(endpoint.local_addr().port(), 18762);
        let meta = fs::symlink_metadata(&socket).unwrap();
        assert!(meta.file_type().is_socket());
        assert_eq!(meta.permissions().mode() & 0o777, 0o600);
        let mut client = UnixStream::connect(&socket).unwrap();
        client
            .set_read_timeout(Some(Duration::from_secs(2)))
            .unwrap();
        client
            .write_all(b"POST /v1/chat/completions HTTP/1.1\r\nAuthorization: Bearer wrong\r\nContent-Type: application/json\r\nContent-Length: 2\r\n\r\n{}")
            .unwrap();
        let mut reply = Vec::new();
        client.read_to_end(&mut reply).unwrap();
        assert!(reply.starts_with(b"HTTP/1.1 401 "));
        drop(client);
        drop(endpoint);
        assert!(!socket.exists());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn private_unix_gateway_reopens_only_owned_stale_socket() {
        let dir = test_dir();
        let socket = dir.join("provider-gateway.sock");
        let mut settings = config(dir.clone(), "127.0.0.1:1".parse().unwrap());
        settings.unix_socket = Some(socket.clone());
        fs::write(&socket, b"not a socket").unwrap();
        let (commands, _requests) = mpsc::sync_channel(1);
        assert!(GatewayEndpoint::start(settings, commands).is_err());
        assert_eq!(fs::read(&socket).unwrap(), b"not a socket");
        fs::remove_file(&socket).unwrap();
        let stale = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        drop(stale);
        let mut settings = config(dir.clone(), "127.0.0.1:1".parse().unwrap());
        settings.unix_socket = Some(socket.clone());
        let (commands, _requests) = mpsc::sync_channel(1);
        let endpoint = GatewayEndpoint::start(settings, commands).unwrap();
        assert!(UnixStream::connect(&socket).is_ok());
        drop(endpoint);
        assert!(!socket.exists());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn private_bridge_ack_is_per_connection_and_revocation_fails_closed() {
        let dir = test_dir();
        let mut settings = config(dir.clone(), "127.0.0.1:1".parse().unwrap());
        settings.unix_socket = Some(dir.join("provider-gateway.sock"));
        let (commands, _requests) = mpsc::sync_channel(1);
        let endpoint = GatewayEndpoint::start(settings, commands).unwrap();
        let lease = lease(1, TOKEN);
        endpoint
            .control()
            .activate(lease, Instant::now() + Duration::from_secs(10))
            .unwrap();
        let id = LeaseId {
            prompt_operation_id: 1,
            parent_generation: "17".into(),
        };
        let (server, mut bridge) = UnixStream::pair().unwrap();
        let mut server = GatewayStream::Unix(server);
        bridge.write_all(b"1").unwrap();
        assert!(bridge_delivery_ack(&mut server, &endpoint.control(), &id));
        let (server, bridge) = UnixStream::pair().unwrap();
        drop(bridge);
        assert!(!bridge_delivery_ack(
            &mut GatewayStream::Unix(server),
            &endpoint.control(),
            &id,
        ));
        let (server, mut bridge) = UnixStream::pair().unwrap();
        endpoint.control().revoke();
        bridge.write_all(b"1").unwrap();
        assert!(!bridge_delivery_ack(
            &mut GatewayStream::Unix(server),
            &endpoint.control(),
            &id,
        ));
        drop(endpoint);
        fs::remove_dir_all(dir).unwrap();
    }

    fn unix_delivery_case(acknowledge: bool) {
        let dir = test_dir();
        let socket = dir.join("provider-gateway.sock");
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(
            upstream.try_clone().unwrap(),
            deliveries.clone(),
            false,
            br#"{"id":"local-provider"}"#.to_vec(),
        );
        let mut settings = config(dir.clone(), upstream.local_addr().unwrap());
        settings.unix_socket = Some(socket.clone());
        let (commands, requests) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(settings, commands).unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(20))
            .unwrap();
        let controller = thread::spawn(move || {
            let ProviderCommand::Reserve { request, reply } =
                requests.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("reserve expected");
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 7,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            let ProviderCommand::BeforeSend { reply, .. } =
                requests.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("send boundary expected");
            };
            reply.send(Ok(())).unwrap();
            let ProviderCommand::Outcome { outcome, reply, .. } =
                requests.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("outcome expected");
            };
            assert!(matches!(outcome, ProviderOutcome::Received { .. }));
            reply.send(Ok(())).unwrap();
            let ProviderCommand::Delivery {
                local_write_success,
                reply,
                ..
            } = requests.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("delivery expected");
            };
            assert_eq!(local_write_success, acknowledge);
            reply.send(Ok(())).unwrap();
        });
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let mut client = UnixStream::connect(&socket).unwrap();
        client
            .set_read_timeout(Some(Duration::from_secs(5)))
            .unwrap();
        write!(client, "POST /v1/chat/completions HTTP/1.1\r\nAuthorization: Bearer {TOKEN}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n", body.len()).unwrap();
        client.write_all(body).unwrap();
        let mut response = Vec::new();
        while !response
            .windows(b"local-provider".len())
            .any(|part| part == b"local-provider")
        {
            let mut chunk = [0u8; 4096];
            let count = client.read(&mut chunk).unwrap();
            assert!(count > 0);
            response.extend_from_slice(&chunk[..count]);
        }
        if acknowledge {
            client.write_all(b"1").unwrap();
        }
        drop(client);
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn private_unix_delivery_requires_bridge_write_ack() {
        unix_delivery_case(true);
        unix_delivery_case(false);
    }

    #[test]
    fn upstream_endpoint_is_exact_and_openrouter_path_is_supported() {
        assert!(validate_upstream("https://openrouter.ai/api/v1/chat/completions").is_ok());
        assert!(validate_upstream("https://example.org/v1/chat/completions").is_ok());
        assert!(
            validate_upstream("https://openrouter.ai/api/v1/chat/completions?model=x").is_err()
        );
        assert!(validate_upstream("http://openrouter.ai/api/v1/chat/completions").is_err());
        assert!(validate_upstream("https://openrouter.ai/other").is_err());
    }

    fn lease(id: u64, token: &str) -> Lease {
        Lease {
            id: LeaseId {
                prompt_operation_id: id,
                parent_generation: "17".into(),
            },
            worker_token: token.into(),
        }
    }

    #[test]
    fn final_response_requires_one_actual_content_type() {
        let complete = b"HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nContent-Type: text/event-stream; charset=UTF-8\r\nContent-Length: 2\r\n\r\n";
        assert_eq!(
            response_headers(complete).unwrap(),
            (200, "text/event-stream; charset=UTF-8".into())
        );
        assert!(
            response_headers(b"HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\n")
                .unwrap_err()
                .contains("Content-Type absent")
        );
        assert!(response_headers(
            b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\ncontent-type: text/event-stream\r\n\r\n"
        )
        .unwrap_err()
        .contains("duplicate Content-Type"));
        assert!(
            response_headers(b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n").is_err()
        );
        assert!(response_headers(
            b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\nHTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n"
        )
        .is_err());
        let token_names =
            b"HTTP/1.1 200 OK\r\n!#$%&'*+-.^_`|~: token\r\nContent-Type: application/json\r\n\r\n";
        assert_eq!(response_headers(token_names).unwrap().0, 200);
        for malformed in [
            b"HTTP/1.1 200 OK\r\nBad Name: x\r\nContent-Type: application/json\r\n\r\n".as_slice(),
            b"HTTP/1.1 200 OK\r\nBad\x01Name: x\r\nContent-Type: application/json\r\n\r\n"
                .as_slice(),
            b"HTTP/1.1 200 OK\r\n: x\r\nContent-Type: application/json\r\n\r\n".as_slice(),
        ] {
            assert!(response_headers(malformed).is_err());
        }
    }

    fn post(address: SocketAddr, token: &str, body: &[u8]) -> String {
        let mut stream = TcpStream::connect(address).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .unwrap();
        write!(stream, "POST /v1/chat/completions HTTP/1.1\r\nHost: 127.0.0.1\r\nAuthorization: Bearer {token}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n", body.len()).unwrap();
        stream.write_all(body).unwrap();
        let mut response = String::new();
        stream.read_to_string(&mut response).unwrap();
        response
    }

    fn fake_upstream(
        listener: TcpListener,
        deliveries: Arc<AtomicUsize>,
        close_without_reply: bool,
        reply_body: Vec<u8>,
    ) -> JoinHandle<String> {
        fake_upstream_with_headers(
            listener,
            deliveries,
            close_without_reply,
            reply_body,
            "Content-Type: application/json\r\n",
        )
    }

    fn fake_upstream_with_headers(
        listener: TcpListener,
        deliveries: Arc<AtomicUsize>,
        close_without_reply: bool,
        reply_body: Vec<u8>,
        response_headers: &'static str,
    ) -> JoinHandle<String> {
        thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            deliveries.fetch_add(1, Ordering::SeqCst);
            stream
                .set_read_timeout(Some(Duration::from_secs(5)))
                .unwrap();
            let mut bytes = Vec::new();
            let end = loop {
                let mut chunk = [0u8; 4096];
                let n = stream.read(&mut chunk).unwrap();
                assert!(n > 0);
                bytes.extend_from_slice(&chunk[..n]);
                if let Some(offset) = bytes.windows(4).position(|window| window == b"\r\n\r\n") {
                    break offset + 4;
                }
            };
            let headers = String::from_utf8(bytes[..end].to_vec()).unwrap();
            let length: usize = headers
                .lines()
                .find_map(|line| {
                    line.to_ascii_lowercase()
                        .strip_prefix("content-length:")
                        .and_then(|v| v.trim().parse().ok())
                })
                .unwrap();
            while bytes.len() - end < length {
                let mut chunk = [0u8; 4096];
                let n = stream.read(&mut chunk).unwrap();
                assert!(n > 0);
                bytes.extend_from_slice(&chunk[..n]);
            }
            if !close_without_reply {
                write!(stream, "HTTP/1.1 200 OK\r\n{response_headers}Content-Length: {}\r\nConnection: close\r\n\r\n", reply_body.len()).unwrap();
                stream.write_all(&reply_body).unwrap();
            }
            format!(
                "{headers}\nbody={}",
                String::from_utf8_lossy(&bytes[end..end + length])
            )
        })
    }

    fn ambiguous_header_exchange(headers: &'static str, expected_reason: &'static str) {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let upstream_addr = upstream.local_addr().unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream_with_headers(
            upstream,
            deliveries.clone(),
            false,
            br#"{"id":"local-provider"}"#.to_vec(),
            headers,
        );
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(config(dir.clone(), upstream_addr), tx).unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let controller = thread::spawn(move || {
            let ProviderCommand::Reserve { request, reply } =
                rx.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("native reserve must precede provider send");
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 7,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            let ProviderCommand::BeforeSend { reply, .. } =
                rx.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("durable send boundary absent");
            };
            reply.send(Ok(())).unwrap();
            let ProviderCommand::Outcome { outcome, reply, .. } =
                rx.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("upstream outcome absent");
            };
            match outcome {
                ProviderOutcome::Uncertain { reason, .. } => {
                    assert!(reason.contains(expected_reason), "{reason}");
                }
                _ => panic!("ambiguous Content-Type must not produce Received"),
            }
            reply.send(Ok(())).unwrap();
        });
        let body = br#"{"model":"operator-model","messages":[{"role":"user","content":"local"}]}"#;
        let response = post(gateway.local_addr(), TOKEN, body);
        assert!(response.starts_with("HTTP/1.1 502"), "{response}");
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        gateway.control().revoke();
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn missing_or_duplicate_upstream_content_type_is_uncertain() {
        ambiguous_header_exchange("", "Content-Type absent");
        ambiguous_header_exchange(
            "Content-Type: application/json\r\nContent-Type: text/event-stream\r\n",
            "duplicate Content-Type",
        );
    }

    #[test]
    fn local_provider_receives_only_after_permit_and_boundary_ack() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let upstream_addr = upstream.local_addr().unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(
            upstream,
            deliveries.clone(),
            false,
            br#"{"id":"local-provider"}"#.to_vec(),
        );
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(config(dir.clone(), upstream_addr), tx).unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let body = br#"{"model":"operator-model","messages":[{"role":"user","content":"local"}]}"#
            .to_vec();
        let expected = body.clone();
        let controller = thread::spawn(move || {
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => {
                    assert_eq!(request.exact_body, expected);
                    assert_eq!(request.lease.prompt_operation_id, 1);
                    reply
                        .send(Ok(ForwardPermit::Fresh {
                            attempt_id: 7,
                            lease: request.lease,
                            exact_body: request.exact_body,
                        }))
                        .unwrap();
                }
                _ => panic!("reserve must precede send"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend {
                    attempt_id, reply, ..
                } => {
                    assert_eq!(attempt_id, 7);
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("durable send boundary absent"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    attempt_id,
                    outcome,
                    reply,
                } => {
                    assert_eq!(attempt_id, 7);
                    match outcome {
                        ProviderOutcome::Received {
                            status,
                            exact_headers,
                            exact_body,
                            ..
                        } => {
                            assert_eq!(status, 200);
                            assert!(exact_headers
                                .windows(b"Content-Type: application/json".len())
                                .any(|window| window == b"Content-Type: application/json"));
                            assert_eq!(exact_body, br#"{"id":"local-provider"}"#);
                        }
                        _ => panic!("unexpected provider outcome"),
                    }
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("outcome missing"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Delivery {
                    attempt_id,
                    local_write_success,
                    reply,
                } => {
                    assert_eq!(attempt_id, 7);
                    assert!(local_write_success);
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("delivery acknowledgement missing"),
            }
        });
        let response = post(gateway.local_addr(), TOKEN, &body);
        assert!(response.starts_with("HTTP/1.1 200"), "{response}");
        assert!(response.contains("local-provider"));
        controller.join().unwrap();
        let observed = upstream_thread.join().unwrap();
        assert!(observed.contains("Authorization: Bearer private-provider-key"));
        assert!(!observed.contains(TOKEN));
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn refused_reserve_and_revoked_token_never_reach_upstream() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        upstream.set_nonblocking(true).unwrap();
        let (tx, rx) = mpsc::sync_channel(2);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let controller =
            thread::spawn(
                move || match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                    ProviderCommand::Reserve { reply, .. } => {
                        reply.send(Err("signed reserve refused".into())).unwrap()
                    }
                    _ => panic!("unexpected command"),
                },
            );
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let refused = post(gateway.local_addr(), TOKEN, body);
        assert!(refused.starts_with("HTTP/1.1 503"));
        controller.join().unwrap();
        gateway.control().revoke();
        let stale = post(gateway.local_addr(), TOKEN, body);
        assert!(stale.starts_with("HTTP/1.1 401"));
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn concurrent_request_gets_bounded_busy_reply_without_a_second_reserve() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        upstream.set_nonblocking(true).unwrap();
        let (tx, rx) = mpsc::sync_channel(2);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let address = gateway.local_addr();
        let first = thread::spawn(move || post(address, TOKEN, body));
        let ProviderCommand::Reserve { reply, .. } =
            rx.recv_timeout(Duration::from_secs(5)).unwrap()
        else {
            panic!("first request must await native reserve");
        };
        let busy = post(address, TOKEN, body);
        assert!(busy.starts_with("HTTP/1.1 503"), "{busy}");
        assert!(busy.contains("provider controller is busy"));
        assert!(rx.try_recv().is_err(), "busy request must not reserve");
        reply.send(Err("signed reserve refused".into())).unwrap();
        assert!(first.join().unwrap().starts_with("HTTP/1.1 503"));
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn lost_outcome_ack_does_not_deliver_or_send_again() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(
            upstream.try_clone().unwrap(),
            deliveries.clone(),
            false,
            br#"{"id":"once"}"#.to_vec(),
        );
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("first reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 21,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend { reply, .. } => reply.send(Ok(())).unwrap(),
                _ => panic!("send boundary expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    outcome: ProviderOutcome::Received { .. },
                    reply,
                    ..
                } => {
                    drop(reply); // Controller crash after receiving the exact upstream result.
                }
                _ => panic!("received outcome expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { reply, .. } => {
                    reply.send(Err("held attempt".into())).unwrap()
                }
                _ => panic!("retry must first ask controller"),
            }
            assert!(rx.recv_timeout(Duration::from_millis(200)).is_err());
        });
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let first = post(gateway.local_addr(), TOKEN, body);
        assert!(first.starts_with("HTTP/1.1 503"), "{first}");
        assert!(!first.contains("once"));
        let retry = post(gateway.local_addr(), TOKEN, body);
        assert!(retry.starts_with("HTTP/1.1 503"), "{retry}");
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        upstream.set_nonblocking(true).unwrap();
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn cached_replay_never_contacts_upstream_or_claims_a_new_delivery() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        upstream.set_nonblocking(true).unwrap();
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let body = br#"{"model":"operator-model","messages":[]}"#.to_vec();
        let expected = body.clone();
        let controller = thread::spawn(move || {
            for _ in 0..2 {
                match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                    ProviderCommand::Reserve { request, reply } => {
                        assert_eq!(request.exact_body, expected);
                        reply
                            .send(Ok(ForwardPermit::Replay {
                                lease: request.lease,
                                exact_body: request.exact_body,
                                status: 200,
                                content_type: "application/json".into(),
                                exact_response: br#"{"id":"cached"}"#.to_vec(),
                            }))
                            .unwrap();
                    }
                    _ => panic!("replay must only request cached reserve"),
                }
            }
            assert!(rx.recv_timeout(Duration::from_millis(200)).is_err());
        });
        for _ in 0..2 {
            let response = post(gateway.local_addr(), TOKEN, &body);
            assert!(response.starts_with("HTTP/1.1 200"), "{response}");
            assert!(response.contains("cached"));
        }
        controller.join().unwrap();
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn client_reset_before_local_reply_never_retries_upstream() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(
            upstream.try_clone().unwrap(),
            deliveries.clone(),
            false,
            br#"{"id":"sent"}"#.to_vec(),
        );
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let (outcome_ready_tx, outcome_ready_rx) = mpsc::channel();
        let (client_closed_tx, client_closed_rx) = mpsc::channel();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 22,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend { reply, .. } => reply.send(Ok(())).unwrap(),
                _ => panic!("send boundary expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    outcome: ProviderOutcome::Received { .. },
                    reply,
                    ..
                } => {
                    outcome_ready_tx.send(()).unwrap();
                    client_closed_rx
                        .recv_timeout(Duration::from_secs(5))
                        .unwrap();
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("received outcome expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Delivery {
                    attempt_id,
                    local_write_success: _,
                    reply,
                } => {
                    assert_eq!(attempt_id, 22);
                    // The client requests RST before Outcome ack, but a
                    // small write can still complete in the local kernel
                    // before that reset becomes visible. Either result must
                    // still make the next request consult this controller.
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("failed delivery must be retained"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { reply, .. } => {
                    reply.send(Err("delivery unresolved".into())).unwrap()
                }
                _ => panic!("retry must first ask controller"),
            }
        });
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let mut client = TcpStream::connect(gateway.local_addr()).unwrap();
        write!(client, "POST /v1/chat/completions HTTP/1.1\r\nHost: 127.0.0.1\r\nAuthorization: Bearer {TOKEN}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n", body.len()).unwrap();
        client.write_all(body).unwrap();
        outcome_ready_rx
            .recv_timeout(Duration::from_secs(5))
            .unwrap();
        let linger = libc::linger {
            l_onoff: 1,
            l_linger: 0,
        };
        let result = unsafe {
            libc::setsockopt(
                client.as_raw_fd(),
                libc::SOL_SOCKET,
                libc::SO_LINGER,
                (&linger as *const libc::linger).cast(),
                std::mem::size_of_val(&linger) as libc::socklen_t,
            )
        };
        assert_eq!(result, 0);
        drop(client);
        client_closed_tx.send(()).unwrap();
        let idle_deadline = Instant::now() + Duration::from_secs(5);
        while !gateway.control().is_idle() && Instant::now() < idle_deadline {
            thread::sleep(Duration::from_millis(10));
        }
        assert!(gateway.control().is_idle(), "first delivery did not finish");
        let retry = post(gateway.local_addr(), TOKEN, body);
        assert!(retry.starts_with("HTTP/1.1 503"), "{retry}");
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        upstream.set_nonblocking(true).unwrap();
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn expired_worker_deadline_rejects_late_reserve_without_upstream_send() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        upstream.set_nonblocking(true).unwrap();
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let shared = gateway.control().shared.clone();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            shared.lease.lock().unwrap().worker_deadline = Some(Instant::now());
            let _ = reply.send(Ok(ForwardPermit::Fresh {
                attempt_id: 31,
                lease: request.lease,
                exact_body: request.exact_body,
            }));
            assert!(rx.recv_timeout(Duration::from_millis(100)).is_err());
        });
        let response = post(
            gateway.local_addr(),
            TOKEN,
            br#"{"model":"operator-model","messages":[]}"#,
        );
        assert!(response.starts_with("HTTP/1.1 503"), "{response}");
        controller.join().unwrap();
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn expired_worker_deadline_rejects_late_send_boundary_ack() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        upstream.set_nonblocking(true).unwrap();
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let shared = gateway.control().shared.clone();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 32,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            let boundary = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend { reply, .. } => reply,
                _ => panic!("send boundary expected"),
            };
            shared.lease.lock().unwrap().worker_deadline = Some(Instant::now());
            // The receiver can still be in scope while NotSent is being
            // journaled. A late acknowledgement must not authorize curl.
            let _ = boundary.send(Ok(()));
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    outcome: ProviderOutcome::NotSent { .. },
                    reply,
                    ..
                } => reply.send(Ok(())).unwrap(),
                _ => panic!("expired boundary must retain NotSent"),
            }
        });
        let response = post(
            gateway.local_addr(),
            TOKEN,
            br#"{"model":"operator-model","messages":[]}"#,
        );
        assert!(response.starts_with("HTTP/1.1 503"), "{response}");
        controller.join().unwrap();
        assert_eq!(
            upstream.accept().unwrap_err().kind(),
            io::ErrorKind::WouldBlock
        );
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn hard_revoke_during_slow_outcome_ack_never_delivers_response() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(
            upstream.try_clone().unwrap(),
            deliveries.clone(),
            false,
            br#"{"id":"local-provider"}"#.to_vec(),
        );
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway =
            GatewayEndpoint::start(config(dir.clone(), upstream.local_addr().unwrap()), tx)
                .unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let (seen_tx, seen_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let controller = thread::spawn(move || {
            let ProviderCommand::Reserve { request, reply } =
                rx.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("reserve absent");
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 41,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            let ProviderCommand::BeforeSend { reply, .. } =
                rx.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("send boundary absent");
            };
            reply.send(Ok(())).unwrap();
            let ProviderCommand::Outcome { outcome, reply, .. } =
                rx.recv_timeout(Duration::from_secs(5)).unwrap()
            else {
                panic!("received outcome absent");
            };
            assert!(matches!(outcome, ProviderOutcome::Received { .. }));
            seen_tx.send(()).unwrap();
            release_rx.recv_timeout(Duration::from_secs(5)).unwrap();
            let _ = reply.send(Ok(()));
            assert!(rx.recv_timeout(Duration::from_millis(100)).is_err());
        });
        let address = gateway.local_addr();
        let client = thread::spawn(move || {
            let mut stream = TcpStream::connect(address).unwrap();
            stream
                .set_read_timeout(Some(Duration::from_secs(2)))
                .unwrap();
            let body = br#"{"model":"operator-model","messages":[]}"#;
            write!(stream, "POST /v1/chat/completions HTTP/1.1\r\nHost: 127.0.0.1\r\nAuthorization: Bearer {TOKEN}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n", body.len()).unwrap();
            stream.write_all(body).unwrap();
            let mut received = Vec::new();
            let _ = stream.read_to_end(&mut received);
            received
        });
        seen_rx.recv_timeout(Duration::from_secs(5)).unwrap();
        let stopped_at = Instant::now();
        gateway.control().revoke();
        release_tx.send(()).unwrap();
        let received = client.join().unwrap();
        assert!(stopped_at.elapsed() < Duration::from_secs(1));
        assert!(!received
            .windows(b"local-provider".len())
            .any(|window| window == b"local-provider"));
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn lost_upstream_reply_is_retained_as_uncertain_without_resend() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let upstream_addr = upstream.local_addr().unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(upstream, deliveries.clone(), true, Vec::new());
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(config(dir.clone(), upstream_addr), tx).unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 9,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend { reply, .. } => reply.send(Ok(())).unwrap(),
                _ => panic!("send boundary expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    outcome: ProviderOutcome::Uncertain { .. },
                    reply,
                    ..
                } => reply.send(Ok(())).unwrap(),
                _ => panic!("uncertain outcome expected"),
            }
        });
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let response = post(gateway.local_addr(), TOKEN, body);
        assert!(response.starts_with("HTTP/1.1 502"), "{response}");
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn upstream_echo_of_custody_key_is_never_returned_to_worker() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let upstream_addr = upstream.local_addr().unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(
            upstream,
            deliveries.clone(),
            false,
            br#"{"echo":"private-provider-key"}"#.to_vec(),
        );
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(config(dir.clone(), upstream_addr), tx).unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 10,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend { reply, .. } => reply.send(Ok(())).unwrap(),
                _ => panic!("send boundary expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    outcome: ProviderOutcome::Uncertain { reason, .. },
                    reply,
                    ..
                } => {
                    assert!(reason.contains("custody secret"));
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("secret-containing response must be withheld"),
            }
        });
        let body = br#"{"model":"operator-model","messages":[]}"#;
        let response = post(gateway.local_addr(), TOKEN, body);
        assert!(response.starts_with("HTTP/1.1 502"));
        assert!(!response.contains("private-provider-key"));
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn hard_revoke_kills_inflight_transport_without_waiting_for_controller() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let upstream_addr = upstream.local_addr().unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let observed = deliveries.clone();
        let upstream_thread = thread::spawn(move || {
            let (mut stream, _) = upstream.accept().unwrap();
            observed.fetch_add(1, Ordering::SeqCst);
            stream
                .set_read_timeout(Some(Duration::from_secs(5)))
                .unwrap();
            let mut bytes = [0u8; 4096];
            let _ = stream.read(&mut bytes).unwrap();
            // The fake upstream intentionally never replies while the lease
            // is active. Closing it later is not a retry or a successful call.
            thread::sleep(Duration::from_millis(500));
        });
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(config(dir.clone(), upstream_addr), tx).unwrap();
        gateway
            .control()
            .activate(lease(1, TOKEN), Instant::now() + Duration::from_secs(600))
            .unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit::Fresh {
                    attempt_id: 11,
                    lease: request.lease,
                    exact_body: request.exact_body,
                }))
                .unwrap();
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::BeforeSend { reply, .. } => reply.send(Ok(())).unwrap(),
                _ => panic!("send boundary expected"),
            }
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Outcome {
                    outcome: ProviderOutcome::Uncertain { .. },
                    reply,
                    ..
                } => reply.send(Ok(())).unwrap(),
                _ => panic!("revoke must retain uncertainty"),
            }
        });
        let address = gateway.local_addr();
        let client = thread::spawn(move || {
            let body = br#"{"model":"operator-model","messages":[]}"#;
            let mut stream = TcpStream::connect(address).unwrap();
            write!(stream, "POST /v1/chat/completions HTTP/1.1\r\nHost: 127.0.0.1\r\nAuthorization: Bearer {TOKEN}\r\nContent-Type: application/json\r\nContent-Length: {}\r\n\r\n", body.len()).unwrap();
            stream.write_all(body).unwrap();
            let mut response = Vec::new();
            let _ = stream.read_to_end(&mut response);
        });
        for _ in 0..100 {
            if deliveries.load(Ordering::SeqCst) > 0 {
                break;
            }
            thread::sleep(Duration::from_millis(10));
        }
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        let started = Instant::now();
        gateway.control().revoke();
        assert!(started.elapsed() < Duration::from_millis(250));
        client.join().unwrap();
        controller.join().unwrap();
        upstream_thread.join().unwrap();
        assert_eq!(deliveries.load(Ordering::SeqCst), 1);
        drop(gateway);
        fs::remove_dir_all(dir).unwrap();
    }
}
