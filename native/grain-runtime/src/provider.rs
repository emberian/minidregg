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
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender, TrySendError};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant};

const MAX_HEADER: usize = 16_384;
const MAX_REQUEST: usize = 1_048_576;
const MAX_RESPONSE: usize = 8_388_608;
const MAX_TOKEN: usize = 128;
const BRIDGE_WAIT: Duration = Duration::from_secs(300);

pub struct GatewayConfig {
    pub bind: SocketAddr,
    /// Exact upstream endpoint, including `/v1/chat/completions`.
    pub upstream_url: String,
    pub pinned_model: String,
    /// Never pass this to a worker process, its environment, or an HTTP reply.
    pub provider_key: String,
    pub private_dir: PathBuf,
    pub max_request_bytes: usize,
    pub max_response_bytes: usize,
    pub timeout: Duration,
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

pub struct ForwardPermit {
    pub attempt_id: u64,
    pub lease: LeaseId,
    /// Must equal the request bytes; a permit is never transferable to a
    /// changed model, request, generation, or prompt.
    pub exact_body: Vec<u8>,
}

pub enum ProviderOutcome {
    Received {
        status: u16,
        content_type: String,
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
}

struct LeaseState {
    active: Option<Lease>,
    last_token: Option<String>,
}

struct Shared {
    lease: Mutex<LeaseState>,
    revoked: AtomicBool,
    active_request: AtomicBool,
    last_permit_id: AtomicU64,
    curl: Mutex<Option<Child>>,
    client: Mutex<Option<TcpStream>>,
    stop: AtomicBool,
}

#[derive(Clone)]
pub struct GatewayControl {
    shared: Arc<Shared>,
}

impl GatewayControl {
    pub fn activate(&self, lease: Lease) -> Result<(), String> {
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
        self.shared.revoked.store(false, Ordering::SeqCst);
        Ok(())
    }

    /// Call synchronously from the hard-EOF callback, before native Mini I/O.
    /// It never waits for a provider reply or controller command.
    pub fn revoke(&self) {
        self.shared.revoked.store(true, Ordering::SeqCst);
        if let Ok(mut state) = self.shared.lease.lock() {
            state.active = None;
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

    fn current(&self, token: &str) -> Option<LeaseId> {
        if self.shared.revoked.load(Ordering::SeqCst) {
            return None;
        }
        let state = self.shared.lease.lock().ok()?;
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
            .and_then(|s| s.active.as_ref().map(|lease| lease.id == *id))
            .unwrap_or(false)
    }
}

pub struct GatewayEndpoint {
    address: SocketAddr,
    control: GatewayControl,
    listener_thread: Option<JoinHandle<()>>,
}

impl GatewayEndpoint {
    pub fn start(
        config: GatewayConfig,
        commands: SyncSender<ProviderCommand>,
    ) -> Result<Self, String> {
        validate_config(&config)?;
        let listener = TcpListener::bind(config.bind).map_err(|e| format!("provider bind: {e}"))?;
        listener.set_nonblocking(true).map_err(|e| e.to_string())?;
        let address = listener.local_addr().map_err(|e| e.to_string())?;
        let shared = Arc::new(Shared {
            lease: Mutex::new(LeaseState {
                active: None,
                last_token: None,
            }),
            revoked: AtomicBool::new(true),
            active_request: AtomicBool::new(false),
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
                    Ok((mut stream, _)) => {
                        if shared.active_request.swap(true, Ordering::SeqCst) {
                            let _ = stream.shutdown(Shutdown::Both);
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

fn read_request(stream: &mut TcpStream, max_body: usize) -> Result<HttpRequest, String> {
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
    stream: &mut TcpStream,
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

fn error_reply(stream: &mut TcpStream, status: u16, message: &str) {
    let body = json!({"error":{"message":message,"type":"gateway_error"}}).to_string();
    let _ = write_http(stream, status, "application/json", body.as_bytes());
}

fn serve_client(
    stream: &mut TcpStream,
    config: &GatewayConfig,
    shared: &Arc<Shared>,
    commands: &SyncSender<ProviderCommand>,
) {
    let request = match read_request(stream, config.max_request_bytes) {
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
    let permit = match wait_reply(&rx, &control, &lease, true) {
        Ok(permit) => permit,
        Err(_) => {
            error_reply(stream, 503, "provider reserve was refused or interrupted");
            return;
        }
    };
    if permit.attempt_id == 0 || permit.lease != lease || permit.exact_body != request.body {
        error_reply(stream, 503, "provider permit did not bind this request");
        return;
    }
    if shared
        .last_permit_id
        .fetch_max(permit.attempt_id, Ordering::SeqCst)
        >= permit.attempt_id
    {
        error_reply(stream, 503, "provider permit was already consumed");
        return;
    }
    let (tx, rx) = mpsc::channel();
    if commands
        .try_send(ProviderCommand::BeforeSend {
            attempt_id: permit.attempt_id,
            lease: lease.clone(),
            reply: tx,
        })
        .is_err()
        || wait_reply(&rx, &control, &lease, true).is_err()
    {
        report_outcome(
            commands,
            permit.attempt_id,
            ProviderOutcome::NotSent {
                reason: "send boundary not acknowledged".into(),
            },
        );
        error_reply(stream, 503, "provider send boundary was not acknowledged");
        return;
    }
    let outcome = forward(config, shared, &control, &lease, &permit);
    let reply = match &outcome {
        ProviderOutcome::Received {
            status,
            content_type,
            exact_body,
        } => Some((*status, content_type.clone(), exact_body.clone())),
        _ => None,
    };
    if !report_outcome(commands, permit.attempt_id, outcome) {
        error_reply(
            stream,
            503,
            "provider outcome is pending controller recovery",
        );
        return;
    }
    if let Some((status, content_type, body)) = reply {
        let _ = write_http(stream, status, &content_type, &body);
    } else {
        error_reply(
            stream,
            502,
            "provider outcome is uncertain; no retry was sent",
        );
    }
}

fn wait_reply<T>(
    rx: &Receiver<Result<T, String>>,
    control: &GatewayControl,
    lease: &LeaseId,
    require_active: bool,
) -> Result<T, String> {
    let started = Instant::now();
    loop {
        if require_active && !control.still_active(lease) {
            return Err("prompt lease revoked".into());
        }
        if started.elapsed() >= BRIDGE_WAIT {
            return Err("controller reply deadline".into());
        }
        match rx.recv_timeout(Duration::from_millis(20)) {
            Ok(result) => return result,
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
) -> bool {
    let (tx, rx) = mpsc::channel();
    let mut command = ProviderCommand::Outcome {
        attempt_id,
        outcome,
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

fn response_headers(bytes: &[u8]) -> Result<(u16, String), String> {
    let text = std::str::from_utf8(bytes).map_err(|_| "provider headers are not UTF-8")?;
    let mut status = None;
    let mut content_type = None;
    for line in text.lines() {
        let line = line.trim_end_matches('\r');
        if line.starts_with("HTTP/") {
            let code = line
                .split_whitespace()
                .nth(1)
                .ok_or("provider status absent")?;
            let parsed = code.parse::<u16>().map_err(|_| "provider status invalid")?;
            if !(100..=599).contains(&parsed) {
                return Err("provider status invalid".into());
            }
            status = Some(parsed);
            content_type = None;
        } else if let Some((name, value)) = line.split_once(':') {
            if name.eq_ignore_ascii_case("content-encoding")
                && !value.trim().eq_ignore_ascii_case("identity")
            {
                return Err("provider response used unsupported content encoding".into());
            }
            if name.eq_ignore_ascii_case("content-type") {
                let value = value.trim();
                if value.len() > 128 || value.bytes().any(|b| !(0x20..=0x7e).contains(&b)) {
                    return Err("provider content type invalid".into());
                }
                content_type = Some(value.to_owned());
            }
        }
    }
    let status = status.ok_or("provider status absent")?;
    if status < 200 {
        return Err("provider final response absent".into());
    }
    Ok((
        status,
        content_type.unwrap_or_else(|| "application/json".into()),
    ))
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
    permit: &ForwardPermit,
) -> ProviderOutcome {
    if !control.still_active(lease) {
        return ProviderOutcome::NotSent {
            reason: "prompt lease revoked before dispatch".into(),
        };
    }
    let prefix = format!("provider-{:016}", permit.attempt_id);
    let request_path = config.private_dir.join(format!("{prefix}.request"));
    let body_path = config.private_dir.join(format!("{prefix}.response"));
    let header_path = config.private_dir.join(format!("{prefix}.headers"));
    if let Err(reason) = write_private(&request_path, &permit.exact_body)
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
        if guard.active.as_ref().map(|active| &active.id) != Some(lease) {
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
    if partial_body
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
        exact_body: partial_body,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
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
            upstream_url: format!("http://{upstream}/v1/chat/completions"),
            pinned_model: "operator-model".into(),
            provider_key: "private-provider-key".into(),
            private_dir: dir,
            max_request_bytes: 16_384,
            max_response_bytes: 16_384,
            timeout: Duration::from_secs(5),
        }
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
                write!(stream, "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", reply_body.len()).unwrap();
                stream.write_all(&reply_body).unwrap();
            }
            format!(
                "{headers}\nbody={}",
                String::from_utf8_lossy(&bytes[end..end + length])
            )
        })
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
        gateway.control().activate(lease(1, TOKEN)).unwrap();
        let body = br#"{"model":"operator-model","messages":[{"role":"user","content":"local"}]}"#
            .to_vec();
        let expected = body.clone();
        let controller = thread::spawn(move || {
            match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => {
                    assert_eq!(request.exact_body, expected);
                    assert_eq!(request.lease.prompt_operation_id, 1);
                    reply
                        .send(Ok(ForwardPermit {
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
                            status, exact_body, ..
                        } => {
                            assert_eq!(status, 200);
                            assert_eq!(exact_body, br#"{"id":"local-provider"}"#);
                        }
                        _ => panic!("unexpected provider outcome"),
                    }
                    reply.send(Ok(())).unwrap();
                }
                _ => panic!("outcome missing"),
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
        gateway.control().activate(lease(1, TOKEN)).unwrap();
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
    fn lost_upstream_reply_is_retained_as_uncertain_without_resend() {
        let dir = test_dir();
        let upstream = TcpListener::bind("127.0.0.1:0").unwrap();
        let upstream_addr = upstream.local_addr().unwrap();
        let deliveries = Arc::new(AtomicUsize::new(0));
        let upstream_thread = fake_upstream(upstream, deliveries.clone(), true, Vec::new());
        let (tx, rx) = mpsc::sync_channel(4);
        let gateway = GatewayEndpoint::start(config(dir.clone(), upstream_addr), tx).unwrap();
        gateway.control().activate(lease(1, TOKEN)).unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit {
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
        gateway.control().activate(lease(1, TOKEN)).unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit {
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
        gateway.control().activate(lease(1, TOKEN)).unwrap();
        let controller = thread::spawn(move || {
            let (request, reply) = match rx.recv_timeout(Duration::from_secs(5)).unwrap() {
                ProviderCommand::Reserve { request, reply } => (request, reply),
                _ => panic!("reserve expected"),
            };
            reply
                .send(Ok(ForwardPermit {
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
