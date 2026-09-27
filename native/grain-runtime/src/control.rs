//! Persistent controller socket and unprivileged SSH stdio connector.
//!
//! The socket belongs to the long-lived controller. A connector holds no Mini
//! authority and may disappear at any point without taking the controller or
//! its supervised child with it.
use serde_json::{json, Value};
use std::fs;
use std::io::{self, Read, Write};
use std::net::Shutdown;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, SyncSender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const MAX_LINE: u64 = 16_384;
const MAX_TOOL_FRAME: usize = 262_144;
const QUEUE: usize = 128;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    Hard,
    Soft,
    Inspect,
}

#[derive(Debug)]
pub enum Event {
    Attached { id: u64, soft: bool },
    InspectAttached { id: u64 },
    Line { id: u64, text: String },
    Tool { id: u64, frame: Vec<u8> },
    Detached { id: u64, hard: bool },
}

pub struct AdminRequest {
    pub command: String,
    pub reply: mpsc::Sender<String>,
    pub deadline: Instant,
    pub phase: Arc<AtomicU8>,
}

pub struct AdminServer {
    pub requests: Receiver<AdminRequest>,
    stop: Arc<AtomicBool>,
    path: PathBuf,
    socket_identity: (u64, u64),
}

impl Drop for AdminServer {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        if let Ok(meta) = fs::symlink_metadata(&self.path) {
            if meta.file_type().is_socket() && (meta.dev(), meta.ino()) == self.socket_identity {
                let _ = fs::remove_file(&self.path);
            }
        }
    }
}

/// Separate local operator socket. The SSH forced-command connector never
/// opens this path and ordinary attachments cannot submit AdminRequest events.
pub fn start_admin(path: &Path) -> Result<AdminServer, String> {
    if !path.is_absolute() {
        return Err("admin socket path must be absolute".into());
    }
    let listener = UnixListener::bind(path).map_err(|e| format!("admin bind: {e}"))?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("admin socket mode: {e}"))?;
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let (tx, requests) = mpsc::sync_channel(8);
    let stop = Arc::new(AtomicBool::new(false));
    let thread_stop = stop.clone();
    let active = Arc::new(AtomicUsize::new(0));
    thread::spawn(move || {
        while !thread_stop.load(Ordering::SeqCst) {
            match listener.accept() {
                Ok((stream, _)) => {
                    if active.fetch_add(1, Ordering::SeqCst) >= 4 {
                        active.fetch_sub(1, Ordering::SeqCst);
                        continue;
                    }
                    let tx = tx.clone();
                    let active = active.clone();
                    thread::spawn(move || {
                        serve_admin_connection(stream, tx);
                        active.fetch_sub(1, Ordering::SeqCst);
                    });
                }
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(20));
                }
                Err(_) => break,
            }
        }
    });
    Ok(AdminServer {
        requests,
        stop,
        path: path.to_owned(),
        socket_identity: (meta.dev(), meta.ino()),
    })
}

fn serve_admin_connection(mut stream: UnixStream, tx: SyncSender<AdminRequest>) {
    let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
    let _ = stream.set_write_timeout(Some(Duration::from_secs(2)));
    let response = match read_line(&mut stream) {
        Ok(command) => {
            let (reply, recv) = mpsc::channel();
            let phase = Arc::new(AtomicU8::new(0));
            let deadline = Instant::now() + Duration::from_secs(300);
            if tx
                .try_send(AdminRequest {
                    command,
                    reply,
                    deadline,
                    phase: phase.clone(),
                })
                .is_err()
            {
                "admin queue full".to_owned()
            } else {
                match recv.recv_timeout(Duration::from_secs(300)) {
                    Ok(value) => value,
                    Err(_)
                        if phase
                            .compare_exchange(0, 3, Ordering::SeqCst, Ordering::SeqCst)
                            .is_ok() =>
                    {
                        "admin action expired before dispatch".to_owned()
                    }
                    Err(_) => {
                        "admin action may have begun; inspect durable journal and exact attempt"
                            .to_owned()
                    }
                }
            }
        }
        Err(error) => format!("invalid admin request: {error}"),
    };
    let _ = writeln!(stream, "{response}");
}

pub fn admin_call(path: &Path, command: &str) -> Result<String, String> {
    if !path.is_absolute() || command.contains('\n') || command.len() > MAX_LINE as usize {
        return Err("admin socket/command invalid".into());
    }
    let mut stream = UnixStream::connect(path).map_err(|e| format!("admin connect: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(310)))
        .map_err(|e| e.to_string())?;
    writeln!(stream, "{command}").map_err(|e| e.to_string())?;
    read_line(&mut stream).map_err(|e| e.to_string())
}

struct Attachment {
    id: u64,
    mode: Mode,
    framed: bool,
    output: SyncSender<Outbound>,
}
enum Outbound {
    Text(String),
    Terminal(Value),
}
struct State {
    next_id: u64,
    active: Option<Attachment>,
    detaching: bool,
}

/// The callback must be fast and nonblocking: signal the controller-owned
/// process group, then return. It is called while the attachment lock is held
/// to order hard EOF before any replacement attachment can become active.
pub type HardInterrupt = Arc<dyn Fn(u64) + Send + Sync + 'static>;

pub struct Server {
    pub events: Receiver<Event>,
    state: Arc<Mutex<State>>,
    stop: Arc<AtomicBool>,
    path: PathBuf,
    socket_identity: (u64, u64),
}

#[derive(Clone)]
pub struct OutputHandle {
    state: Arc<Mutex<State>>,
}

impl OutputHandle {
    /// Send one bounded foreground result or acknowledgement only to its
    /// original framed attachment.
    /// A missing reader never turns a retained Mini outcome into a retry.
    pub fn try_tool_event_for(&self, id: u64, event: Value) -> bool {
        if !matches!(
            event.get("type").and_then(Value::as_str),
            Some("tool-complete" | "tool-acknowledged")
        ) || !serde_json::to_vec(&event).is_ok_and(|bytes| bytes.len() <= 1_048_576)
        {
            return false;
        }
        self.state.lock().is_ok_and(|state| {
            state.active.as_ref().is_some_and(|active| {
                active.framed
                    && active.id == id
                    && active.output.try_send(Outbound::Terminal(event)).is_ok()
            })
        })
    }
    pub fn is_active_framed_attachment(&self, id: u64) -> bool {
        self.state.lock().is_ok_and(|state| {
            state
                .active
                .as_ref()
                .is_some_and(|active| active.framed && active.id == id)
        })
    }

    /// Drop display text if no frontend is attached or its output queue is full.
    pub fn try_output(&self, message: impl Into<String>) -> bool {
        let Ok(state) = self.state.lock() else {
            return false;
        };
        state
            .active
            .as_ref()
            .is_some_and(|a| a.output.try_send(Outbound::Text(message.into())).is_ok())
    }

    /// Send a source-owned presentation event only to the same framed
    /// attachment. A completed old prompt cannot mark a new attachment ready.
    pub fn try_terminal_event_for(&self, id: u64, event: Value) -> bool {
        if !matches!(
            event.get("type").and_then(Value::as_str),
            Some("state" | "prompt-complete")
        ) || !serde_json::to_vec(&event).is_ok_and(|bytes| bytes.len() <= 4096)
        {
            return false;
        }
        let Ok(state) = self.state.lock() else {
            return false;
        };
        state.active.as_ref().is_some_and(|active| {
            active.framed
                && active.id == id
                // A completion cannot be silently lost behind ACP output.
                // The socket writer has a finite timeout, so backpressure
                // either makes space or breaks the attachment.
                && active.output.send(Outbound::Terminal(event)).is_ok()
        })
    }
}

impl Server {
    /// Never waits for a frontend reader. False means no current attachment or
    /// its bounded output queue is full; the controller may drop display text.
    #[cfg(test)]
    pub fn try_output(&self, message: impl Into<String>) -> bool {
        self.output_handle().try_output(message)
    }

    pub fn output_handle(&self) -> OutputHandle {
        OutputHandle {
            state: self.state.clone(),
        }
    }

    #[cfg(test)]
    pub fn attachment(&self) -> Option<(u64, Mode)> {
        self.state
            .lock()
            .ok()
            .and_then(|state| state.active.as_ref().map(|active| (active.id, active.mode)))
    }
}

impl Drop for Server {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        // Do not unlink a replacement socket created by another controller.
        if let Ok(meta) = fs::symlink_metadata(&self.path) {
            if meta.file_type().is_socket() && (meta.dev(), meta.ino()) == self.socket_identity {
                let _ = fs::remove_file(&self.path);
            }
        }
    }
}

pub fn start(path: &Path, hard_interrupt: HardInterrupt) -> Result<Server, String> {
    if !path.is_absolute() {
        return Err("controller socket path must be absolute".into());
    }
    let listener = UnixListener::bind(path).map_err(|e| format!("bind {}: {e}", path.display()))?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("socket permissions: {e}"))?;
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    let identity = (meta.dev(), meta.ino());
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let (tx, events) = mpsc::sync_channel(QUEUE);
    let state = Arc::new(Mutex::new(State {
        next_id: 1,
        active: None,
        detaching: false,
    }));
    let stop = Arc::new(AtomicBool::new(false));
    let active_connections = Arc::new(AtomicUsize::new(0));
    let accept_state = state.clone();
    let accept_stop = stop.clone();
    thread::spawn(move || {
        while !accept_stop.load(Ordering::SeqCst) {
            match listener.accept() {
                Ok((stream, _)) => {
                    if active_connections.fetch_add(1, Ordering::SeqCst) >= 8 {
                        active_connections.fetch_sub(1, Ordering::SeqCst);
                        continue;
                    }
                    let state = accept_state.clone();
                    let tx = tx.clone();
                    let interrupt = hard_interrupt.clone();
                    let active_connections = active_connections.clone();
                    thread::spawn(move || {
                        serve_connection(stream, state, tx, interrupt);
                        active_connections.fetch_sub(1, Ordering::SeqCst);
                    });
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(20))
                }
                Err(_) => break,
            }
        }
    });
    Ok(Server {
        events,
        state,
        stop,
        path: path.to_owned(),
        socket_identity: identity,
    })
}

fn serve_connection(
    mut stream: UnixStream,
    state: Arc<Mutex<State>>,
    events: SyncSender<Event>,
    hard_interrupt: HardInterrupt,
) {
    let _ = stream.set_nonblocking(false);
    let _ = stream.set_read_timeout(Some(Duration::from_secs(10)));
    let Ok(first) = read_line(&mut stream) else {
        return;
    };
    let (mode, framed) = match first.as_str() {
        "attach hard" => (Mode::Hard, false),
        "attach soft" => (Mode::Soft, false),
        "attach terminal-v1 hard" => (Mode::Hard, true),
        "attach terminal-v1 soft" => (Mode::Soft, true),
        "attach terminal-v1 inspect" => (Mode::Inspect, true),
        _ => {
            let _ = stream.write_all(
                b"first line must be attach hard|soft or attach terminal-v1 hard|soft\n",
            );
            return;
        }
    };
    let (output, display) = mpsc::sync_channel::<Outbound>(QUEUE);
    let id = {
        let Ok(mut state) = state.lock() else {
            return;
        };
        if state.active.is_some() || state.detaching {
            let _ = stream.write_all(b"controller already has an attachment\n");
            return;
        }
        let id = state.next_id;
        let Some(next) = id.checked_add(1) else {
            return;
        };
        state.next_id = next;
        state.active = Some(Attachment {
            id,
            mode,
            framed,
            output,
        });
        let attached = if mode == Mode::Inspect {
            Event::InspectAttached { id }
        } else {
            Event::Attached {
                id,
                soft: mode == Mode::Soft,
            }
        };
        if events.try_send(attached).is_err() {
            state.active = None;
            return;
        }
        id
    };
    let _ = stream.set_read_timeout(None);
    let mut writer = match stream.try_clone() {
        Ok(s) => s,
        Err(_) => {
            detach(id, &state, &events, &hard_interrupt);
            return;
        }
    };
    let _ = writer.set_write_timeout(Some(Duration::from_secs(2)));
    if framed
        && write_frame(
            &mut writer,
            &json!({"v":1,"type":"socket-attached",
        "attachmentId":id,"mode":match mode {
            Mode::Soft => "soft", Mode::Hard => "hard", Mode::Inspect => "inspect"}}),
        )
        .is_err()
    {
        detach(id, &state, &events, &hard_interrupt);
        return;
    }
    thread::spawn(move || {
        for message in display {
            let result = match message {
                Outbound::Text(text) if framed => {
                    write_frame(&mut writer, &json!({"v":1,"type":"output","text":text}))
                }
                Outbound::Text(text) => writer.write_all(text.as_bytes()),
                Outbound::Terminal(event) if framed => write_frame(&mut writer, &event),
                Outbound::Terminal(_) => continue,
            };
            if result.is_err() {
                break;
            }
        }
        let _ = writer.shutdown(Shutdown::Both);
    });
    loop {
        match read_line(&mut stream) {
            Ok(line) if line == "disconnect" => break,
            Ok(line) if line.starts_with("tool-v1 ") => {
                if !framed || mode == Mode::Inspect {
                    break;
                }
                let size = line[8..].parse::<usize>();
                let Ok(size) = size else { break };
                if size == 0 || size > MAX_TOOL_FRAME || size.to_string() != line[8..] {
                    break;
                }
                let mut frame = vec![0; size];
                if stream.read_exact(&mut frame).is_err()
                    || events.try_send(Event::Tool { id, frame }).is_err()
                {
                    break;
                }
            }
            Ok(line)
                if mode == Mode::Inspect
                    && !line.starts_with("tool result ")
                    && !line.starts_with("tool ack ") =>
            {
                break
            }
            Ok(line) => {
                if events.try_send(Event::Line { id, text: line }).is_err() {
                    break;
                }
            }
            Err(_) => break,
        }
    }
    detach(id, &state, &events, &hard_interrupt);
}

fn write_frame(stream: &mut UnixStream, event: &Value) -> io::Result<()> {
    serde_json::to_writer(&mut *stream, event).map_err(io::Error::other)?;
    stream.write_all(b"\n")
}

fn detach(id: u64, state: &Mutex<State>, events: &SyncSender<Event>, interrupt: &HardInterrupt) {
    let Ok(mut guard) = state.lock() else {
        return;
    };
    if guard.active.as_ref().map(|a| a.id) != Some(id) {
        return;
    }
    let mode = guard.active.as_ref().unwrap().mode;
    if mode == Mode::Hard {
        interrupt(id);
    }
    guard.active = None;
    guard.detaching = true;
    drop(guard);
    // Sending can wait for controller progress, but physical interruption has
    // already happened and the detaching flag bars a replacement attachment.
    let _ = events.send(Event::Detached {
        id,
        hard: mode == Mode::Hard,
    });
    if let Ok(mut guard) = state.lock() {
        guard.detaching = false;
    }
}

fn read_line(stream: &mut UnixStream) -> io::Result<String> {
    read_line_bounded(stream, MAX_LINE as usize)
}

fn read_line_bounded(stream: &mut UnixStream, limit: usize) -> io::Result<String> {
    let mut bytes = Vec::new();
    loop {
        let mut byte = [0u8; 1];
        if stream.read(&mut byte)? == 0 {
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "connection closed",
            ));
        }
        if byte[0] == b'\n' {
            break;
        }
        if bytes.len() == limit {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "control line too long",
            ));
        }
        bytes.push(byte[0]);
    }
    if bytes.last() == Some(&b'\r') {
        bytes.pop();
    }
    String::from_utf8(bytes).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

/// Forward SSH forced-command stdin/stdout to the persistent controller. An
/// optional fixed mode sends the first attach line before accepting user input;
/// the original raw connector remains available to scripted clients. The
/// connector does not read config, keys, journals, or Mini authority data.
pub fn connect(path: &Path, mode: Option<&str>) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("controller socket path must be absolute".into());
    }
    let mut stream =
        UnixStream::connect(path).map_err(|e| format!("connect {}: {e}", path.display()))?;
    if let Some(mode) = mode {
        let attach = match mode {
            "hard" => b"attach hard\n".as_slice(),
            "soft" => b"attach soft\n".as_slice(),
            _ => return Err("attachment mode must be hard or soft".into()),
        };
        stream
            .write_all(attach)
            .map_err(|e| format!("send {mode} attachment: {e}"))?;
        // The socket can refuse a second attachment before any runtime event
        // is delivered. Read its first line before starting the stdin copier,
        // so that refusal exits even when SSH stdin is still open.
        let first = read_line(&mut stream)
            .map_err(|e| format!("{mode} attachment closed before a response: {e}"))?;
        if first == "controller already has an attachment"
            || first == "first line must be attach hard|soft"
            || first.starts_with("grain-runtime:")
        {
            return Err(format!("{mode} attachment refused: {first}"));
        }
        writeln!(io::stdout().lock(), "{first}").map_err(|e| format!("attachment output: {e}"))?;
    }
    let mut to_server = stream.try_clone().map_err(|e| e.to_string())?;
    thread::spawn(move || {
        let _ = io::copy(&mut io::stdin().lock(), &mut to_server);
        let _ = to_server.shutdown(Shutdown::Write);
    });
    let result = (|| -> Result<(), String> {
        let mut stdout = io::stdout().lock();
        let mut buffer = [0u8; 4096];
        loop {
            let count = stream.read(&mut buffer).map_err(|e| e.to_string())?;
            if count == 0 {
                return Ok(());
            }
            stdout
                .write_all(&buffer[..count])
                .and_then(|_| stdout.flush())
                .map_err(|e| e.to_string())?;
        }
    })();
    let _ = stream.shutdown(Shutdown::Both);
    result
}

/// One foreground tool request on the existing exclusive attachment. The
/// caller never receives a Mini key; loss after sending is an unknown result.
pub fn tool_connect(
    path: &Path,
    mode: Mode,
    request_id: &str,
    request: &[u8],
) -> Result<Value, String> {
    if !path.is_absolute() || request.is_empty() || request.len() > MAX_TOOL_FRAME {
        return Err("foreground tool socket or frame is invalid".into());
    }
    let mut stream = UnixStream::connect(path).map_err(|e| format!("tool connect: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(1810)))
        .map_err(|e| e.to_string())?;
    stream
        .write_all(match mode {
            Mode::Hard => b"attach terminal-v1 hard\n",
            Mode::Soft => b"attach terminal-v1 soft\n",
            Mode::Inspect => return Err("inspect attachment cannot dispatch a tool".into()),
        })
        .map_err(|e| format!("tool attach: {e}"))?;
    let attached: Value = serde_json::from_str(
        &read_line_bounded(&mut stream, 4096).map_err(|e| format!("tool attach: {e}"))?,
    )
    .map_err(|e| format!("tool attach frame: {e}"))?;
    if attached.get("type").and_then(Value::as_str) != Some("socket-attached") {
        return Err("foreground tool attachment refused".into());
    }
    stream
        .write_all(format!("tool-v1 {}\n", request.len()).as_bytes())
        .and_then(|_| stream.write_all(request))
        .map_err(|e| format!("tool frame send: {e}; outcome unknown"))?;
    loop {
        let line = read_line_bounded(&mut stream, 1_048_576)
            .map_err(|e| format!("tool result lost: {e}; inspect retained operation"))?;
        let frame: Value = serde_json::from_str(&line)
            .map_err(|e| format!("tool result frame: {e}; inspect retained operation"))?;
        if frame.get("type").and_then(Value::as_str) == Some("tool-complete") {
            if frame.get("requestId").and_then(Value::as_str) != Some(request_id) {
                return Err(format!(
                    "foreground completion identity differs; inspect requestId {request_id}"
                ));
            }
            return Ok(frame);
        }
    }
}

pub fn tool_result_connect(path: &Path, request_id: &str) -> Result<Value, String> {
    inspect_tool_connect(path, "result", request_id, "tool-complete")
}

pub fn tool_ack_connect(path: &Path, request_id: &str) -> Result<Value, String> {
    inspect_tool_connect(path, "ack", request_id, "tool-acknowledged")
}

fn inspect_tool_connect(
    path: &Path,
    verb: &str,
    request_id: &str,
    expected_type: &str,
) -> Result<Value, String> {
    if !path.is_absolute()
        || request_id.len() != 32
        || !request_id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("foreground result coordinates are invalid".into());
    }
    let mut stream = UnixStream::connect(path).map_err(|e| format!("result connect: {e}"))?;
    stream
        .set_read_timeout(Some(Duration::from_secs(30)))
        .map_err(|e| e.to_string())?;
    stream
        .write_all(b"attach terminal-v1 inspect\n")
        .map_err(|e| format!("result attach: {e}"))?;
    let attached: Value = serde_json::from_str(
        &read_line_bounded(&mut stream, 4096).map_err(|e| format!("result attach: {e}"))?,
    )
    .map_err(|e| format!("result attach frame: {e}"))?;
    if attached.get("type").and_then(Value::as_str) != Some("socket-attached") {
        return Err("foreground result attachment refused".into());
    }
    stream
        .write_all(format!("tool {verb} {request_id}\n").as_bytes())
        .map_err(|e| format!("result request: {e}"))?;
    loop {
        let line = read_line_bounded(&mut stream, 1_048_576)
            .map_err(|e| format!("retained result lost: {e}"))?;
        let frame: Value =
            serde_json::from_str(&line).map_err(|e| format!("retained result frame: {e}"))?;
        if frame.get("type").and_then(Value::as_str) == Some(expected_type) {
            if frame.get("requestId").and_then(Value::as_str) != Some(request_id) {
                return Err("foreground inspected requestId differs".into());
            }
            return Ok(frame);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn foreground_frame_exceeds_line_limit_and_inspect_is_read_only() {
        let dir = PathBuf::from("/tmp").join(format!("gt-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let socket = dir.join("control.sock");
        let (interrupt_tx, interrupt_rx) = mpsc::channel();
        let server = start(
            &socket,
            Arc::new(move |id| {
                let _ = interrupt_tx.send(id);
            }),
        )
        .unwrap();
        let mut stream = UnixStream::connect(&socket).unwrap();
        stream.write_all(b"attach terminal-v1 soft\n").unwrap();
        let id = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
            Event::Attached { id, soft: true } => id,
            other => panic!("unexpected attachment: {other:?}"),
        };
        let _ = read_line(&mut stream).unwrap();
        let frame = vec![b'a'; 24_000];
        stream
            .write_all(format!("tool-v1 {}\n", frame.len()).as_bytes())
            .unwrap();
        stream.write_all(&frame).unwrap();
        assert!(matches!(
            server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Tool { id: event_id, frame: received }
                if event_id == id && received == frame
        ));
        let completion = json!({"v":1,"type":"tool-complete","operationId":"71",
            "isError":false,"result":{"ok":true}});
        assert!(server
            .output_handle()
            .try_tool_event_for(id, completion.clone()));
        let observed: Value = serde_json::from_str(&read_line(&mut stream).unwrap()).unwrap();
        assert_eq!(observed, completion);
        drop(stream);
        assert!(matches!(
            server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Detached { hard: false, .. }
        ));
        let mut inspect = UnixStream::connect(&socket).unwrap();
        inspect.write_all(b"attach terminal-v1 inspect\n").unwrap();
        let inspect_id = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
            Event::InspectAttached { id } => id,
            other => panic!("unexpected inspect attachment: {other:?}"),
        };
        let hello: Value = serde_json::from_str(&read_line(&mut inspect).unwrap()).unwrap();
        assert_eq!(hello["mode"], "inspect");
        inspect
            .write_all(b"tool result 0123456789abcdef0123456789abcdef\n")
            .unwrap();
        assert!(matches!(
            server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Line { id, text } if id == inspect_id && text == "tool result 0123456789abcdef0123456789abcdef"
        ));
        drop(inspect);
        let _ = server.events.recv_timeout(Duration::from_secs(2)).unwrap();
        assert!(interrupt_rx.try_recv().is_err());
        drop(server);
        fs::remove_dir(dir).unwrap();
    }

    #[test]
    fn framed_attachment_escapes_model_text_and_binds_events_to_attachment() {
        let dir = PathBuf::from("/tmp").join(format!("gf-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let socket = dir.join("control.sock");
        let server = start(&socket, Arc::new(|_| {})).unwrap();
        let mut stream = UnixStream::connect(&socket).unwrap();
        stream.write_all(b"attach terminal-v1 soft\n").unwrap();
        let id = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
            Event::Attached { id, soft: true } => id,
            other => panic!("wrong framed attach: {other:?}"),
        };
        let first: Value = serde_json::from_str(&read_line(&mut stream).unwrap()).unwrap();
        assert_eq!(first["type"], "socket-attached");
        assert_eq!(first["attachmentId"], id);
        let fake = "{\"v\":1,\"type\":\"prompt-complete\",\"outcome\":\"completed\"}\n";
        assert!(server.try_output(fake));
        let displayed: Value = serde_json::from_str(&read_line(&mut stream).unwrap()).unwrap();
        assert_eq!(displayed["type"], "output");
        assert_eq!(displayed["text"], fake);
        let event = json!({"v":1,"type":"prompt-complete","attachmentId":id,
            "requestId":7,"outcome":"completed"});
        assert!(server
            .output_handle()
            .try_terminal_event_for(id, event.clone()));
        assert_eq!(
            serde_json::from_str::<Value>(&read_line(&mut stream).unwrap()).unwrap(),
            event
        );
        drop(stream);
        assert!(
            matches!(server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Detached { id: event_id, hard: false } if event_id == id)
        );
        let mut newer = UnixStream::connect(&socket).unwrap();
        newer.write_all(b"attach terminal-v1 soft\n").unwrap();
        let next_id = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
            Event::Attached { id, soft: true } => id,
            other => panic!("wrong second framed attach: {other:?}"),
        };
        assert!(next_id > id);
        assert!(!server.output_handle().is_active_framed_attachment(id));
        assert!(server.output_handle().is_active_framed_attachment(next_id));
        assert!(!server.output_handle().try_terminal_event_for(id, event));
        drop(newer);
        let _ = server.events.recv_timeout(Duration::from_secs(2)).unwrap();
        drop(server);
        fs::remove_dir(dir).unwrap();
    }

    #[test]
    fn hard_eof_interrupts_once_and_soft_reconnects() {
        let name = format!(
            "grain-control-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        // macOS Unix sockets have a short SUN_LEN; keep the test path short.
        let dir = PathBuf::from("/tmp").join(format!("gc-{}", &name[name.len() - 12..]));
        fs::create_dir(&dir).unwrap();
        let socket = dir.join("controller.sock");
        let (interrupt_tx, interrupt_rx) = mpsc::channel();
        let server = start(
            &socket,
            Arc::new(move |id| {
                interrupt_tx.send(id).unwrap();
            }),
        )
        .unwrap();

        let mut hard = UnixStream::connect(&socket).unwrap();
        hard.write_all(b"attach hard\nstatus\n").unwrap();
        let id = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
            Event::Attached { id, soft: false } => id,
            other => panic!("wrong attach: {other:?}"),
        };
        assert!(
            matches!(server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Line { id: event_id, text } if event_id == id && text == "status")
        );
        assert!(
            server.try_output("ok\n"),
            "attachment: {:?}",
            server.attachment()
        );
        assert_eq!(read_line(&mut hard).unwrap(), "ok");
        drop(hard);
        assert_eq!(
            interrupt_rx.recv_timeout(Duration::from_secs(2)).unwrap(),
            id
        );
        assert!(
            matches!(server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Detached { id: event_id, hard: true } if event_id == id)
        );

        let mut soft = UnixStream::connect(&socket).unwrap();
        soft.write_all(b"attach soft\n").unwrap();
        let newer = match server.events.recv_timeout(Duration::from_secs(2)).unwrap() {
            Event::Attached { id, soft: true } => id,
            other => panic!("wrong soft attach: {other:?}"),
        };
        assert!(newer > id);
        drop(soft);
        assert!(
            matches!(server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Detached { id: event_id, hard: false } if event_id == newer)
        );
        assert!(interrupt_rx.try_recv().is_err());

        drop(server);
        assert!(!socket.exists());
        fs::remove_dir(dir).unwrap();
    }

    #[test]
    fn mode_connector_reports_busy_attachment_without_waiting_for_ssh_input() {
        let dir = PathBuf::from("/tmp").join(format!(
            "gb-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        let socket = dir.join("controller.sock");
        let server = start(&socket, Arc::new(|_| {})).unwrap();
        let mut held = UnixStream::connect(&socket).unwrap();
        held.write_all(b"attach soft\n").unwrap();
        assert!(matches!(
            server.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Attached { soft: true, .. }
        ));
        let error = connect(&socket, Some("hard")).unwrap_err();
        assert!(error.contains("controller already has an attachment"));
        assert!(server.events.try_recv().is_err());
        drop(held);
        let _ = server.events.recv_timeout(Duration::from_secs(2)).unwrap();
        drop(server);
        fs::remove_dir(dir).unwrap();
    }

    #[test]
    fn admin_requests_use_a_separate_socket() {
        let dir = PathBuf::from("/tmp").join(format!("ga-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let ordinary_path = dir.join("control.sock");
        let admin_path = dir.join("admin.sock");
        let ordinary = start(&ordinary_path, Arc::new(|_| {})).unwrap();
        let admin = start_admin(&admin_path).unwrap();
        let mut connection = UnixStream::connect(&ordinary_path).unwrap();
        connection
            .write_all(b"attach soft\nreconcile effects\n")
            .unwrap();
        assert!(matches!(
            ordinary
                .events
                .recv_timeout(Duration::from_secs(2))
                .unwrap(),
            Event::Attached { soft: true, .. }
        ));
        assert!(
            matches!(ordinary.events.recv_timeout(Duration::from_secs(2)).unwrap(),
            Event::Line { text, .. } if text == "reconcile effects")
        );
        assert!(admin.requests.try_recv().is_err());
        let path = admin_path.clone();
        let caller = thread::spawn(move || admin_call(&path, "reconcile effects"));
        let request = admin.requests.recv_timeout(Duration::from_secs(2)).unwrap();
        assert_eq!(request.command, "reconcile effects");
        request.reply.send("ok".into()).unwrap();
        assert_eq!(caller.join().unwrap().unwrap(), "ok");
        drop(connection);
        drop(admin);
        drop(ordinary);
        fs::remove_dir(dir).unwrap();
    }
}
