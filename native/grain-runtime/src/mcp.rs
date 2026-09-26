//! Stdio MCP edge. This process has no Mini signing key; each call is sent to
//! the separately supervised controller over an owner-only Unix socket.
use serde_json::{json, Value};
use std::fs;
use std::io::{self, BufRead, Read, Write};
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::mpsc::{self, Receiver, Sender, SyncSender};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

const MAX_WORKER_WALL: Duration = Duration::from_secs(1800);
const MCP_DELIVERY_GRACE: Duration = Duration::from_secs(10);
const MAX_PROXY_WAIT: Duration = Duration::from_secs(1810);

pub struct BrokerRequest {
    pub name: String,
    pub arguments: Value,
    pub prompt_epoch: u64,
    pub reply: Sender<Value>,
}

pub struct BrokerEndpoint {
    pub requests: Receiver<BrokerRequest>,
    stop: Arc<AtomicBool>,
    path: PathBuf,
    socket_identity: (u64, u64),
    prompt_epoch: Arc<AtomicU64>,
}

impl BrokerEndpoint {
    pub fn activate_prompt(&self) {
        self.prompt_epoch.store(1, Ordering::SeqCst);
    }

    pub fn deactivate_prompt(&self) {
        self.prompt_epoch.store(0, Ordering::SeqCst);
    }
}

impl Drop for BrokerEndpoint {
    fn drop(&mut self) {
        self.stop.store(true, Ordering::SeqCst);
        if let Ok(meta) = fs::symlink_metadata(&self.path) {
            if meta.file_type().is_socket() && (meta.dev(), meta.ino()) == self.socket_identity {
                let _ = fs::remove_file(&self.path);
            }
        }
    }
}

pub fn start_broker(path: &Path, worker_wall: Duration) -> Result<BrokerEndpoint, String> {
    if worker_wall.is_zero() || worker_wall > MAX_WORKER_WALL {
        return Err("MCP broker worker wall time must be 1..1800 seconds".into());
    }
    let response_timeout = worker_wall + MCP_DELIVERY_GRACE;
    let listener = UnixListener::bind(path).map_err(|e| format!("MCP broker bind: {e}"))?;
    fs::set_permissions(path, fs::Permissions::from_mode(0o600))
        .map_err(|e| format!("MCP broker mode: {e}"))?;
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    let socket_identity = (meta.dev(), meta.ino());
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let (tx, rx) = mpsc::sync_channel(8);
    let stop = Arc::new(AtomicBool::new(false));
    let active = Arc::new(AtomicUsize::new(0));
    let prompt_epoch = Arc::new(AtomicU64::new(0));
    let thread_stop = stop.clone();
    let thread_epoch = prompt_epoch.clone();
    thread::spawn(move || {
        while !thread_stop.load(Ordering::SeqCst) {
            match listener.accept() {
                Ok((stream, _)) => {
                    if active.fetch_add(1, Ordering::SeqCst) >= 8 {
                        active.fetch_sub(1, Ordering::SeqCst);
                        continue;
                    }
                    let tx = tx.clone();
                    let active = active.clone();
                    let epoch = thread_epoch.clone();
                    thread::spawn(move || {
                        serve_broker_connection(stream, tx, epoch, response_timeout);
                        active.fetch_sub(1, Ordering::SeqCst);
                    });
                }
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                    thread::sleep(Duration::from_millis(20))
                }
                Err(_) => break,
            }
        }
    });
    Ok(BrokerEndpoint {
        requests: rx,
        stop,
        path: path.to_path_buf(),
        socket_identity,
        prompt_epoch,
    })
}

fn serve_broker_connection(
    mut stream: UnixStream,
    tx: SyncSender<BrokerRequest>,
    epoch: Arc<AtomicU64>,
    response_timeout: Duration,
) {
    if stream
        .set_write_timeout(Some(Duration::from_secs(5)))
        .is_err()
    {
        return;
    }
    let mut line = String::new();
    if io::BufReader::new(
        DeadlineRead {
            stream: &mut stream,
            deadline: Instant::now() + Duration::from_secs(5),
        }
        .take(65_537),
    )
    .read_line(&mut line)
    .is_err()
        || line.is_empty()
        || line.len() > 65_536
        || !line.ends_with('\n')
    {
        return;
    }
    let Ok(req) = serde_json::from_str::<Value>(&line) else {
        return;
    };
    let Some(name) = req.get("name").and_then(Value::as_str) else {
        return;
    };
    let prompt_epoch = epoch.load(Ordering::SeqCst);
    let (reply_tx, reply_rx) = mpsc::channel();
    if tx
        .try_send(BrokerRequest {
            name: name.to_owned(),
            arguments: req.get("arguments").cloned().unwrap_or(Value::Null),
            prompt_epoch,
            reply: reply_tx,
        })
        .is_err()
    {
        let _ = writeln!(
            stream,
            "{}",
            json!({"isError":true,"text":"broker queue is full"})
        );
        return;
    }
    let response = reply_rx.recv_timeout(response_timeout).unwrap_or_else(|_| {
        json!({"isError":true,"text":"tool delivery timed out or reply was lost; outcome unknown"})
    });
    let _ = writeln!(stream, "{response}");
}

fn call_controller(path: &Path, name: &str, arguments: Value) -> Value {
    call_controller_with_timeout(path, name, arguments, MAX_PROXY_WAIT)
}

fn call_controller_with_timeout(
    path: &Path,
    name: &str,
    arguments: Value,
    response_timeout: Duration,
) -> Value {
    let result = (|| -> Result<Value, String> {
        let mut stream = UnixStream::connect(path).map_err(|e| e.to_string())?;
        stream
            .set_write_timeout(Some(Duration::from_secs(5)))
            .map_err(|e| e.to_string())?;
        writeln!(stream, "{}", json!({"name":name,"arguments":arguments}))
            .map_err(|e| e.to_string())?;
        let mut line = String::new();
        io::BufReader::new(DeadlineRead {
            stream: &mut stream,
            deadline: Instant::now() + response_timeout,
        })
        .take(16_777_217)
        .read_line(&mut line)
        .map_err(|e| e.to_string())?;
        if line.len() > 16_777_216 || !line.ends_with('\n') {
            return Err("controller reply exceeds 16 MiB".into());
        }
        serde_json::from_str(&line).map_err(|e| e.to_string())
    })();
    result.unwrap_or_else(|e| {
        json!({"isError":true,"text":format!("Mini tool delivery timed out or reply unavailable; outcome unknown: {e}")})
    })
}

struct DeadlineRead<'a> {
    stream: &'a mut UnixStream,
    deadline: Instant,
}

impl Read for DeadlineRead<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "MCP reply deadline exceeded",
            ));
        }
        self.stream.set_read_timeout(Some(remaining))?;
        self.stream.read(buf)
    }
}

pub fn serve_stdio(path: &Path) -> Result<(), String> {
    if !path.is_absolute() {
        return Err("MCP broker socket must be absolute".into());
    }
    let stdin = io::stdin();
    let mut input = stdin.lock();
    let mut stdout = io::stdout().lock();
    loop {
        let mut line = String::new();
        input
            .by_ref()
            .take(65_537)
            .read_line(&mut line)
            .map_err(|e| e.to_string())?;
        if line.is_empty() {
            break;
        }
        if line.len() > 65_536 || !line.ends_with('\n') {
            return Err("MCP frame exceeds 64 KiB".into());
        }
        let msg: Value = serde_json::from_str(&line).map_err(|e| e.to_string())?;
        let Some(id) = msg.get("id") else {
            continue;
        };
        let method = msg.get("method").and_then(Value::as_str).unwrap_or("");
        let result = match method {
            "initialize" => json!({"protocolVersion":msg.pointer("/params/protocolVersion")
                .and_then(Value::as_str).unwrap_or("2025-06-18"),
                "capabilities":{"tools":{}},
                "serverInfo":{"name":"mini-grain","version":"0.1.0"}}),
            "ping" => json!({}),
            "tools/list" => json!({"tools":[
                {"name":"mini_grain_status","description":"Read the signed Mini task resource",
                 "inputSchema":{"type":"object","properties":{}}},
                {"name":"mini_read_resource","description":"Read one operator-allowlisted Mini resource with signed delegated observe authority",
                 "inputSchema":{"type":"object","properties":{"name":{"type":"string"}},"required":["name"],"additionalProperties":false}},
                {"name":"mini_publish","description":"Atomically settle a delegated grain allowance and publish Mini resource targets",
                 "inputSchema":{"type":"object","properties":{"publications":{"type":"array","items":{"type":"object"}}},"required":["publications"]}}
            ]}),
            "tools/call" => {
                let name = msg
                    .pointer("/params/name")
                    .and_then(Value::as_str)
                    .unwrap_or("");
                let arguments = msg
                    .pointer("/params/arguments")
                    .cloned()
                    .unwrap_or(Value::Null);
                let response = call_controller(path, name, arguments);
                json!({"content":[{"type":"text","text":response.get("text").and_then(Value::as_str).unwrap_or("tool returned no text")}],
                    "isError":response.get("isError").and_then(Value::as_bool).unwrap_or(true)})
            }
            _ => json!({"error":format!("unsupported MCP method {method}")}),
        };
        let response = json!({"jsonrpc":"2.0","id":id,"result":result});
        writeln!(stdout, "{response}")
            .and_then(|_| stdout.flush())
            .map_err(|e| e.to_string())?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::AtomicUsize;

    static NEXT_SOCKET: AtomicUsize = AtomicUsize::new(1);

    #[test]
    fn broker_deadline_reports_unknown_delivery_without_claiming_settlement() {
        let (mut client, broker) = UnixStream::pair().unwrap();
        client
            .set_read_timeout(Some(Duration::from_secs(1)))
            .unwrap();
        let (tx, rx) = mpsc::sync_channel(1);
        let epoch = Arc::new(AtomicU64::new(1));
        let worker = thread::spawn(move || {
            serve_broker_connection(broker, tx, epoch, Duration::from_millis(30));
        });
        writeln!(client, "{}", json!({"name":"mini_publish","arguments":{}})).unwrap();
        let request = rx.recv_timeout(Duration::from_secs(1)).unwrap();
        assert_eq!(request.prompt_epoch, 1);
        let mut reply = String::new();
        io::BufReader::new(&client).read_line(&mut reply).unwrap();
        let value: Value = serde_json::from_str(&reply).unwrap();
        assert_eq!(value["isError"], true);
        assert!(value["text"].as_str().unwrap().contains("outcome unknown"));
        assert!(request.reply.send(json!({"isError":false})).is_err());
        worker.join().unwrap();
    }

    #[test]
    fn proxy_read_has_total_deadline_and_preserves_unknown_outcome() {
        let socket = std::env::temp_dir().join(format!(
            "mini-mcp-timeout-{}-{}",
            std::process::id(),
            NEXT_SOCKET.fetch_add(1, Ordering::SeqCst)
        ));
        let listener = UnixListener::bind(&socket).unwrap();
        let server = thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut request = String::new();
            io::BufReader::new(&stream).read_line(&mut request).unwrap();
            assert!(request.contains("mini_publish"));
            stream.write_all(b"{\"isError\":").unwrap();
            thread::sleep(Duration::from_millis(100));
        });
        let result = call_controller_with_timeout(
            &socket,
            "mini_publish",
            json!({}),
            Duration::from_millis(30),
        );
        assert_eq!(result["isError"], true);
        assert!(result["text"].as_str().unwrap().contains("outcome unknown"));
        server.join().unwrap();
        fs::remove_file(socket).unwrap();
    }
}
