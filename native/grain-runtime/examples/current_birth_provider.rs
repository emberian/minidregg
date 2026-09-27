//! Deterministic loopback provider for the isolated hosted app/session gate.
//!
//! This is an explicit Cargo example, not part of the grain-runtime server.
//! It supplies model-shaped tool calls to a real Hermes worker; Mini remains
//! responsible for authoring, admission, receipts, and recovery.
use serde_json::{json, Value};
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

const MAX_HEADERS: usize = 16_384;
const MAX_BODY: usize = 1_048_576;

fn main() {
    if let Err(error) = run() {
        eprintln!("current-birth provider fixture: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    if args.next().as_deref() != Some("--port") {
        return Err("usage: current_birth_provider --port PORT --state-dir PRIVATE_DIR".into());
    }
    let port: u16 = args
        .next()
        .ok_or("port absent")?
        .parse()
        .map_err(|_| "invalid port")?;
    if args.next().as_deref() != Some("--state-dir") {
        return Err("state directory option absent".into());
    }
    let directory = PathBuf::from(args.next().ok_or("state directory absent")?);
    if args.next().is_some() || !directory.is_absolute() {
        return Err("state directory must be an absolute path".into());
    }
    let metadata = fs::symlink_metadata(&directory).map_err(|e| e.to_string())?;
    if !metadata.file_type().is_dir() || metadata.permissions().mode() & 0o077 != 0 {
        return Err("state directory must be an owner-private directory".into());
    }
    let stage = directory.join("stage");
    let mut initial = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&stage)
        .map_err(|e| format!("fresh fixture stage: {e}"))?;
    initial.write_all(b"0\n").map_err(|e| e.to_string())?;
    initial.sync_all().map_err(|e| e.to_string())?;
    fs::File::open(&directory)
        .and_then(|file| file.sync_all())
        .map_err(|e| e.to_string())?;
    let listener = TcpListener::bind(("127.0.0.1", port)).map_err(|e| e.to_string())?;
    for incoming in listener.incoming() {
        let mut stream = incoming.map_err(|e| e.to_string())?;
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| e.to_string())?;
        stream
            .set_write_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| e.to_string())?;
        if let Err(error) = handle(&mut stream, &directory) {
            eprintln!("current-birth provider fixture: request refused: {error}");
        }
    }
    Ok(())
}

fn request(stream: &mut TcpStream) -> Result<Value, String> {
    let mut header = Vec::new();
    while !header.ends_with(b"\r\n\r\n") {
        if header.len() >= MAX_HEADERS {
            return Err("HTTP headers exceed bound".into());
        }
        let mut byte = [0u8; 1];
        stream.read_exact(&mut byte).map_err(|e| e.to_string())?;
        header.push(byte[0]);
    }
    let text = std::str::from_utf8(&header).map_err(|_| "HTTP headers are not UTF-8")?;
    let mut lines = text.split("\r\n");
    if lines.next() != Some("POST /v1/chat/completions HTTP/1.1") {
        return Err("unexpected HTTP route".into());
    }
    let mut length = None;
    for line in lines {
        let Some((name, value)) = line.split_once(':') else {
            continue;
        };
        if name.eq_ignore_ascii_case("content-length") {
            if length.is_some() {
                return Err("duplicate Content-Length".into());
            }
            length = Some(
                value
                    .trim()
                    .parse::<usize>()
                    .map_err(|_| "invalid Content-Length")?,
            );
        }
    }
    let length = length.ok_or("Content-Length absent")?;
    if length == 0 || length > MAX_BODY {
        return Err("request body exceeds bound".into());
    }
    let mut body = vec![0; length];
    stream.read_exact(&mut body).map_err(|e| e.to_string())?;
    serde_json::from_slice(&body).map_err(|_| "request JSON invalid".into())
}

fn chunk(model: &str, delta: Value, finish: Option<&str>) -> Value {
    json!({"id":"chatcmpl-mini-current-birth-fixture",
        "object":"chat.completion.chunk","created":1,"model":model,
        "choices":[{"index":0,"delta":delta,"finish_reason":finish}]})
}

fn event_stream(model: &str, tool: Option<(&str, &str, Value)>, final_text: &str) -> Vec<u8> {
    let (first, finish) = if let Some((name, call_id, arguments)) = tool {
        (
            chunk(
                model,
                json!({"role":"assistant","tool_calls":[{
            "index":0,"id":call_id,"type":"function",
            "function":{"name":name,"arguments":arguments.to_string()}}]}),
                None,
            ),
            "tool_calls",
        )
    } else {
        (
            chunk(
                model,
                json!({"role":"assistant","content":final_text}),
                None,
            ),
            "stop",
        )
    };
    // These are synthetic, bounded fixture counts, not a claim about real
    // provider billing. The metered Host route requires one terminal usage
    // event before [DONE], including on tool-call turns.
    let usage = json!({"id":"chatcmpl-mini-current-birth-fixture",
        "object":"chat.completion.chunk","created":1,"model":model,
        "choices":[],"usage":{"prompt_tokens":1,"completion_tokens":1,"total_tokens":2}});
    format!(
        "data: {}\n\ndata: {}\n\ndata: {}\n\ndata: [DONE]\n\n",
        first,
        chunk(model, json!({}), Some(finish)),
        usage
    )
    .into_bytes()
}

fn advance(directory: &Path, next: u8) -> Result<(), String> {
    let pending = directory.join("stage.next");
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&pending)
        .map_err(|e| e.to_string())?;
    writeln!(file, "{next}").map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())?;
    fs::rename(pending, directory.join("stage")).map_err(|e| e.to_string())?;
    fs::File::open(directory)
        .and_then(|dir| dir.sync_all())
        .map_err(|e| e.to_string())
}

fn send(
    stream: &mut TcpStream,
    status: &str,
    content_type: &str,
    body: &[u8],
) -> Result<(), String> {
    write!(stream, "HTTP/1.1 {status}\r\nContent-Type: {content_type}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", body.len())
        .and_then(|_| stream.write_all(body)).and_then(|_| stream.flush())
        .map_err(|e| e.to_string())
}

fn refuse(stream: &mut TcpStream, status: &str, reason: &str) -> Result<(), String> {
    let body = json!({"error":{"message":reason,"type":"invalid_request_error"}}).to_string();
    send(stream, status, "application/json", body.as_bytes())?;
    Err(reason.into())
}

fn handle(stream: &mut TcpStream, directory: &Path) -> Result<(), String> {
    let request = match request(stream) {
        Ok(value) => value,
        Err(reason) => {
            let body =
                json!({"error":{"message":reason,"type":"invalid_request_error"}}).to_string();
            send(
                stream,
                "400 Bad Request",
                "application/json",
                body.as_bytes(),
            )?;
            return Err(reason);
        }
    };
    let Some(model) = request
        .get("model")
        .and_then(Value::as_str)
        .filter(|model| model.len() <= 128)
    else {
        return refuse(stream, "409 Conflict", "model absent or too long");
    };
    let Some(tools) = request.get("tools").and_then(Value::as_array) else {
        return refuse(stream, "409 Conflict", "tools absent");
    };
    if request.get("stream") != Some(&Value::Bool(true)) {
        return refuse(stream, "409 Conflict", "streaming tool request required");
    }
    let has_tool = |name: &str| {
        tools
            .iter()
            .any(|tool| tool.pointer("/function/name").and_then(Value::as_str) == Some(name))
    };
    let has_result = |call_id: &str| {
        request
            .get("messages")
            .and_then(Value::as_array)
            .is_some_and(|messages| {
                messages.iter().any(|message| {
                    message.get("role").and_then(Value::as_str) == Some("tool")
                        && message.get("tool_call_id").and_then(Value::as_str) == Some(call_id)
                })
            })
    };
    let stage: u8 = fs::read_to_string(directory.join("stage"))
        .map_err(|e| e.to_string())?
        .trim()
        .parse()
        .map_err(|_| "fixture stage invalid")?;
    let body = match stage {
        0 if has_tool("mcp__mini_grain__mini_create_application") => event_stream(
            model,
            Some((
                "mcp__mini_grain__mini_create_application",
                "call-mini-app",
                json!({"family":"office"}),
            )),
            "",
        ),
        1 if has_result("call-mini-app") => event_stream(
            model,
            None,
            "Application birth tool returned; stop this prompt.",
        ),
        2 if has_tool("mcp__mini_grain__mini_create_application_session") => event_stream(
            model,
            Some((
                "mcp__mini_grain__mini_create_application_session",
                "call-mini-session",
                json!({"family":"office-web","application":"office-0-app"}),
            )),
            "",
        ),
        3 if has_result("call-mini-session") => event_stream(
            model,
            None,
            "Session birth tool returned; stop this prompt.",
        ),
        _ => {
            return refuse(
                stream,
                "409 Conflict",
                "fixture stage and tool history differ",
            )
        }
    };
    // Claim the stage before sending. A lost reply is explicit fixture
    // uncertainty; no automatic second model tool call is fabricated.
    advance(directory, stage + 1)?;
    send(stream, "200 OK", "text/event-stream", &body)
}
