//! Git smart HTTP inside the already confined Hermes MCP worker. Every
//! request crosses the ordinary Mini application API; this process has no
//! app, payer, or provider signing key and no direct app network route.
use serde_json::{json, Value};
use std::fs::{self, DirBuilder, File};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

const MAX_GIT_BODY: usize = 24 * 1024;
const MAX_GIT_REPLY: usize = 512 * 1024;
const MAX_GIT_HTTP: usize = 16;
const COMMAND_DEADLINE: Duration = Duration::from_secs(180);
static NEXT_SCRATCH: AtomicU64 = AtomicU64::new(0);

struct Input {
    application: String,
    path: String,
    content: String,
    message: String,
}

fn input(value: &Value) -> Result<Input, String> {
    let fields = value.as_object().ok_or("GitWeb edit requires an object")?;
    if fields.len() != 4
        || fields
            .keys()
            .any(|key| !matches!(key.as_str(), "application" | "path" | "content" | "message"))
    {
        return Err("GitWeb edit has noncanonical fields".into());
    }
    let get = |name: &str| -> Result<String, String> {
        fields
            .get(name)
            .and_then(Value::as_str)
            .map(str::to_owned)
            .ok_or_else(|| format!("GitWeb edit {name} must be a string"))
    };
    let application = get("application")?;
    let path = get("path")?;
    let content = get("content")?;
    let message = get("message")?;
    if application.is_empty()
        || application.len() > 64
        || !application.ends_with("-app")
        || !application
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
        || path.is_empty()
        || path.len() > 256
        || path.starts_with('/')
        || path.split('/').any(|part| {
            part.is_empty()
                || part == "."
                || part == ".."
                || part == ".git"
                || part.starts_with('-')
                || !part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || b"._-".contains(&byte))
        })
        || content.len() > 8192
        || content.bytes().any(|byte| byte == 0)
        || message.is_empty()
        || message.len() > 256
        || message.chars().any(char::is_control)
    {
        return Err("GitWeb edit exceeds the fixed path/content/message profile".into());
    }
    Ok(Input {
        application,
        path,
        content,
        message,
    })
}

fn unhex(encoded: &str, max: usize) -> Result<Vec<u8>, String> {
    if encoded.len() > max * 2 || !encoded.len().is_multiple_of(2) {
        return Err("GitWeb HTTP body exceeds exact hex bound".into());
    }
    let mut out = Vec::with_capacity(encoded.len() / 2);
    for pair in encoded.as_bytes().chunks_exact(2) {
        let digit = |byte| match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            _ => None,
        };
        out.push(
            (digit(pair[0]).ok_or("GitWeb HTTP body is not canonical hex")? << 4)
                | digit(pair[1]).ok_or("GitWeb HTTP body is not canonical hex")?,
        );
    }
    Ok(out)
}

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

struct HttpRequest {
    method: &'static str,
    path: String,
    query: String,
    headers: Vec<Value>,
    body: Vec<u8>,
}

fn proxy_token() -> Result<String, String> {
    let mut bytes = [0u8; 32];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|_| "Git proxy entropy unavailable")?;
    Ok(hex(&bytes))
}

fn read_http(stream: &mut TcpStream, token: &str) -> Result<HttpRequest, String> {
    let deadline = Instant::now() + Duration::from_secs(10);
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;
    let mut raw = Vec::new();
    let mut chunk = [0u8; 4096];
    let boundary = loop {
        if raw.len() > 16 * 1024 {
            return Err("Git HTTP headers exceed bound".into());
        }
        if let Some(index) = raw.windows(4).position(|part| part == b"\r\n\r\n") {
            break index + 4;
        }
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err("Git HTTP request deadline exceeded".into());
        }
        stream
            .set_read_timeout(Some(remaining))
            .map_err(|e| e.to_string())?;
        let count = stream.read(&mut chunk).map_err(|e| e.to_string())?;
        if count == 0 {
            return Err("Git HTTP header ended early".into());
        }
        raw.extend_from_slice(&chunk[..count]);
    };
    let head = std::str::from_utf8(&raw[..boundary]).map_err(|_| "Git HTTP header is not UTF-8")?;
    let mut lines = head.trim_end_matches("\r\n\r\n").split("\r\n");
    let request = lines.next().ok_or("Git HTTP request line absent")?;
    let (method, target) = match request.split(' ').collect::<Vec<_>>().as_slice() {
        ["GET", target, "HTTP/1.1"] => ("GET", *target),
        ["POST", target, "HTTP/1.1"] => ("POST", *target),
        _ => return Err("Git HTTP method or version unavailable".into()),
    };
    let target = target
        .strip_prefix("/repo.git/")
        .ok_or("Git HTTP escaped fixed repo prefix")?;
    let (path, query) = target.split_once('?').unwrap_or((target, ""));
    if !matches!(
        (method, path, query),
        (
            "GET",
            "info/refs",
            "service=git-upload-pack" | "service=git-receive-pack"
        ) | ("POST", "git-upload-pack" | "git-receive-pack", "")
    ) {
        return Err("Git requested a route outside the fixed smart-HTTP profile".into());
    }
    let mut content_length = None;
    let mut authorized = false;
    let mut headers = Vec::new();
    for line in lines {
        let (name, value) = line.split_once(':').ok_or("malformed Git HTTP header")?;
        let value = value.trim();
        if name.eq_ignore_ascii_case("X-Mini-Git-Proxy-Token") {
            if authorized || value != token {
                return Err("Git proxy caller is not authenticated".into());
            }
            authorized = true;
        } else if name.eq_ignore_ascii_case("Content-Length") {
            if content_length
                .replace(
                    value
                        .parse::<usize>()
                        .map_err(|_| "Git HTTP length invalid")?,
                )
                .is_some()
            {
                return Err("duplicate Git HTTP Content-Length".into());
            }
        } else if name.eq_ignore_ascii_case("Transfer-Encoding") {
            return Err("Git HTTP transfer encoding unsupported".into());
        } else if matches!(
            name.to_ascii_lowercase().as_str(),
            "accept" | "content-type" | "user-agent"
        ) {
            if !value.is_ascii()
                || value.bytes().any(|b| b < 0x20 || b == 0x7f)
                || value.len() > 8192
            {
                return Err("Git HTTP ordinary header invalid".into());
            }
            headers.push(json!({"name":name.to_ascii_lowercase(),"value":value}));
        }
    }
    if !authorized {
        return Err("Git proxy caller is not authenticated".into());
    }
    let length = content_length.unwrap_or(0);
    if length > MAX_GIT_BODY
        || (method == "POST" && content_length.is_none())
        || (method == "GET" && length != 0)
        || raw.len() - boundary > length
    {
        return Err("Git HTTP body exceeds Mini's 24 KiB request profile".into());
    }
    let path = path.to_owned();
    let query = query.to_owned();
    while raw.len() - boundary < length {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err("Git HTTP request deadline exceeded".into());
        }
        stream
            .set_read_timeout(Some(remaining))
            .map_err(|e| e.to_string())?;
        let count = stream.read(&mut chunk).map_err(|e| e.to_string())?;
        if count == 0 {
            return Err("Git HTTP body ended early".into());
        }
        raw.extend_from_slice(&chunk[..count]);
        if raw.len() - boundary > length {
            return Err("Git HTTP body exceeds declared length".into());
        }
    }
    Ok(HttpRequest {
        method,
        path,
        query,
        headers,
        body: raw[boundary..].to_vec(),
    })
}

fn write_http(stream: &mut TcpStream, reply: &Value) -> Result<(), String> {
    if reply.get("type").and_then(Value::as_str) != Some("http-v3") {
        return Err("Git HTTP call has no definite app result".into());
    }
    let status = reply
        .get("status")
        .and_then(Value::as_u64)
        .filter(|status| (100..=599).contains(status))
        .ok_or("Git app status absent")?;
    let body = unhex(
        reply
            .get("bodyHex")
            .and_then(Value::as_str)
            .ok_or("Git app body absent")?,
        MAX_GIT_REPLY,
    )?;
    let mime = reply
        .get("headers")
        .and_then(Value::as_array)
        .and_then(|headers| {
            headers.iter().find_map(|header| {
                header
                    .get("name")
                    .and_then(Value::as_str)
                    .is_some_and(|name| name.eq_ignore_ascii_case("content-type"))
                    .then(|| header.get("value").and_then(Value::as_str))
                    .flatten()
            })
        })
        .unwrap_or("application/octet-stream");
    if !mime.is_ascii() || mime.bytes().any(|byte| byte < 0x20 || byte == 0x7f) {
        return Err("Git app Content-Type invalid".into());
    }
    write!(stream, "HTTP/1.1 {status} Result\r\nContent-Type: {mime}\r\nContent-Length: {}\r\nConnection: close\r\n\r\n", body.len())
        .and_then(|_| stream.write_all(&body))
        .and_then(|_| stream.flush()).map_err(|e| e.to_string())
}

fn git_command(repo: Option<&Path>, args: &[&str]) -> Command {
    let mut command = Command::new("/usr/bin/git");
    command
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_TERMINAL_PROMPT", "0")
        .args([
            "-c",
            "protocol.version=0",
            "-c",
            "http.maxRequests=1",
            "-c",
            "http.postBuffer=4194304",
        ]);
    if let Some(repo) = repo {
        command.arg("-C").arg(repo);
    }
    command.args(args);
    command
}

fn git_http_command(repo: Option<&Path>, args: &[&str], token: &str) -> Command {
    let mut command = git_command(repo, args);
    command
        .env("GIT_CONFIG_COUNT", "1")
        .env("GIT_CONFIG_KEY_0", "http.extraHeader")
        .env(
            "GIT_CONFIG_VALUE_0",
            format!("X-Mini-Git-Proxy-Token: {token}"),
        );
    command
}

fn run_plain(repo: &Path, args: &[&str]) -> Result<String, String> {
    let output = git_command(Some(repo), args)
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() {
        return Err(format!(
            "Git local operation failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    String::from_utf8(output.stdout)
        .map(|text| text.trim().to_owned())
        .map_err(|_| "Git local output is not UTF-8".into())
}

struct ProxyPolicy<'a> {
    token: &'a str,
    allow_mutation: bool,
}

fn serve_git<F>(
    listener: &TcpListener,
    child: &mut Child,
    application: &str,
    receive_post_seen: &mut bool,
    receipts: &mut Vec<Value>,
    forward: &mut F,
    policy: ProxyPolicy<'_>,
) -> Result<(), String>
where
    F: FnMut(Value) -> Result<Value, String>,
{
    let result = (|| {
        listener.set_nonblocking(true).map_err(|e| e.to_string())?;
        let started = Instant::now();
        loop {
            if started.elapsed() >= COMMAND_DEADLINE {
                return Err(
                    "Git command exceeded bounded worker deadline; any POST is uncertain".into(),
                );
            }
            match listener.accept() {
                Ok((mut stream, _)) => {
                    if receipts.len() >= MAX_GIT_HTTP {
                        return Err("Git issued too many HTTP requests".into());
                    }
                    let request = read_http(&mut stream, policy.token)?;
                    if !policy.allow_mutation
                        && request.method == "POST"
                        && request.path == "git-receive-pack"
                    {
                        return Err("Git read cannot forward a mutating HTTP request".into());
                    }
                    if request.method == "POST" && request.path == "git-receive-pack" {
                        if *receive_post_seen {
                            return Err("Git receive-pack POST would be repeated".into());
                        }
                        *receive_post_seen = true;
                    }
                    let call = json!({"application":application,"method":request.method,
                    "path":request.path,"query":request.query,"headers":request.headers,
                    "bodyHex":hex(&request.body)});
                    let reply = forward(call)?;
                    if reply.get("type").and_then(Value::as_str) != Some("http-v3") {
                        return Err(
                            "Git app request is uncertain or refused; do not retry the push".into(),
                        );
                    }
                    receipts.push(json!({"method":request.method,"path":request.path,
                    "status":reply.get("status"),"committedReceipt":reply.get("committedReceipt"),
                    "responseSha256":reply.get("responseSha256")}));
                    write_http(&mut stream, &reply)?;
                }
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {
                    if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
                        if status.success() {
                            return Ok(());
                        }
                        return Err(format!(
                            "Git smart HTTP exited {status}; no mutating retry is allowed"
                        ));
                    }
                    std::thread::sleep(Duration::from_millis(20));
                }
                Err(error) => return Err(format!("Git loopback accept: {error}")),
            }
        }
    })();
    if result.is_err() {
        let _ = child.kill();
        let _ = child.wait();
    }
    result
}

struct Scratch(PathBuf);
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub(crate) fn read<F>(arguments: &Value, mut forward: F) -> Result<Value, String>
where
    F: FnMut(Value) -> Result<Value, String>,
{
    let fields = arguments
        .as_object()
        .ok_or("GitWeb read requires an object")?;
    if fields.len() != 2 || !fields.contains_key("application") || !fields.contains_key("path") {
        return Err("GitWeb read has noncanonical fields".into());
    }
    let application = fields
        .get("application")
        .and_then(Value::as_str)
        .ok_or("GitWeb application absent")?;
    let path = fields
        .get("path")
        .and_then(Value::as_str)
        .ok_or("GitWeb read path absent")?;
    let validated = input(&json!({"application":application,"path":path,
        "content":"","message":"read"}))?;
    let scratch = Scratch(std::env::temp_dir().join(format!(
        "mini-gitweb-read-{}-{}",
        std::process::id(),
        NEXT_SCRATCH.fetch_add(1, Ordering::SeqCst)
    )));
    DirBuilder::new()
        .mode(0o700)
        .create(&scratch.0)
        .map_err(|e| e.to_string())?;
    let listener = TcpListener::bind(("127.0.0.1", 0))
        .map_err(|e| format!("confined Git loopback unavailable: {e}"))?;
    let url = format!(
        "http://127.0.0.1:{}/repo.git",
        listener.local_addr().map_err(|e| e.to_string())?.port()
    );
    let repo = scratch.0.join("repo");
    let token = proxy_token()?;
    let mut receipts = Vec::new();
    let mut receive_post_seen = false;
    let mut clone = git_http_command(
        None,
        &[
            "clone",
            "-q",
            &url,
            repo.to_str().ok_or("Git scratch path UTF-8")?,
        ],
        &token,
    )
    .stdout(Stdio::null())
    .stderr(Stdio::null())
    .spawn()
    .map_err(|e| e.to_string())?;
    serve_git(
        &listener,
        &mut clone,
        &validated.application,
        &mut receive_post_seen,
        &mut receipts,
        &mut forward,
        ProxyPolicy {
            token: &token,
            allow_mutation: false,
        },
    )?;
    if run_plain(&repo, &["symbolic-ref", "--short", "HEAD"])? != "master" {
        return Err("GitWeb repository default branch is not master".into());
    }
    if receive_post_seen {
        return Err("Git read unexpectedly sent a mutating request".into());
    }
    let mut file = repo.clone();
    for part in validated.path.split('/') {
        file.push(part);
        let meta = fs::symlink_metadata(&file).map_err(|e| e.to_string())?;
        if meta.file_type().is_symlink() {
            return Err("Git read path crosses a symlink".into());
        }
    }
    let meta = fs::metadata(&file).map_err(|e| e.to_string())?;
    if !meta.is_file() || meta.len() > 32 * 1024 {
        return Err("Git read target is not a bounded ordinary file".into());
    }
    let content = fs::read_to_string(&file).map_err(|_| "Git read file is not UTF-8")?;
    Ok(
        json!({"type":"mini-gitweb-read-v1","application":validated.application,
        "path":validated.path,"content":content,"httpReceipts":receipts}),
    )
}

pub(crate) fn edit<F>(arguments: &Value, mut forward: F) -> Result<Value, String>
where
    F: FnMut(Value) -> Result<Value, String>,
{
    let input = input(arguments)?;
    let scratch = Scratch(std::env::temp_dir().join(format!(
        "mini-gitweb-edit-{}-{}",
        std::process::id(),
        NEXT_SCRATCH.fetch_add(1, Ordering::SeqCst)
    )));
    DirBuilder::new()
        .mode(0o700)
        .create(&scratch.0)
        .map_err(|e| e.to_string())?;
    let listener = TcpListener::bind(("127.0.0.1", 0))
        .map_err(|e| format!("confined Git loopback unavailable: {e}"))?;
    let url = format!(
        "http://127.0.0.1:{}/repo.git",
        listener.local_addr().map_err(|e| e.to_string())?.port()
    );
    let repo = scratch.0.join("repo");
    let token = proxy_token()?;
    let mut receipts = Vec::new();
    let mut receive_post_seen = false;
    let mut clone = git_http_command(
        None,
        &[
            "clone",
            "-q",
            &url,
            repo.to_str().ok_or("Git scratch path UTF-8")?,
        ],
        &token,
    )
    .stdout(Stdio::null())
    .stderr(Stdio::null())
    .spawn()
    .map_err(|e| e.to_string())?;
    serve_git(
        &listener,
        &mut clone,
        &input.application,
        &mut receive_post_seen,
        &mut receipts,
        &mut forward,
        ProxyPolicy {
            token: &token,
            allow_mutation: false,
        },
    )?;
    if run_plain(&repo, &["symbolic-ref", "--short", "HEAD"])? != "master" {
        return Err("GitWeb repository default branch is not master".into());
    }
    let mut file = repo.clone();
    let parts = input.path.split('/').collect::<Vec<_>>();
    for (index, part) in parts.iter().enumerate() {
        file.push(part);
        if index + 1 == parts.len() {
            if let Ok(meta) = fs::symlink_metadata(&file) {
                if !meta.is_file() || meta.file_type().is_symlink() {
                    return Err("Git edit target is not an ordinary file".into());
                }
            }
        } else {
            match fs::symlink_metadata(&file) {
                Ok(meta) if meta.is_dir() && !meta.file_type().is_symlink() => {}
                Ok(_) => return Err("Git edit path crosses a non-directory or symlink".into()),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    fs::create_dir(&file).map_err(|e| e.to_string())?;
                }
                Err(error) => return Err(error.to_string()),
            }
        }
    }
    fs::write(&file, input.content.as_bytes()).map_err(|e| e.to_string())?;
    run_plain(&repo, &["add", "--", &input.path])?;
    run_plain(
        &repo,
        &[
            "-c",
            "user.name=Mini Agent",
            "-c",
            "user.email=mini-agent@example.invalid",
            "commit",
            "-qm",
            &input.message,
        ],
    )?;
    let commit = run_plain(&repo, &["rev-parse", "HEAD"])?;
    if commit.len() != 40
        || !commit
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("Git commit identity is invalid".into());
    }
    let mut push = git_http_command(
        Some(&repo),
        &["push", "--porcelain", "origin", "HEAD:refs/heads/master"],
        &token,
    )
    .stdout(Stdio::null())
    .stderr(Stdio::null())
    .spawn()
    .map_err(|e| e.to_string())?;
    serve_git(
        &listener,
        &mut push,
        &input.application,
        &mut receive_post_seen,
        &mut receipts,
        &mut forward,
        ProxyPolicy {
            token: &token,
            allow_mutation: true,
        },
    )?;
    if !receive_post_seen {
        return Err("Git push emitted no receive-pack POST".into());
    }
    let observed_path = scratch.0.join("observed-ref");
    let observed_file = File::create(&observed_path).map_err(|e| e.to_string())?;
    let mut verify = git_http_command(
        Some(&repo),
        &["ls-remote", "origin", "refs/heads/master"],
        &token,
    )
    .stdout(Stdio::from(observed_file))
    .stderr(Stdio::null())
    .spawn()
    .map_err(|e| e.to_string())?;
    serve_git(
        &listener,
        &mut verify,
        &input.application,
        &mut receive_post_seen,
        &mut receipts,
        &mut forward,
        ProxyPolicy {
            token: &token,
            allow_mutation: false,
        },
    )?;
    let observed = fs::read(&observed_path).map_err(|e| e.to_string())?;
    if observed.len() > 128 || observed != format!("{commit}\trefs/heads/master\n").as_bytes() {
        return Err("Git remote ref did not match the committed push".into());
    }
    Ok(
        json!({"type":"mini-gitweb-edit-v1","application":input.application,
        "path":input.path,"commit":commit,"receivePostCount":1,
        "httpReceipts":receipts}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    fn git_ok(args: &[&str]) {
        let output = Command::new("/usr/bin/git").args(args).output().unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    fn cgi_forward(root: &Path, request: Value) -> Result<Value, String> {
        let method = request["method"].as_str().ok_or("method")?;
        let path = request["path"].as_str().ok_or("path")?;
        let query = request["query"].as_str().ok_or("query")?;
        let body = unhex(request["bodyHex"].as_str().ok_or("bodyHex")?, MAX_GIT_BODY)?;
        let content_type = request["headers"]
            .as_array()
            .ok_or("headers")?
            .iter()
            .find(|header| header["name"] == "content-type")
            .and_then(|header| header["value"].as_str())
            .unwrap_or("");
        let mut child = Command::new("/usr/bin/git")
            .arg("http-backend")
            .env("GIT_PROJECT_ROOT", root)
            .env("GIT_HTTP_EXPORT_ALL", "1")
            .env("REQUEST_METHOD", method)
            .env("PATH_INFO", format!("/repo.git/{path}"))
            .env("QUERY_STRING", query)
            .env("CONTENT_TYPE", content_type)
            .env("CONTENT_LENGTH", body.len().to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| e.to_string())?;
        child
            .stdin
            .take()
            .ok_or("CGI stdin")?
            .write_all(&body)
            .map_err(|e| e.to_string())?;
        let output = child.wait_with_output().map_err(|e| e.to_string())?;
        if !output.status.success() {
            return Err(format!(
                "Git CGI failed: {}",
                String::from_utf8_lossy(&output.stderr)
            ));
        }
        let boundary = output
            .stdout
            .windows(4)
            .position(|part| part == b"\r\n\r\n")
            .ok_or("Git CGI header boundary")?;
        let head =
            std::str::from_utf8(&output.stdout[..boundary]).map_err(|_| "Git CGI header UTF-8")?;
        let mut status = 200;
        let mut mime = "application/octet-stream";
        for line in head.split("\r\n") {
            if let Some(value) = line.strip_prefix("Status: ") {
                status = value
                    .split(' ')
                    .next()
                    .ok_or("CGI status")?
                    .parse::<u16>()
                    .map_err(|_| "CGI status")?;
            }
            if let Some(value) = line.strip_prefix("Content-Type: ") {
                mime = value;
            }
        }
        Ok(json!({"type":"http-v3","status":status,
            "headers":[{"name":"content-type","value":mime}],
            "bodyHex":hex(&output.stdout[boundary+4..]),
            "committedReceipt":{"transactionId":"1","eventId":"2",
                "acceptedCount":"3","worldRoot":"4"}}))
    }

    #[test]
    fn actual_git_http_backend_empty_birth_then_read_and_existing_edit() {
        let root = Scratch(std::env::temp_dir().join(format!(
            "mini-git-cgi-{}-{}",
            std::process::id(),
            NEXT_SCRATCH.fetch_add(1, Ordering::SeqCst)
        )));
        fs::create_dir(&root.0).unwrap();
        let bare = root.0.join("repo.git");
        git_ok(&[
            "init",
            "-q",
            "--bare",
            "-b",
            "master",
            bare.to_str().unwrap(),
        ]);
        git_ok(&[
            "-C",
            bare.to_str().unwrap(),
            "config",
            "http.receivepack",
            "true",
        ]);
        let first = edit(
            &json!({"application":"gitweb-app","path":"notes/readme.txt",
            "content":"first\n","message":"First note"}),
            |request| cgi_forward(&root.0, request),
        )
        .unwrap();
        assert_eq!(first["receivePostCount"], 1);
        let readback = read(
            &json!({"application":"gitweb-app","path":"notes/readme.txt"}),
            |request| cgi_forward(&root.0, request),
        )
        .unwrap();
        assert_eq!(readback["content"], "first\n");
        let second = edit(
            &json!({"application":"gitweb-app","path":"notes/readme.txt",
            "content":"second\n","message":"Second note"}),
            |request| cgi_forward(&root.0, request),
        )
        .unwrap();
        assert_eq!(second["receivePostCount"], 1);
        assert_ne!(first["commit"], second["commit"]);
    }
    #[test]
    fn rejects_path_escape_and_oversize_pack_without_forwarding() {
        let good = json!({"application":"gitweb-app","path":"notes/readme.txt",
            "content":"hello","message":"Edit note"});
        assert!(input(&good).is_ok());
        let mut escaped = good.clone();
        escaped["path"] = json!("../secret");
        assert!(input(&escaped).is_err());
        let mut hidden = good.clone();
        hidden["path"] = json!(".git/config");
        assert!(input(&hidden).is_err());
        let mut oversized = good;
        oversized["content"] = json!("x".repeat(8193));
        assert!(input(&oversized).is_err());
        assert!(unhex(&"aa".repeat(MAX_GIT_BODY + 1), MAX_GIT_BODY).is_err());
        let configured = git_http_command(None, &["config", "--get", "http.extraHeader"], "fixed")
            .output()
            .unwrap();
        assert!(configured.status.success());
        assert_eq!(configured.stdout, b"X-Mini-Git-Proxy-Token: fixed\n");
    }

    #[test]
    fn uncertain_receive_pack_is_forwarded_once_and_stops_git_child() {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let sender = thread::spawn(move || {
            let mut stream = TcpStream::connect(address).unwrap();
            stream.write_all(b"POST /repo.git/git-receive-pack HTTP/1.1\r\nHost: localhost\r\nX-Mini-Git-Proxy-Token: accepted\r\nContent-Length: 3\r\nContent-Type: application/x-git-receive-pack-request\r\n\r\nabc").unwrap();
        });
        let mut child = Command::new("/bin/sleep").arg("30").spawn().unwrap();
        let mut seen = false;
        let mut receipts = Vec::new();
        let mut forwarded = 0;
        let result = serve_git(
            &listener,
            &mut child,
            "gitweb-app",
            &mut seen,
            &mut receipts,
            &mut |call| {
                assert!(!call["headers"].to_string().contains("accepted"));
                forwarded += 1;
                Err("uncertain native dispatch".into())
            },
            ProxyPolicy {
                token: "accepted",
                allow_mutation: true,
            },
        );
        sender.join().unwrap();
        assert!(result.is_err());
        assert!(seen);
        assert_eq!(forwarded, 1);
        assert!(receipts.is_empty());
        assert!(child.try_wait().unwrap().is_some());
    }

    #[test]
    fn unauthenticated_peer_and_read_mode_post_never_reach_mini() {
        for (header, allow_mutation) in
            [("", true), ("X-Mini-Git-Proxy-Token: accepted\r\n", false)]
        {
            let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
            let address = listener.local_addr().unwrap();
            let request = format!("POST /repo.git/git-receive-pack HTTP/1.1\r\nHost: localhost\r\n{header}Content-Length: 3\r\n\r\nabc");
            let sender = thread::spawn(move || {
                TcpStream::connect(address)
                    .unwrap()
                    .write_all(request.as_bytes())
                    .unwrap();
            });
            let mut child = Command::new("/bin/sleep").arg("30").spawn().unwrap();
            let mut seen = false;
            let mut receipts = Vec::new();
            let mut forwarded = 0;
            let result = serve_git(
                &listener,
                &mut child,
                "gitweb-app",
                &mut seen,
                &mut receipts,
                &mut |_| {
                    forwarded += 1;
                    Ok(json!({"type":"http-v3"}))
                },
                ProxyPolicy {
                    token: "accepted",
                    allow_mutation,
                },
            );
            sender.join().unwrap();
            assert!(result.is_err());
            assert_eq!(forwarded, 0);
            assert!(!seen);
            assert!(child.try_wait().unwrap().is_some());
        }
    }
}
