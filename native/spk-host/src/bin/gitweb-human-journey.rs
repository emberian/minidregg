//! Operator-private Git smart-HTTP transport for one human GitWeb journey.
//! The resident Mini/SPK path remains the authority for every forwarded call.

use serde_json::json;
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Component, Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::time::{Duration, Instant};

const MAX_REQUEST: usize = 24 * 1024;
const MAX_REPLY: usize = 512 * 1024;
const MAX_FILE: usize = 8192;
const MAX_HTTP_CALLS: usize = 16;
// Match the grain-runtime MCP proxy's 1800-second worker wall plus delivery grace.
const CALL_WALL: Duration = Duration::from_secs(1810);

type Result<T> = std::result::Result<T, String>;
type HttpResponse<'a> = (u16, Vec<(String, String)>, &'a [u8]);

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8] = b"0123456789abcdef";
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize] as char);
        out.push(DIGITS[(byte & 15) as usize] as char);
    }
    out
}

fn sha(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn protected_ancestors(path: &Path) -> Result<()> {
    if !path.is_absolute()
        || path
            .components()
            .any(|part| matches!(part, Component::CurDir | Component::ParentDir))
    {
        return Err("noncanonical private path".into());
    }
    for ancestor in path.ancestors() {
        let meta = fs::symlink_metadata(ancestor).map_err(|e| e.to_string())?;
        if !meta.is_dir()
            || meta.file_type().is_symlink()
            || (meta.uid() != 0 && meta.uid() != unsafe { libc::geteuid() })
            || meta.mode() & 0o022 != 0
        {
            return Err("private path ancestor refused".into());
        }
    }
    Ok(())
}

fn private_file(path: &Path, max: usize) -> Result<Vec<u8>> {
    protected_ancestors(path.parent().ok_or("private input parent absent")?)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|e| e.to_string())?;
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.is_file()
        || meta.file_type().is_symlink()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o777 != 0o600
        || meta.nlink() != 1
        || meta.len() as usize > max
    {
        return Err("private input custody refused".into());
    }
    let mut bytes = Vec::new();
    Read::take(&mut file, (max + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > max {
        return Err("private input size refused".into());
    }
    Ok(bytes)
}

fn private_parent(path: &Path) -> Result<()> {
    let parent = path.parent().ok_or("private output parent absent")?;
    protected_ancestors(parent)?;
    let meta = fs::symlink_metadata(parent).map_err(|e| e.to_string())?;
    if !meta.is_dir()
        || meta.file_type().is_symlink()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
    {
        return Err("private output parent refused".into());
    }
    Ok(())
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|e| e.to_string())?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| e.to_string())
}

fn sync_dir(path: &Path) -> Result<()> {
    File::open(path)
        .and_then(|file| file.sync_all())
        .map_err(|e| e.to_string())
}

fn ordinary_path(path: &str) -> bool {
    !path.is_empty()
        && path.len() <= 256
        && !path.starts_with('/')
        && path.split('/').all(|part| {
            !part.is_empty()
                && part != "."
                && part != ".."
                && part != ".git"
                && !part.starts_with('-')
                && part
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || b"._-".contains(&byte))
        })
}

fn host_name(host: &str) -> bool {
    if host.is_empty() || host.len() > 255 || host != host.to_ascii_lowercase() {
        return false;
    }
    let (name, port) = match host.split_once(':') {
        Some((name, port)) => (name, Some(port)),
        None => (host, None),
    };
    if port.is_some_and(|port| {
        port.is_empty()
            || port.starts_with('0')
            || !port.bytes().all(|byte| byte.is_ascii_digit())
            || port.parse::<u16>().is_err()
    }) {
        return false;
    }
    name.split('.').all(|label| {
        !label.is_empty()
            && label.len() <= 63
            && label
                .bytes()
                .next()
                .is_some_and(|byte| byte.is_ascii_alphanumeric())
            && label
                .bytes()
                .last()
                .is_some_and(|byte| byte.is_ascii_alphanumeric())
            && label
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    })
}

fn exact_token(path: &Path) -> Result<String> {
    let bytes = private_file(path, 128)?;
    let token = std::str::from_utf8(&bytes)
        .map_err(|_| "token is not UTF-8")?
        .trim();
    if token.len() != 64 || !token.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("native token is not 64 hex digits".into());
    }
    Ok(token.to_owned())
}

fn socket_file(path: &Path) -> Result<()> {
    protected_ancestors(path.parent().ok_or("native entrance parent absent")?)?;
    if path.file_name().and_then(|name| name.to_str()) != Some("http.sock") {
        return Err("native entrance socket name refused".into());
    }
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.file_type().is_socket()
        || meta.file_type().is_symlink()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o777 != 0o600
        || meta.nlink() != 1
    {
        return Err("native entrance socket absent".into());
    }
    Ok(())
}

fn find_header(raw: &[u8]) -> Option<usize> {
    raw.windows(4)
        .position(|part| part == b"\r\n\r\n")
        .map(|offset| offset + 4)
}

fn parse_http_response(raw: &[u8]) -> Result<HttpResponse<'_>> {
    let boundary = find_header(raw).ok_or("native HTTP response header absent")?;
    let header =
        std::str::from_utf8(&raw[..boundary]).map_err(|_| "native HTTP header not UTF-8")?;
    let mut lines = header.trim_end_matches("\r\n\r\n").split("\r\n");
    let first = lines.next().ok_or("native HTTP status absent")?;
    let mut words = first.split(' ');
    if !words
        .next()
        .is_some_and(|version| version == "HTTP/1.1" || version == "HTTP/1.0")
    {
        return Err("native HTTP version refused".into());
    }
    let status: u16 = words
        .next()
        .ok_or("native HTTP code absent")?
        .parse()
        .map_err(|_| "native HTTP code invalid")?;
    if !(100..=599).contains(&status) {
        return Err("native HTTP code outside range".into());
    }
    let mut selected = Vec::new();
    let mut length = None;
    for line in lines {
        let (name, value) = line.split_once(':').ok_or("native HTTP header malformed")?;
        let value = value.trim();
        if name.eq_ignore_ascii_case("transfer-encoding") {
            return Err("chunked native HTTP reply refused".into());
        }
        if name.eq_ignore_ascii_case("content-length")
            && length
                .replace(
                    value
                        .parse::<usize>()
                        .map_err(|_| "native HTTP length invalid")?,
                )
                .is_some()
        {
            return Err("duplicate native HTTP length".into());
        }
        if ["content-type", "cache-control", "pragma", "expires"]
            .iter()
            .any(|allowed| name.eq_ignore_ascii_case(allowed))
        {
            selected.push((name.to_owned(), value.to_owned()));
        }
    }
    let payload = &raw[boundary..];
    if length.is_some_and(|expected| expected != payload.len()) {
        return Err("native HTTP body length differs".into());
    }
    Ok((status, selected, payload))
}

fn unix_http(socket: &Path, request: &[u8], deadline: Instant) -> Result<Vec<u8>> {
    let mut stream = UnixStream::connect(socket).map_err(|e| e.to_string())?;
    let remaining = deadline.saturating_duration_since(Instant::now());
    if remaining.is_zero() {
        return Err("native HTTP absolute deadline expired".into());
    }
    stream
        .set_write_timeout(Some(remaining))
        .map_err(|e| e.to_string())?;
    stream.write_all(request).map_err(|e| e.to_string())?;
    let mut response = Vec::new();
    loop {
        let remaining = deadline.saturating_duration_since(Instant::now());
        if remaining.is_zero() {
            return Err("native HTTP absolute deadline expired".into());
        }
        stream
            .set_read_timeout(Some(remaining))
            .map_err(|e| e.to_string())?;
        let mut chunk = [0; 8192];
        let count = stream.read(&mut chunk).map_err(|e| e.to_string())?;
        if count == 0 {
            break;
        }
        if response.len() + count > MAX_REPLY {
            return Err("native HTTP response exceeds bound".into());
        }
        response.extend_from_slice(&chunk[..count]);
    }
    Ok(response)
}

struct Bridge {
    socket: PathBuf,
    host: String,
    bearer: String,
    proxy_token: String,
    directory: PathBuf,
    calls: usize,
    read_only: bool,
}

impl Bridge {
    fn handle(&mut self, mut stream: TcpStream, deadline: Instant) -> Result<()> {
        stream
            .set_read_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| e.to_string())?;
        stream
            .set_write_timeout(Some(Duration::from_secs(10)))
            .map_err(|e| e.to_string())?;
        let mut raw = Vec::new();
        let boundary = loop {
            if Instant::now() >= deadline {
                return Err("Git HTTP absolute deadline expired".into());
            }
            if let Some(boundary) = find_header(&raw) {
                break boundary;
            }
            if raw.len() >= 16 * 1024 {
                return Err("Git HTTP request header exceeds bound".into());
            }
            let mut chunk = [0; 4096];
            let count = stream.read(&mut chunk).map_err(|e| e.to_string())?;
            if count == 0 {
                return Err("Git HTTP request ended early".into());
            }
            raw.extend_from_slice(&chunk[..count]);
        };
        let header =
            std::str::from_utf8(&raw[..boundary]).map_err(|_| "Git HTTP header not UTF-8")?;
        let mut lines = header.trim_end_matches("\r\n\r\n").split("\r\n");
        let first = lines.next().ok_or("Git HTTP request line absent")?;
        let words: Vec<_> = first.split(' ').collect();
        if words.len() != 3 || words[2] != "HTTP/1.1" {
            return Err("Git HTTP request line refused".into());
        }
        let method = words[0].to_owned();
        let target = words[1].to_owned();
        let allowed = matches!(
            (method.as_str(), target.as_str()),
            ("GET", "/repo.git/info/refs?service=git-upload-pack")
                | ("GET", "/repo.git/info/refs?service=git-receive-pack")
                | ("POST", "/repo.git/git-upload-pack")
                | ("POST", "/repo.git/git-receive-pack")
        );
        if !allowed {
            return Err("Git requested a route outside fixed smart HTTP".into());
        }
        let mut length = None;
        let mut authorized = false;
        let mut forwarded = Vec::new();
        for line in lines {
            let (name, value) = line.split_once(':').ok_or("Git HTTP header malformed")?;
            let value = value.trim();
            if name.eq_ignore_ascii_case("x-mini-git-proxy-token") {
                if authorized || value != self.proxy_token {
                    return Err("local Git proxy token refused".into());
                }
                authorized = true;
            } else if name.eq_ignore_ascii_case("content-length") {
                if length
                    .replace(
                        value
                            .parse::<usize>()
                            .map_err(|_| "Git HTTP length invalid")?,
                    )
                    .is_some()
                {
                    return Err("duplicate Git HTTP length".into());
                }
            } else if name.eq_ignore_ascii_case("transfer-encoding")
                || name.eq_ignore_ascii_case("authorization")
                || name.eq_ignore_ascii_case("cookie")
                || name.eq_ignore_ascii_case("expect")
            {
                return Err("Git HTTP header outside fixed proxy profile".into());
            } else if ["accept", "content-type", "user-agent"]
                .iter()
                .any(|allowed| name.eq_ignore_ascii_case(allowed))
                && value.is_ascii()
                && !value.contains(['\r', '\n'])
            {
                forwarded.push(format!("{name}: {value}"));
            }
        }
        if !authorized {
            return Err("local Git proxy token absent".into());
        }
        let length = length.unwrap_or(0);
        if length > MAX_REQUEST || (method == "POST" && length == 0) {
            return Err("Git HTTP body outside fixed bound".into());
        }
        while raw.len() - boundary < length {
            if Instant::now() >= deadline {
                return Err("Git HTTP absolute deadline expired".into());
            }
            let mut chunk = [0; 4096];
            let count = stream.read(&mut chunk).map_err(|e| e.to_string())?;
            if count == 0 {
                return Err("Git HTTP body ended early".into());
            }
            raw.extend_from_slice(&chunk[..count]);
            if raw.len() - boundary > length {
                return Err("Git HTTP body length differs".into());
            }
        }
        if raw.len() - boundary != length {
            return Err("Git HTTP body length differs".into());
        }
        self.calls += 1;
        if self.calls > MAX_HTTP_CALLS {
            return Err("Git HTTP call count exceeded".into());
        }
        if method == "POST" && target == "/repo.git/git-receive-pack" {
            if self.read_only {
                return Err("recovery refuses Git receive-pack".into());
            }
            write_new(
                &self.directory.join("receive-pack-forwarded.marker"),
                b"one receive-pack forwarded; reconcile before any retry\n",
            )?;
            sync_dir(&self.directory)?;
        }
        let mut native = format!("{method} {target} HTTP/1.1\r\nHost: {}\r\nAuthorization: Bearer {}\r\nContent-Length: {length}\r\nConnection: close\r\n",
            self.host, self.bearer).into_bytes();
        for header in forwarded {
            native.extend_from_slice(header.as_bytes());
            native.extend_from_slice(b"\r\n");
        }
        native.extend_from_slice(b"\r\n");
        native.extend_from_slice(&raw[boundary..]);
        let response = unix_http(&self.socket, &native, deadline)?;
        let (status, headers, payload) = parse_http_response(&response)?;
        let mut head = format!(
            "HTTP/1.1 {status} Result\r\nContent-Length: {}\r\nConnection: close\r\n",
            payload.len()
        );
        for (name, value) in headers {
            head.push_str(&format!("{name}: {value}\r\n"));
        }
        head.push_str("\r\n");
        stream
            .write_all(head.as_bytes())
            .and_then(|_| stream.write_all(payload))
            .map_err(|e| e.to_string())
    }
}

fn git_command(
    args: &[&str],
    cwd: &Path,
    config: &Path,
    log: &Path,
    listener: Option<&TcpListener>,
    bridge: &mut Bridge,
) -> Result<()> {
    let output = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(log)
        .map_err(|e| e.to_string())?;
    let error = output.try_clone().map_err(|e| e.to_string())?;
    let mut child: Child = Command::new("/usr/bin/git")
        .args(args)
        .current_dir(cwd)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", config)
        .env("GIT_TERMINAL_PROMPT", "0")
        .stdout(Stdio::from(output))
        .stderr(Stdio::from(error))
        .spawn()
        .map_err(|e| e.to_string())?;
    let deadline = Instant::now() + CALL_WALL;
    loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            return if status.success() {
                Ok(())
            } else {
                Err(format!(
                    "Git command failed; inspect {} and reconcile before retry",
                    log.display()
                ))
            };
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return Err("Git command timed out; reconcile before any mutating retry".into());
        }
        if let Some(listener) = listener {
            match listener.accept() {
                Ok((stream, _)) => {
                    if let Err(error) = bridge.handle(stream, deadline) {
                        let _ = child.kill();
                        let _ = child.wait();
                        return Err(format!(
                            "Git HTTP bridge refused: {error}; reconcile before retry"
                        ));
                    }
                }
                Err(error) if error.kind() == std::io::ErrorKind::WouldBlock => {}
                Err(error) => {
                    let _ = child.kill();
                    let _ = child.wait();
                    return Err(error.to_string());
                }
            }
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn checked_git_output(args: &[&str], cwd: &Path, config: &Path) -> Result<String> {
    let output = Command::new("/usr/bin/git")
        .args(args)
        .current_dir(cwd)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .env("LANG", "C")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", config)
        .env("GIT_TERMINAL_PROMPT", "0")
        .output()
        .map_err(|e| e.to_string())?;
    if !output.status.success() || output.stdout.len() > 4096 || output.stderr.len() > 4096 {
        return Err("Git read-only output refused".into());
    }
    String::from_utf8(output.stdout)
        .map(|text| text.trim().to_owned())
        .map_err(|e| e.to_string())
}

fn remote_master(log: &Path) -> Result<Option<String>> {
    protected_ancestors(log.parent().ok_or("Git remote log parent absent")?)?;
    let meta = fs::symlink_metadata(log).map_err(|e| e.to_string())?;
    if !meta.is_file()
        || meta.file_type().is_symlink()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o777 != 0o600
        || meta.nlink() != 1
        || meta.len() > 4096
    {
        return Err("Git remote log custody refused".into());
    }
    let bytes = fs::read(log).map_err(|e| e.to_string())?;
    let text = std::str::from_utf8(&bytes).map_err(|_| "Git remote output is not UTF-8")?;
    let matches: Vec<_> = text
        .lines()
        .filter_map(|line| line.split_once('\t'))
        .filter(|(_, name)| *name == "refs/heads/master")
        .map(|(commit, _)| commit)
        .collect();
    if matches.is_empty() {
        return Ok(None);
    }
    if matches.len() != 1
        || !matches!(matches[0].len(), 40 | 64)
        || !matches[0].bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        return Err("Git remote master readback ambiguous".into());
    }
    Ok(Some(matches[0].to_owned()))
}

fn seed(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("seed-api API-UNIX-SOCKET API-TOKEN-600 EXPECTED-HOST FILE-PATH CONTENT-UTF8 COMMIT-MESSAGE NEW-DIR".into());
    }
    let socket = PathBuf::from(&args[1]);
    socket_file(&socket)?;
    let token_path = Path::new(&args[2]);
    if socket.parent() != token_path.parent()
        || token_path.file_name().and_then(|name| name.to_str()) != Some("api.token")
    {
        return Err("API token differs from native entrance directory".into());
    }
    let bearer = exact_token(token_path)?;
    let host = &args[3];
    if !host_name(host) {
        return Err("expected Host invalid".into());
    }
    let path = &args[4];
    if !ordinary_path(path) {
        return Err("Git file path invalid".into());
    }
    let content = private_file(Path::new(&args[5]), MAX_FILE)?;
    std::str::from_utf8(&content).map_err(|_| "Git file is not UTF-8")?;
    if content.contains(&0) {
        return Err("Git file contains NUL".into());
    }
    let message = &args[6];
    if message.is_empty() || message.len() > 256 || message.chars().any(char::is_control) {
        return Err("Git commit message invalid".into());
    }
    let directory = PathBuf::from(&args[7]);
    private_parent(&directory)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|e| e.to_string())?;
    let mut entropy = [0; 32];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut entropy))
        .map_err(|e| e.to_string())?;
    let proxy_token = hex(&entropy);
    let config = directory.join("gitconfig");
    write_new(&config, format!("[http]\n\textraHeader = X-Mini-Git-Proxy-Token: {proxy_token}\n\tfollowRedirects = false\n[protocol]\n\tversion = 0\n[credential]\n\thelper =\n").as_bytes())?;
    let listener = TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let port = listener.local_addr().map_err(|e| e.to_string())?.port();
    let url = format!("http://127.0.0.1:{port}/repo.git");
    let mut bridge = Bridge {
        socket,
        host: host.to_owned(),
        bearer,
        proxy_token,
        directory: directory.clone(),
        calls: 0,
        read_only: false,
    };
    let repo = directory.join("repo");
    git_command(
        &["clone", "-q", &url, repo.to_str().ok_or("repo path UTF-8")?],
        &directory,
        &config,
        &directory.join("clone.log"),
        Some(&listener),
        &mut bridge,
    )?;
    if checked_git_output(&["symbolic-ref", "--short", "HEAD"], &repo, &config)? != "master" {
        return Err("Git default branch is not master".into());
    }
    let mut target = repo.clone();
    for part in path.split('/') {
        target.push(part);
        if target.exists()
            && fs::symlink_metadata(&target)
                .map_err(|e| e.to_string())?
                .file_type()
                .is_symlink()
        {
            return Err("Git file path crosses symlink".into());
        }
    }
    fs::create_dir_all(target.parent().ok_or("Git file parent absent")?)
        .map_err(|e| e.to_string())?;
    write_new(&target, &content)?;
    git_command(
        &["add", "--", path],
        &repo,
        &config,
        &directory.join("add.log"),
        None,
        &mut bridge,
    )?;
    git_command(
        &[
            "-c",
            "user.name=Alice",
            "-c",
            "user.email=alice@mini.invalid",
            "commit",
            "-q",
            "-m",
            message,
        ],
        &repo,
        &config,
        &directory.join("commit.log"),
        None,
        &mut bridge,
    )?;
    let commit = checked_git_output(&["rev-parse", "HEAD"], &repo, &config)?;
    if !matches!(commit.len(), 40 | 64) || !commit.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("local Git commit object ID invalid".into());
    }
    let intent = json!({"type":"mini-gitweb-alice-api-push-intent-v1",
        "socket":bridge.socket.to_str().ok_or("socket path UTF-8")?,"host":host,"apiTokenSha256":sha(bridge.bearer.as_bytes()),
        "commit":commit,"path":path,"fileSha256":sha(&content)});
    write_new(
        &directory.join("push-intent.json"),
        format!("{intent}\n").as_bytes(),
    )?;
    sync_dir(&directory)?;
    git_command(
        &["push", "-q", "origin", "HEAD:refs/heads/master"],
        &repo,
        &config,
        &directory.join("push.log"),
        Some(&listener),
        &mut bridge,
    )?;
    git_command(
        &["ls-remote", "origin", "refs/heads/master"],
        &repo,
        &config,
        &directory.join("remote-ref.log"),
        Some(&listener),
        &mut bridge,
    )?;
    if remote_master(&directory.join("remote-ref.log"))?.as_deref() != Some(commit.as_str()) {
        return Err("Git remote ref differs; preserve exact attempt".into());
    }
    let marker = private_file(&directory.join("receive-pack-forwarded.marker"), 128)?;
    if marker != b"one receive-pack forwarded; reconcile before any retry\n" {
        return Err("one-send Git marker differs".into());
    }
    let result = json!({"type":"mini-gitweb-alice-api-seed-v1","commit":commit,
        "path":path,"fileSha256":sha(&content),"receivePostCount":1});
    write_new(
        &directory.join("result.json"),
        format!("{result}\n").as_bytes(),
    )?;
    println!("{result}");
    Ok(())
}

fn lookup(args: &[String]) -> Result<()> {
    if args.len() != 5 {
        return Err(
            "lookup-api API-UNIX-SOCKET API-TOKEN-600 EXPECTED-HOST RETAINED-SEED-DIR".into(),
        );
    }
    let socket = PathBuf::from(&args[1]);
    socket_file(&socket)?;
    let token_path = Path::new(&args[2]);
    if socket.parent() != token_path.parent()
        || token_path.file_name().and_then(|name| name.to_str()) != Some("api.token")
    {
        return Err("API token differs from native entrance directory".into());
    }
    let bearer = exact_token(token_path)?;
    let host = &args[3];
    if !host_name(host) {
        return Err("expected Host invalid".into());
    }
    let directory = PathBuf::from(&args[4]);
    private_parent(&directory)?;
    let meta = fs::symlink_metadata(&directory).map_err(|e| e.to_string())?;
    if !meta.is_dir()
        || meta.file_type().is_symlink()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o777 != 0o700
    {
        return Err("retained seed directory custody refused".into());
    }
    let intent: serde_json::Value =
        serde_json::from_slice(&private_file(&directory.join("push-intent.json"), 4096)?)
            .map_err(|e| e.to_string())?;
    let text = |name: &str| -> Result<&str> {
        intent
            .get(name)
            .and_then(|value| value.as_str())
            .ok_or_else(|| format!("retained intent {name} absent"))
    };
    if text("type")? != "mini-gitweb-alice-api-push-intent-v1"
        || text("socket")? != socket.to_str().ok_or("socket path UTF-8")?
        || text("host")? != host
        || text("apiTokenSha256")? != sha(bearer.as_bytes())
    {
        return Err("retained push intent differs from exact entrance".into());
    }
    let commit = text("commit")?;
    let path = text("path")?;
    let file_sha = text("fileSha256")?;
    if !matches!(commit.len(), 40 | 64)
        || !commit.bytes().all(|byte| byte.is_ascii_hexdigit())
        || !ordinary_path(path)
        || file_sha.len() != 64
        || !file_sha.bytes().all(|byte| byte.is_ascii_hexdigit())
    {
        return Err("retained push intent coordinates invalid".into());
    }
    let marker = private_file(&directory.join("receive-pack-forwarded.marker"), 128)?;
    if marker != b"one receive-pack forwarded; reconcile before any retry\n" {
        return Err("retained one-send marker differs".into());
    }
    let repo = directory.join("repo");
    let mut file = repo.clone();
    for part in path.split('/') {
        file.push(part);
        if fs::symlink_metadata(&file)
            .map_err(|e| e.to_string())?
            .file_type()
            .is_symlink()
        {
            return Err("retained Git file path crosses symlink".into());
        }
    }
    let bytes = private_file(&file, MAX_FILE)?;
    if sha(&bytes) != file_sha {
        return Err("retained Git file differs from pre-push intent".into());
    }
    let local_commit = checked_git_output(&["rev-parse", "HEAD"], &repo, Path::new("/dev/null"))?;
    if local_commit != commit {
        return Err("retained local commit differs from pre-push intent".into());
    }
    let index = (1..=1000)
        .find(|index| {
            !directory.join(format!("lookup-{index:04}.json")).exists()
                && !directory.join(format!("lookup-{index:04}.log")).exists()
        })
        .ok_or("Git lookup evidence names exhausted")?;
    let mut entropy = [0; 32];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut entropy))
        .map_err(|e| e.to_string())?;
    let proxy_token = hex(&entropy);
    let config = directory.join(format!("lookup-{index:04}.gitconfig"));
    write_new(&config, format!("[http]\n\textraHeader = X-Mini-Git-Proxy-Token: {proxy_token}\n\tfollowRedirects = false\n[protocol]\n\tversion = 0\n[credential]\n\thelper =\n").as_bytes())?;
    let listener = TcpListener::bind("127.0.0.1:0").map_err(|e| e.to_string())?;
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let url = format!(
        "http://127.0.0.1:{}/repo.git",
        listener.local_addr().map_err(|e| e.to_string())?.port()
    );
    let mut bridge = Bridge {
        socket,
        host: host.to_owned(),
        bearer,
        proxy_token,
        directory: directory.clone(),
        calls: 0,
        read_only: true,
    };
    let log = directory.join(format!("lookup-{index:04}.log"));
    git_command(
        &["ls-remote", &url, "refs/heads/master"],
        &repo,
        &config,
        &log,
        Some(&listener),
        &mut bridge,
    )?;
    let remote = remote_master(&log)?;
    let matches = remote.as_deref() == Some(commit);
    let result = json!({"type":"mini-gitweb-alice-api-lookup-v1","expectedCommit":commit,
        "observedRemoteCommit":remote,"matchesExpected":matches,"receivePackForwarded":true,
        "nativeReceiptClaim":false});
    write_new(
        &directory.join(format!("lookup-{index:04}.json")),
        format!("{result}\n").as_bytes(),
    )?;
    sync_dir(&directory)?;
    println!("{result}");
    if !matches {
        return Err("remote master differs; no mutation was retried".into());
    }
    Ok(())
}

fn view(args: &[String]) -> Result<()> {
    if args.len() != 8 {
        return Err("view-web WEB-UNIX-SOCKET BROWSER-TOKEN-600 EXPECTED-HOST COMMIT-OID FILE-PATH EXPECTED-SHA256 NEW-RESULT.json".into());
    }
    let socket = PathBuf::from(&args[1]);
    socket_file(&socket)?;
    let token_path = Path::new(&args[2]);
    if socket.parent() != token_path.parent()
        || token_path.file_name().and_then(|name| name.to_str()) != Some("browser.token")
    {
        return Err("browser token differs from native entrance directory".into());
    }
    let token = exact_token(token_path)?;
    let host = &args[3];
    if !host_name(host) {
        return Err("expected Host invalid".into());
    }
    let commit = &args[4];
    if !matches!(commit.len(), 40 | 64) || !commit.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("full commit OID invalid".into());
    }
    let path = &args[5];
    if !ordinary_path(path) {
        return Err("Git file path invalid".into());
    }
    let expected = &args[6];
    if expected.len() != 64 || !expected.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("expected file SHA invalid".into());
    }
    let output = PathBuf::from(&args[7]);
    private_parent(&output)?;
    let target = format!("/gitweb.cgi?p=repo.git;a=blob_plain;f={path};hb={commit}");
    let request = format!("GET {target} HTTP/1.1\r\nHost: {host}\r\nCookie: __Host-mini_spk_session={token}\r\nConnection: close\r\n\r\n");
    let reply = unix_http(&socket, request.as_bytes(), Instant::now() + CALL_WALL)?;
    let (status, _, body) = parse_http_response(&reply)?;
    if status != 200 || sha(body) != *expected {
        return Err("human GitWeb blob differs from selected file".into());
    }
    let result = json!({"type":"mini-gitweb-human-view-v1","commit":commit,
        "path":path,"fileSha256":expected,"bytes":body.len()});
    write_new(&output, format!("{result}\n").as_bytes())?;
    println!("{result}");
    Ok(())
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("seed-api") => seed(&args),
        Some("lookup-api") => lookup(&args),
        Some("view-web") => view(&args),
        _ => Err("usage: gitweb-human-journey seed-api|lookup-api|view-web ...".into()),
    };
    if let Err(error) = result {
        eprintln!("gitweb-human-journey: {error}");
        std::process::exit(2);
    }
}
