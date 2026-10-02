//! Bounded Unix-only HTTP entrance for one participant credential custodian.
//!
//! Transport tokens authenticate use of that custodian; they are not Mini
//! resource authority. The current public binary serves an unavailable
//! response; the resident signer/permit path is staged separately.

use crate::hostd::Journal;
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::{Path, PathBuf};
use std::sync::{mpsc, Arc, Mutex};
use std::time::{Duration, Instant};

const MAX_HEAD: usize = 64 * 1024;
const MAX_BODY: usize = 8 * 1024 * 1024;
const MAX_PATH: usize = 8192;
const MAX_HEADERS: usize = 128;
const DEADLINE: Duration = Duration::from_secs(10);
const SESSION_COOKIE: &str = "__Host-mini_spk_session";
const BOOTSTRAP_PATH: &str = "__mini/bootstrap";
const BOOTSTRAP_FORM: &[u8] = b"<!doctype html><html><head><meta charset=\"utf-8\"><title>Private Mini sign-in</title></head><body><form method=\"post\" action=\"/__mini/bootstrap\"><label>Private bootstrap token <input name=\"token\" autocomplete=\"off\" required></label><button type=\"submit\">Sign in</button></form></body></html>";

fn refuse(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Method {
    Get,
    Head,
    Post,
    Put,
    Patch,
    Delete,
    /// A `GET` carrying a valid RFC 6455 upgrade: a streamed dispatch whose
    /// one Mini write is the open (Sandstorm `openWebSocket`).
    WebSocket,
}

impl Method {
    #[allow(dead_code)] // Consumed by the reviewed resident Mini HTTP caller.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Get => "GET",
            Self::Head => "HEAD",
            Self::Post => "POST",
            Self::Put => "PUT",
            Self::Patch => "PATCH",
            Self::Delete => "DELETE",
            Self::WebSocket => crate::dispatch_inspection::STREAMED_OPEN_METHOD,
        }
    }
    fn parse(value: &str) -> io::Result<Self> {
        match value {
            "GET" => Ok(Self::Get),
            "HEAD" => Ok(Self::Head),
            "POST" => Ok(Self::Post),
            "PUT" => Ok(Self::Put),
            "PATCH" => Ok(Self::Patch),
            "DELETE" => Ok(Self::Delete),
            _ => Err(refuse("HTTP method unavailable")),
        }
    }

    fn safe(self) -> bool {
        matches!(self, Self::Get | Self::Head)
    }
}

#[derive(Debug)]
pub(crate) struct ReceivedRequest {
    response_stream: Option<UnixStream>,
    pub method: Method,
    #[allow(dead_code)] // Consumed only after Mini's checked dispatch projector is wired.
    pub path_and_query: String,
    pub ordinary_headers: Vec<(String, String)>,
    pub body: Vec<u8>,
    host: String,
    origin: Option<String>,
    authorization: Option<String>,
    cookie: Option<String>,
    fetch_site: Option<String>,
    fetch_mode: Option<String>,
    fetch_dest: Option<String>,
    /// The validated handshake of a WebSocket open; the entrance attaches the
    /// client stream only after transport authentication.
    pub websocket: Option<crate::web_socket::Handshake>,
    pub upgrade_stream: Option<UnixStream>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum EntranceKind {
    Browser,
    Api,
}

#[derive(Clone)]
pub(crate) struct CustodianPolicy {
    /// The one participant's configured HTTPS origin. It is not HTTP input.
    pub expected_host: String,
    #[allow(dead_code)] // Becomes Mini authoring input only after its native route exists.
    pub fixed_app: String,
    #[allow(dead_code)]
    pub fixed_subject: String,
    #[allow(dead_code)]
    pub fixed_session: String,
    /// Bound to the Mini session, never inferred from the bearer or cookie.
    pub fixed_session_kind: EntranceKind,
    pub export_capture: bool,
    pub export_capture_path: Option<String>,
    #[allow(dead_code)]
    pub fixed_ticket: String,
    pub browser_token_sha256: [u8; 32],
    pub bootstrap_token_sha256: [u8; 32],
    pub api_token_sha256: [u8; 32],
}

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PolicyFile {
    protocol: String,
    expected_host: String,
    fixed_app: String,
    fixed_subject: String,
    fixed_session: String,
    fixed_session_kind: String,
    #[serde(default)]
    export_capture: bool,
    #[serde(default)]
    export_capture_path: Option<String>,
    fixed_ticket: String,
    browser_token_sha256: String,
    bootstrap_token_sha256: String,
    api_token_sha256: String,
}

fn canonical_nat(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

pub(crate) fn valid_export_path(path: &str) -> bool {
    let Some(sheet) = path.strip_prefix("_/").and_then(|p| p.strip_suffix("/csv")) else { return false };
    !sheet.is_empty() && sheet.len() <= 128 && sheet.bytes().all(|b| b.is_ascii_alphanumeric() || b"-_".contains(&b))
}

pub(crate) fn valid_expected_host(host: &str) -> bool {
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

fn hex_digest(value: &str) -> io::Result<[u8; 32]> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(refuse("custodian token hash is not lowercase SHA-256"));
    }
    let mut digest = [0_u8; 32];
    for (index, pair) in value.as_bytes().as_chunks::<2>().0.iter().enumerate() {
        let high = (pair[0] as char)
            .to_digit(16)
            .ok_or_else(|| refuse("token hash hex"))?;
        let low = (pair[1] as char)
            .to_digit(16)
            .ok_or_else(|| refuse("token hash hex"))?;
        digest[index] = ((high << 4) | low) as u8;
    }
    Ok(digest)
}

impl CustodianPolicy {
    pub(crate) fn load(directory: &Path) -> io::Result<Self> {
        Self::load_with_bytes(directory).map(|(policy, _)| policy)
    }

    pub(crate) fn load_with_bytes(directory: &Path) -> io::Result<(Self, Vec<u8>)> {
        let _ = Journal::open(directory)?;
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(directory.join("custodian.json"))?;
        let meta = file.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() > 4096
        {
            return Err(refuse("custodian config identity, mode or length drift"));
        }
        let mut bytes = Vec::new();
        file.take(4097).read_to_end(&mut bytes)?;
        if bytes.len() > 4096 {
            return Err(refuse("custodian config grew"));
        }
        Ok((Self::from_bytes(&bytes)?, bytes))
    }

    pub(crate) fn verify_tokens(&self, directory: &Path) -> io::Result<()> {
        read_private_token(directory, "browser.token", &self.browser_token_sha256)?;
        read_private_token(directory, "bootstrap.token", &self.bootstrap_token_sha256)?;
        read_private_token(directory, "api.token", &self.api_token_sha256)?;
        Ok(())
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> io::Result<Self> {
        let parsed: PolicyFile = serde_json::from_slice(bytes)?;
        if parsed.protocol != "mini-spk-custodian-v1"
            || !valid_expected_host(&parsed.expected_host)
            || !canonical_nat(&parsed.fixed_app)
            || !canonical_nat(&parsed.fixed_subject)
            || !canonical_nat(&parsed.fixed_session)
            || !canonical_nat(&parsed.fixed_ticket)
            || !matches!(parsed.fixed_session_kind.as_str(), "web" | "api")
            || parsed.export_capture != parsed.export_capture_path.is_some()
            || parsed.export_capture_path.as_deref().is_some_and(|p| !valid_export_path(p))
        {
            return Err(refuse("custodian origin or fixed Mini coordinate refused"));
        }
        Ok(Self {
            expected_host: parsed.expected_host,
            fixed_app: parsed.fixed_app,
            fixed_subject: parsed.fixed_subject,
            fixed_session: parsed.fixed_session,
            fixed_session_kind: if parsed.fixed_session_kind == "web" {
                EntranceKind::Browser
            } else {
                EntranceKind::Api
            },
            fixed_ticket: parsed.fixed_ticket,
            export_capture: parsed.export_capture,
            export_capture_path: parsed.export_capture_path,
            browser_token_sha256: hex_digest(&parsed.browser_token_sha256)?,
            bootstrap_token_sha256: hex_digest(&parsed.bootstrap_token_sha256)?,
            api_token_sha256: hex_digest(&parsed.api_token_sha256)?,
        })
    }
}

fn random_token() -> io::Result<String> {
    let mut bytes = [0_u8; 32];
    File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    let mut token = String::with_capacity(64);
    for byte in bytes {
        use std::fmt::Write as _;
        write!(token, "{byte:02x}").map_err(io::Error::other)?;
    }
    Ok(token)
}

fn write_private(directory: &Path, name: &str, bytes: &[u8]) -> io::Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(directory.join(name))?;
    file.write_all(bytes)?;
    file.sync_all()
}

/// Create a new, never-overwritten custodian. Tokens are written only to
/// owner-private files, never stdout, an argument, URL or service log.
pub fn initialize_custodian(
    directory: &Path,
    expected_host: &str,
    app: &str,
    subject: &str,
    session: &str,
    ticket: &str,
    session_kind: &str,
) -> io::Result<()> {
    initialize_custodian_policy(directory, expected_host, app, subject, session, ticket, (session_kind, false, None))
}

/// An explicitly enabled, fixed-participant CSV capture route for document exports.
pub fn initialize_connector_custodian(
    directory: &Path, expected_host: &str, app: &str, subject: &str,
    session: &str, ticket: &str, capture_scope: (&str, &str),
) -> io::Result<()> {
    initialize_custodian_policy(directory, expected_host, app, subject, session, ticket, (capture_scope.0, true, Some(capture_scope.1)))
}

fn initialize_custodian_policy(
    directory: &Path,
    expected_host: &str,
    app: &str,
    subject: &str,
    session: &str,
    ticket: &str,
    session_policy: (&str, bool, Option<&str>),
) -> io::Result<()> {
    let (session_kind, export_capture, export_capture_path) = session_policy;
    if !valid_expected_host(expected_host)
        || !matches!(session_kind, "web" | "api")
        || export_capture != export_capture_path.is_some()
        || export_capture_path.is_some_and(|p| !valid_export_path(p))
        || ![app, subject, session, ticket]
            .into_iter()
            .all(canonical_nat)
    {
        return Err(refuse("custodian bootstrap coordinates refused"));
    }
    let parent = directory
        .parent()
        .ok_or_else(|| refuse("custodian parent missing"))?;
    let _ = Journal::open(parent)?;
    fs::DirBuilder::new().mode(0o700).create(directory)?;
    let _ = Journal::open(directory)?;
    let bootstrap = random_token()?;
    let browser = random_token()?;
    let api = random_token()?;
    let digest = |token: &str| format!("{:x}", Sha256::digest(token.as_bytes()));
    let config = PolicyFile {
        protocol: "mini-spk-custodian-v1".into(),
        expected_host: expected_host.into(),
        fixed_app: app.into(),
        fixed_subject: subject.into(),
        fixed_session: session.into(),
        fixed_session_kind: session_kind.into(),
        export_capture,
        export_capture_path: export_capture_path.map(str::to_owned),
        fixed_ticket: ticket.into(),
        browser_token_sha256: digest(&browser),
        bootstrap_token_sha256: digest(&bootstrap),
        api_token_sha256: digest(&api),
    };
    write_private(directory, "browser.token", browser.as_bytes())?;
    write_private(directory, "bootstrap.token", bootstrap.as_bytes())?;
    write_private(directory, "api.token", api.as_bytes())?;
    write_private(directory, "custodian.json", &serde_json::to_vec(&config)?)?;
    File::open(directory)?.sync_all()?;
    let _ = CustodianPolicy::load(directory)?;
    Ok(())
}

fn token_matches(token: &str, expected: &[u8; 32]) -> bool {
    // A high-entropy bearer or cookie token is provisioned outside this module.
    // Compare its digest without an early byte-dependent return.
    if token.len() < 32 || token.len() > 256 || !token.is_ascii() {
        return false;
    }
    let digest = Sha256::digest(token.as_bytes());
    let mut different = 0_u8;
    for (left, right) in digest.iter().zip(expected) {
        different |= left ^ right;
    }
    different == 0
}

fn session_cookie(raw: &str) -> io::Result<(String, Option<String>)> {
    let mut credential = None;
    let mut ordinary = Vec::new();
    for part in raw.split(';') {
        let item = part.trim();
        if item.is_empty() {
            continue;
        }
        let (name, value) = item
            .split_once('=')
            .ok_or_else(|| refuse("malformed HTTP cookie"))?;
        if name == SESSION_COOKIE {
            if credential.replace(value.to_owned()).is_some() {
                return Err(refuse("duplicate session cookie"));
            }
        } else {
            ordinary.push(item);
        }
    }
    Ok((ordinary.join("; "), credential))
}

fn allowed_ordinary_header(name: &str) -> bool {
    matches!(
        name,
        "accept"
            | "accept-encoding"
            | "content-type"
            | "user-agent"
            | "if-match"
            | "if-none-match"
            | "x-requested-with"
            | "x-csrftoken"
            | "x-csrf-token"
            | "oc-total-length"
            | "oc-chunk-size"
            | "x-oc-mtime"
            | "oc-fileid"
            | "oc-chunked"
            | "oc-checksum"
            | "oc-chunk-offset"
            | "oc-lazyops"
    )
}

fn header_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 128
        && name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"!#$%&'*+-.^_`|~".contains(&byte))
}

fn parse_head(head: &[u8]) -> io::Result<(ReceivedRequest, usize)> {
    let text = std::str::from_utf8(head).map_err(|_| refuse("HTTP headers are not UTF-8"))?;
    let mut lines = text.split("\r\n");
    let request_line = lines
        .next()
        .ok_or_else(|| refuse("missing HTTP request line"))?;
    let words: Vec<_> = request_line.split(' ').collect();
    if words.len() != 3 || words[2] != "HTTP/1.1" {
        return Err(refuse("only one HTTP/1.1 request is supported"));
    }
    let method = Method::parse(words[0])?;
    let target = words[1];
    if !target.starts_with('/')
        || target.len() > MAX_PATH + 1
        || target.contains('#')
        || target.bytes().any(|byte| byte < 0x20 || byte == 0x7f)
        || target.bytes().filter(|byte| *byte == b'?').count() > 1
    {
        return Err(refuse("invalid HTTP request target"));
    }
    let mut seen = HashSet::new();
    let mut host = None;
    let mut origin = None;
    let mut authorization = None;
    let mut cookie = None;
    let mut fetch_site = None;
    let mut fetch_mode = None;
    let mut fetch_dest = None;
    let mut connection = None;
    let mut upgrade = None;
    let mut websocket_key = None;
    let mut websocket_version = None;
    let mut websocket_protocol = None;
    let mut body_len = None;
    let mut ordinary_headers = Vec::new();
    for line in lines {
        if line.is_empty() {
            continue;
        }
        if seen.len() >= MAX_HEADERS {
            return Err(refuse("too many HTTP headers"));
        }
        let (raw_name, raw_value) = line
            .split_once(':')
            .ok_or_else(|| refuse("malformed HTTP header"))?;
        if !header_name(raw_name)
            || raw_value.len() > 8192
            || raw_value
                .bytes()
                .any(|byte| (byte < 0x20 && byte != b'\t') || byte == 0x7f)
        {
            return Err(refuse("invalid HTTP header"));
        }
        let name = raw_name.to_ascii_lowercase();
        if !seen.insert(name.clone()) {
            return Err(refuse("duplicate HTTP header"));
        }
        let value = raw_value.trim().to_owned();
        match name.as_str() {
            "host" => host = Some(value),
            "origin" => origin = Some(value),
            "authorization" => authorization = Some(value),
            "cookie" => cookie = Some(value),
            "sec-fetch-site" => fetch_site = Some(value),
            "sec-fetch-mode" => fetch_mode = Some(value),
            "sec-fetch-dest" => fetch_dest = Some(value),
            "connection" => connection = Some(value),
            "upgrade" => upgrade = Some(value),
            "sec-websocket-key" => websocket_key = Some(value),
            "sec-websocket-version" => websocket_version = Some(value),
            "sec-websocket-protocol" => websocket_protocol = Some(value),
            "content-length" => {
                if value.is_empty()
                    || (value.len() > 1 && value.starts_with('0'))
                    || !value.bytes().all(|byte| byte.is_ascii_digit())
                {
                    return Err(refuse("noncanonical HTTP content length"));
                }
                body_len = Some(
                    value
                        .parse::<usize>()
                        .map_err(|_| refuse("HTTP body length overflow"))?,
                );
            }
            "transfer-encoding" | "expect" | "content-encoding" => {
                return Err(refuse("unsupported HTTP transfer encoding"));
            }
            name if name.starts_with("x-sandstorm-") => {
                return Err(refuse("caller-supplied Sandstorm header"));
            }
            name if allowed_ordinary_header(name) || name == "x-mini-export-capture" => {
                ordinary_headers.push((name.to_owned(), value))
            }
            _ => {} // Browser/proxy metadata is never forwarded to Mini or the app.
        }
    }
    let host = host.ok_or_else(|| refuse("missing HTTP Host"))?;
    let body_len = body_len.unwrap_or(0);
    // An upgrade is a WebSocket open or nothing. Its subprotocol list is an
    // app-visible input, so it is signed like an ordinary header; the
    // extensions offer is declined (never forwarded, never accepted).
    let (method, websocket) = match upgrade {
        None => {
            if websocket_key.is_some()
                || websocket_version.is_some()
                || websocket_protocol.is_some()
            {
                return Err(refuse("WebSocket header without an upgrade"));
            }
            (method, None)
        }
        Some(upgrade) => {
            if method != Method::Get || body_len != 0 {
                return Err(refuse("WebSocket upgrade is not a bodyless GET"));
            }
            let handshake = crate::web_socket::client_handshake(
                connection.as_deref(),
                &upgrade,
                websocket_key.as_deref(),
                websocket_version.as_deref(),
            )?;
            if let Some(protocols) = websocket_protocol {
                crate::web_socket::protocols(Some(&protocols))?;
                ordinary_headers.push(("sec-websocket-protocol".to_owned(), protocols));
            }
            (Method::WebSocket, Some(handshake))
        }
    };
    if body_len > MAX_BODY {
        return Err(refuse("HTTP body exceeds native bound"));
    }
    if target == "/__mini/bootstrap" && body_len > 128 {
        return Err(refuse("bootstrap form exceeds bound"));
    }
    if matches!(method, Method::Get | Method::Head | Method::Delete) && body_len != 0 {
        return Err(refuse("method cannot carry HTTP body"));
    }
    Ok((
        ReceivedRequest {
            response_stream: None,
            method,
            path_and_query: target[1..].to_owned(),
            ordinary_headers,
            body: Vec::new(),
            host,
            origin,
            authorization,
            cookie,
            fetch_site,
            fetch_mode,
            fetch_dest,
            websocket,
            upgrade_stream: None,
        },
        body_len,
    ))
}

fn read_until(
    stream: &mut UnixStream,
    bytes: &mut Vec<u8>,
    minimum: usize,
    deadline: Instant,
) -> io::Result<()> {
    stream.set_nonblocking(true)?;
    while bytes.len() < minimum {
        if Instant::now() >= deadline {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "HTTP frame deadline",
            ));
        }
        let mut chunk = [0_u8; 8192];
        match stream.read(&mut chunk) {
            Ok(0) => return Err(refuse("HTTP frame ended early")),
            Ok(count) => bytes.extend_from_slice(&chunk[..count]),
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                std::thread::sleep(Duration::from_millis(2))
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
        if bytes.len() > MAX_HEAD + MAX_BODY + 8192 {
            return Err(refuse("HTTP frame too large"));
        }
    }
    Ok(())
}

fn read_request_until(stream: &mut UnixStream, deadline: Instant) -> io::Result<ReceivedRequest> {
    let mut bytes = Vec::with_capacity(8192);
    let head_end = loop {
        if let Some(index) = bytes.windows(4).position(|window| window == b"\r\n\r\n") {
            break index + 4;
        }
        if bytes.len() > MAX_HEAD {
            return Err(refuse("HTTP header exceeds bound"));
        }
        let minimum = bytes.len() + 1;
        read_until(stream, &mut bytes, minimum, deadline)?;
    };
    if head_end > MAX_HEAD {
        return Err(refuse("HTTP header exceeds bound"));
    }
    let (mut request, body_len) = parse_head(&bytes[..head_end - 4])?;
    let total = head_end
        .checked_add(body_len)
        .ok_or_else(|| refuse("HTTP frame length overflow"))?;
    read_until(stream, &mut bytes, total, deadline)?;
    if bytes.len() != total {
        return Err(refuse("HTTP pipelining is unsupported"));
    }
    request.body.extend_from_slice(&bytes[head_end..]);
    Ok(request)
}

pub(crate) fn read_request(stream: &mut UnixStream) -> io::Result<ReceivedRequest> {
    read_request_until(stream, Instant::now() + DEADLINE)
}

impl CustodianPolicy {
    /// Only transport authentication. Mini must still sign as the fixed
    /// participant and check each request against current native authority.
    pub(crate) fn authenticate(&self, request: &mut ReceivedRequest) -> io::Result<EntranceKind> {
        if self.expected_host.is_empty() || request.host.to_ascii_lowercase() != self.expected_host
        {
            return Err(refuse("HTTP Host differs from fixed custodian origin"));
        }
        let expected_origin = format!("https://{}", self.expected_host);
        if request
            .origin
            .as_deref()
            .is_some_and(|value| value != expected_origin)
        {
            return Err(refuse("HTTP Origin differs from custodian origin"));
        }
        match request.fetch_site.as_deref() {
            None | Some("same-origin") => {}
            Some("none")
                if request.method.safe()
                    && request
                        .fetch_mode
                        .as_deref()
                        .is_none_or(|value| value == "navigate")
                    && request
                        .fetch_dest
                        .as_deref()
                        .is_none_or(|value| value == "document") => {}
            _ => return Err(refuse("HTTP Fetch Metadata differs from custodian origin")),
        }
        match (request.authorization.take(), request.cookie.take()) {
            (Some(auth), None) => {
                let token = auth
                    .strip_prefix("Bearer ")
                    .ok_or_else(|| refuse("API bearer syntax"))?;
                if !token_matches(token, &self.api_token_sha256) {
                    return Err(refuse("API transport credential refused"));
                }
                if self.fixed_session_kind != EntranceKind::Api {
                    return Err(refuse("API token differs from fixed Mini session kind"));
                }
                Ok(EntranceKind::Api)
            }
            (None, Some(raw_cookie)) => {
                let (ordinary_cookie, token) = session_cookie(&raw_cookie)?;
                let token = token.ok_or_else(|| refuse("browser session cookie missing"))?;
                if !token_matches(&token, &self.browser_token_sha256) {
                    return Err(refuse("browser transport credential refused"));
                }
                if self.fixed_session_kind != EntranceKind::Browser {
                    return Err(refuse(
                        "browser cookie differs from fixed Mini session kind",
                    ));
                }
                if !request.method.safe()
                    && request.origin.as_deref() != Some(expected_origin.as_str())
                {
                    return Err(refuse("browser Origin missing or different"));
                }
                if !ordinary_cookie.is_empty() {
                    if request.ordinary_headers.len() >= MAX_HEADERS {
                        return Err(refuse("too many forwarded HTTP headers"));
                    }
                    request
                        .ordinary_headers
                        .push(("cookie".into(), ordinary_cookie));
                }
                Ok(EntranceKind::Browser)
            }
            _ => Err(refuse("exactly one transport credential required")),
        }
    }
}

const MAX_PENDING_REQUESTS: usize = 16;
const MAX_PENDING_PER_SUBJECT: usize = 2;
const QUEUE_DEADLINE: Duration = Duration::from_secs(30);

#[derive(Default)]
struct Admission {
    total: usize,
    subjects: HashMap<String, usize>,
}
struct AdmissionGuard {
    admission: Arc<Mutex<Admission>>,
    subject: String,
}
impl AdmissionGuard {
    fn reserve(admission: &Arc<Mutex<Admission>>, subject: &str) -> io::Result<Option<Self>> {
        let mut state = admission
            .lock()
            .map_err(|_| refuse("admission lock poisoned"))?;
        if state.total >= MAX_PENDING_REQUESTS
            || state.subjects.get(subject).copied().unwrap_or(0) >= MAX_PENDING_PER_SUBJECT
        {
            return Ok(None);
        }
        state.total += 1;
        *state.subjects.entry(subject.into()).or_default() += 1;
        Ok(Some(Self {
            admission: admission.clone(),
            subject: subject.into(),
        }))
    }
}
impl Drop for AdmissionGuard {
    fn drop(&mut self) {
        if let Ok(mut state) = self.admission.lock() {
            state.total -= 1;
            if let Some(count) = state.subjects.get_mut(&self.subject) {
                *count -= 1;
                if *count == 0 {
                    state.subjects.remove(&self.subject);
                }
            }
        }
    }
}
struct ParsedRequest {
    index: usize,
    request: ReceivedRequest,
    kind: EntranceKind,
    policy: CustodianPolicy,
    stream: UnixStream,
    queued_at: Instant,
    _guard: AdmissionGuard,
}
fn fair_pending_index(
    pending: &VecDeque<ParsedRequest>,
    served: &HashMap<String, u64>,
) -> Option<usize> {
    pending
        .iter()
        .enumerate()
        .min_by_key(|(_, request)| {
            served
                .get(&request.policy.fixed_subject)
                .copied()
                .unwrap_or(0)
        })
        .map(|(index, _)| index)
}
pub(crate) fn admission_response(method: Method, status: &str) -> Vec<u8> {
    let body = format!(
        "{{\"protocol\":\"mini-spk-admission-v1\",\"status\":\"{status}\",\"retry\":\"{}\"}}\n",
        if status == "busy" {
            "new-request"
        } else {
            "exact-recovery-only"
        }
    );
    let mut bytes = format!("HTTP/1.1 503 Service Unavailable\r\nContent-Length: {}\r\nContent-Type: application/json\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n", body.len()).into_bytes();
    if method != Method::Head {
        bytes.extend_from_slice(body.as_bytes());
    }
    bytes
}
fn write_response_bounded(stream: &UnixStream, mut bytes: &[u8]) -> io::Result<()> {
    let deadline = Instant::now() + DEADLINE;
    while !bytes.is_empty() {
        let left = deadline
            .checked_duration_since(Instant::now())
            .ok_or_else(|| io::Error::new(io::ErrorKind::TimedOut, "HTTP response deadline"))?;
        let mut poll = [libc::pollfd {
            fd: stream.as_raw_fd(),
            events: libc::POLLOUT,
            revents: 0,
        }];
        if !poll_entrances(&mut poll, left.as_millis().min(i32::MAX as u128) as i32)? {
            continue;
        }
        let sent = unsafe {
            libc::send(
                stream.as_raw_fd(),
                bytes.as_ptr().cast(),
                bytes.len(),
                libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL,
            )
        };
        if sent > 0 {
            bytes = &bytes[sent as usize..];
        } else {
            let error = io::Error::last_os_error();
            if !matches!(
                error.kind(),
                io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
            ) {
                return Err(error);
            }
        }
    }
    Ok(())
}
fn dispatch_error_response(method: Method, error: &io::Error) -> Vec<u8> {
    if error.kind() == io::ErrorKind::WouldBlock {
        admission_response(method, "busy")
    } else if error.kind() == io::ErrorKind::Interrupted {
        admission_response(method, "uncertain")
    } else {
        unavailable_response(method)
    }
}

/// A same-UID, owner-private Unix entrance. No TCP listener or Mini signer is
/// created here. Under the owner lock, an owned socket is removed only when
/// connect reports ConnectionRefused and its device/inode are unchanged.
pub struct PrivateHttpEntrance {
    listener: UnixListener,
    socket: PathBuf,
    socket_dev: u64,
    socket_ino: u64,
    _lock: std::fs::File,
    policy: CustodianPolicy,
}

impl PrivateHttpEntrance {
    /// Append-only registration keeps every existing participant index and
    /// accepted stream intact. Auxiliary callbacks may append a listener only
    /// after their own current Mini admission has succeeded.
    pub(crate) fn serve_dynamic_with_aux(
        mut entrances: Vec<Self>,
        auxiliary_fds: &[libc::c_int],
        mut dispatch: impl FnMut(
            Result<(usize, ReceivedRequest, EntranceKind, &CustodianPolicy), usize>,
            &mut Vec<Self>,
        ) -> io::Result<Option<Vec<u8>>>,
    ) -> io::Result<()> {
        if entrances.is_empty() || auxiliary_fds.len() > 10 {
            return Err(refuse("resident entrance count refused"));
        }
        // Only unadmitted requests live in this queue. A restart may drop them;
        // no operation ID, Store record or physical effect has been allocated.
        let admission = Arc::new(Mutex::new(Admission::default()));
        let (sender, receiver) = mpsc::sync_channel(MAX_PENDING_REQUESTS);
        let mut pending: VecDeque<ParsedRequest> = VecDeque::new();
        let mut served: HashMap<String, u64> = HashMap::new();
        let mut clock = 0_u64;
        let mut next_route = 0_usize;
        loop {
            if entrances.len() > crate::resident_route_control::MAX_ROUTES {
                return Err(refuse("resident route limit reached"));
            }
            pending.extend(receiver.try_iter());
            let prior_count = entrances.len();
            let mut polls: Vec<libc::pollfd> = entrances
                .iter()
                .map(|entrance| libc::pollfd {
                    fd: entrance.listener.as_raw_fd(),
                    events: libc::POLLIN,
                    revents: 0,
                })
                .collect();
            for fd in auxiliary_fds {
                if *fd < 0 || polls.iter().any(|poll| poll.fd == *fd) {
                    return Err(refuse("resident auxiliary fd refused"));
                }
                polls.push(libc::pollfd {
                    fd: *fd,
                    events: libc::POLLIN,
                    revents: 0,
                });
            }
            // Readers notify through the bounded channel. Poll at a short bound
            // while they exist, and block normally when the app is idle.
            let active = admission
                .lock()
                .map_err(|_| refuse("admission lock poisoned"))?
                .total;
            let timeout = if !pending.is_empty() {
                0
            } else if active > 0 {
                20
            } else {
                -1
            };
            let _ = poll_entrances(&mut polls, timeout)?;
            for (index, auxiliary) in polls.iter().skip(prior_count).enumerate() {
                if auxiliary.revents & (libc::POLLERR | libc::POLLHUP | libc::POLLNVAL) != 0 {
                    return Err(refuse("resident auxiliary poll error"));
                }
                if auxiliary.revents & libc::POLLIN != 0 {
                    let _ = dispatch(Err(index), &mut entrances)?;
                }
            }
            // Rotate listener acceptance, then select queued work by principal's
            // last service turn. Multiple routes do not buy a principal priority.
            for offset in 0..prior_count {
                let index = (next_route + offset) % prior_count;
                let poll = &polls[index];
                if poll.revents & (libc::POLLERR | libc::POLLHUP | libc::POLLNVAL) != 0 {
                    return Err(refuse("resident entrance poll error"));
                }
                if poll.revents & libc::POLLIN == 0 {
                    continue;
                }
                let entrance = &entrances[index];
                let (mut stream, _) = entrance.listener.accept()?;
                if peer_uid(&stream) != Some(unsafe { libc::geteuid() }) {
                    continue;
                }
                let policy = entrance.policy.clone();
                let mut guard = match AdmissionGuard::reserve(&admission, &policy.fixed_subject)? {
                    Some(guard) => Some(guard),
                    None => {
                        let _ = stream.write_all(&admission_response(Method::Get, "busy"));
                        continue;
                    }
                };
                let directory = entrance.socket.parent().map(Path::to_path_buf);
                let sender = sender.clone();
                std::thread::Builder::new()
                    .name("mini-spk-http-reader".into())
                    .spawn(move || {
                        // Parsing/bootstrap never calls Mini. A held or malformed
                        // reader occupies its own bounded slot, not the dispatch loop.
                        let _ = handle_stream_with(
                            stream,
                            &policy,
                            directory.as_deref(),
                            &mut |request, kind, policy| {
                                let response_stream = request
                                    .response_stream
                                    .as_ref()
                                    .ok_or_else(|| refuse("queued response stream absent"))?
                                    .try_clone()?;
                                let queued = ParsedRequest {
                                    index,
                                    request,
                                    kind,
                                    policy: policy.clone(),
                                    stream: response_stream,
                                    queued_at: Instant::now(),
                                    _guard: guard
                                        .take()
                                        .ok_or_else(|| refuse("reader queued twice"))?,
                                };
                                sender
                                    .send(queued)
                                    .map_err(|_| refuse("resident dispatch loop ended"))?;
                                // Ownership of the response passed to the dispatch loop.
                                Ok(Vec::new())
                            },
                        );
                    })?;
            }
            next_route = (next_route + 1) % entrances.len();
            pending.extend(receiver.try_iter());
            if let Some(index) = fair_pending_index(&pending, &served) {
                let queued = pending.remove(index).expect("selected pending request");
                let method = queued.request.method;
                let response = if queued.queued_at.elapsed() >= QUEUE_DEADLINE {
                    admission_response(method, "busy")
                } else {
                    clock = clock
                        .checked_add(1)
                        .ok_or_else(|| refuse("admission turn overflow"))?;
                    served.insert(queued.policy.fixed_subject.clone(), clock);
                    dispatch(
                        Ok((queued.index, queued.request, queued.kind, &queued.policy)),
                        &mut entrances,
                    )
                    .and_then(|reply| reply.ok_or_else(|| refuse("resident HTTP response absent")))
                    .unwrap_or_else(|error| dispatch_error_response(method, &error))
                };
                let stream = queued.stream;
                let guard = queued._guard;
                std::thread::Builder::new()
                    .name("mini-spk-http-response".into())
                    .spawn(move || {
                        let _ = write_response_bounded(&stream, &response);
                        drop(guard);
                    })?;
            }
        }
    }

    pub fn bind(directory: &Path) -> io::Result<Self> {
        Self::bind_fixed(directory, CustodianPolicy::load(directory)?)
    }

    /// The caller retains the already hash-checked policy; do not reopen a
    /// mutable path after current source admission and silently change identity.
    pub(crate) fn bind_fixed(directory: &Path, policy: CustodianPolicy) -> io::Result<Self> {
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(directory.join(".http.lock"))?;
        let meta = lock.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
        {
            return Err(refuse("custodian lock identity drift"));
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "custodian HTTP entrance active",
            ));
        }
        let socket = directory.join("http.sock");
        match fs::symlink_metadata(&socket) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
            Ok(old) => {
                if !old.file_type().is_socket()
                    || old.uid() != unsafe { libc::geteuid() }
                    || old.permissions().mode() & 0o777 != 0o600
                    || old.nlink() != 1
                {
                    return Err(refuse("custodian HTTP stale socket identity drift"));
                }
                match UnixStream::connect(&socket) {
                    Ok(_) => {
                        return Err(io::Error::new(
                            io::ErrorKind::AlreadyExists,
                            "custodian HTTP socket still accepting",
                        ))
                    }
                    Err(error) if error.kind() == io::ErrorKind::ConnectionRefused => {
                        let current = fs::symlink_metadata(&socket)?;
                        if current.dev() != old.dev() || current.ino() != old.ino() {
                            return Err(refuse("custodian HTTP stale socket changed"));
                        }
                        fs::remove_file(&socket)?;
                    }
                    Err(error) => return Err(error),
                }
            }
        }
        let listener = UnixListener::bind(&socket)?;
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600))?;
        let meta = fs::symlink_metadata(&socket)?;
        if !meta.file_type().is_socket() || meta.uid() != unsafe { libc::geteuid() } {
            return Err(refuse("custodian HTTP socket identity drift"));
        }
        Ok(Self {
            listener,
            socket,
            socket_dev: meta.dev(),
            socket_ino: meta.ino(),
            _lock: lock,
            policy,
        })
    }

    pub fn serve_unavailable(&self) -> io::Result<()> {
        self.serve_resident(|request, _, _| Ok(unavailable_response(request.method)))
    }

    /// The caller owns the sole resident RpcDriver and fixed participant
    /// signer. This entrance authenticates transport before invoking it; the
    /// callback must still obtain a fresh Mini permit for every request.
    pub(crate) fn serve_resident(
        &self,
        mut dispatch: impl FnMut(ReceivedRequest, EntranceKind, &CustodianPolicy) -> io::Result<Vec<u8>>,
    ) -> io::Result<()> {
        loop {
            let (stream, _) = self.listener.accept()?;
            if peer_uid(&stream) == Some(unsafe { libc::geteuid() }) {
                let _ =
                    handle_stream_with(stream, &self.policy, self.socket.parent(), &mut dispatch);
            }
        }
    }
}

fn poll_entrances(polls: &mut [libc::pollfd], timeout_ms: i32) -> io::Result<bool> {
    let ready = unsafe { libc::poll(polls.as_mut_ptr(), polls.len() as libc::nfds_t, timeout_ms) };
    if ready < 0 {
        let error = io::Error::last_os_error();
        if error.kind() == io::ErrorKind::Interrupted {
            return Ok(false);
        }
        return Err(error);
    }
    Ok(ready > 0)
}

pub(crate) fn peer_uid(stream: &UnixStream) -> Option<u32> {
    let mut credential = unsafe { std::mem::zeroed::<libc::ucred>() };
    let mut length = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
    if unsafe {
        libc::getsockopt(
            stream.as_raw_fd(),
            libc::SOL_SOCKET,
            libc::SO_PEERCRED,
            (&mut credential as *mut libc::ucred).cast(),
            &mut length,
        )
    } != 0
        || length as usize != std::mem::size_of::<libc::ucred>()
    {
        None
    } else {
        Some(credential.uid)
    }
}

impl Drop for PrivateHttpEntrance {
    fn drop(&mut self) {
        if let Ok(meta) = fs::symlink_metadata(&self.socket) {
            if meta.dev() == self.socket_dev && meta.ino() == self.socket_ino {
                let _ = fs::remove_file(&self.socket);
            }
        }
    }
}

#[cfg(test)]
pub(crate) fn unavailable(stream: UnixStream, policy: &CustodianPolicy) -> io::Result<()> {
    handle_stream(stream, policy, None)
}

fn read_private_token(directory: &Path, name: &str, expected: &[u8; 32]) -> io::Result<String> {
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(directory.join(name))?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() != 64
    {
        return Err(refuse("custodian private token identity drift"));
    }
    let mut token = String::new();
    file.read_to_string(&mut token)?;
    if !token_matches(&token, expected) || !token.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err(refuse("custodian private token hash drift"));
    }
    Ok(token)
}

fn bootstrap(
    mut stream: &UnixStream,
    request: &ReceivedRequest,
    policy: &CustodianPolicy,
    directory: &Path,
) -> io::Result<()> {
    if request.host != policy.expected_host {
        return Err(refuse("bootstrap Host mismatch"));
    }
    match request.method {
        Method::Get => {
            if request
                .fetch_site
                .as_deref()
                .is_some_and(|site| site != "same-origin" && site != "none")
            {
                return Err(refuse("cross-site bootstrap form"));
            }
            let header = format!(
                "HTTP/1.1 200 OK\r\nContent-Type: text/html; charset=utf-8\r\nContent-Length: {}\r\nCache-Control: no-store\r\nReferrer-Policy: no-referrer\r\nContent-Security-Policy: default-src 'none'; form-action 'self'; frame-ancestors 'none'\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n\r\n",
                BOOTSTRAP_FORM.len()
            );
            stream.write_all(header.as_bytes())?;
            stream.write_all(BOOTSTRAP_FORM)
        }
        Method::Post => {
            if request.origin.as_deref()
                != Some(format!("https://{}", policy.expected_host).as_str())
                || request
                    .fetch_site
                    .as_deref()
                    .is_some_and(|site| site != "same-origin")
                || request.authorization.is_some()
                || request.cookie.is_some()
                || request
                    .ordinary_headers
                    .iter()
                    .find(|(name, _)| name == "content-type")
                    .map(|(_, value)| value.as_str())
                    != Some("application/x-www-form-urlencoded")
            {
                return Err(refuse("bootstrap transport context refused"));
            }
            let posted = std::str::from_utf8(&request.body)
                .map_err(|_| refuse("bootstrap token encoding"))?;
            let token = posted
                .strip_prefix("token=")
                .ok_or_else(|| refuse("bootstrap form shape"))?;
            if token.len() != 64
                || !token.bytes().all(|byte| byte.is_ascii_hexdigit())
                || !token_matches(token, &policy.bootstrap_token_sha256)
            {
                return Err(refuse("bootstrap token refused"));
            }
            if directory.join("bootstrap.used").exists() {
                return Err(refuse("bootstrap token already consumed"));
            }
            let browser =
                read_private_token(directory, "browser.token", &policy.browser_token_sha256)?;
            // The marker is durable before the cookie is emitted. A lost reply
            // needs operator review; the bootstrap token is never replayed.
            write_private(directory, "bootstrap.used", b"used\n")?;
            File::open(directory)?.sync_all()?;
            let response = format!(
                "HTTP/1.1 303 See Other\r\nLocation: /\r\nSet-Cookie: {SESSION_COOKIE}={browser}; Secure; HttpOnly; SameSite=Strict; Path=/\r\nContent-Length: 0\r\nCache-Control: no-store\r\nReferrer-Policy: no-referrer\r\nConnection: close\r\n\r\n"
            );
            stream.write_all(response.as_bytes())
        }
        _ => Err(refuse("bootstrap method unavailable")),
    }
}

#[cfg(test)]
fn handle_stream(
    stream: UnixStream,
    policy: &CustodianPolicy,
    directory: Option<&Path>,
) -> io::Result<()> {
    handle_stream_with(stream, policy, directory, &mut |request, _, _| {
        Ok(unavailable_response(request.method))
    })
}

fn unavailable_response(method: Method) -> Vec<u8> {
    let mut bytes = b"HTTP/1.1 503 Service Unavailable\r\nContent-Length: 36\r\nContent-Type: text/plain; charset=utf-8\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n".to_vec();
    if method != Method::Head {
        bytes.extend_from_slice(b"Mini dispatch admission unavailable\n");
    }
    bytes
}

fn handle_stream_with(
    mut stream: UnixStream,
    policy: &CustodianPolicy,
    directory: Option<&Path>,
    dispatch: &mut impl FnMut(ReceivedRequest, EntranceKind, &CustodianPolicy) -> io::Result<Vec<u8>>,
) -> io::Result<()> {
    let mut request = read_request(&mut stream)?;
    if request.path_and_query == BOOTSTRAP_PATH {
        if policy.fixed_session_kind != EntranceKind::Browser {
            stream.write_all(b"HTTP/1.1 404 Not Found\r\nContent-Length: 0\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n")?;
            return Ok(());
        }
        let directory = directory.ok_or_else(|| refuse("bootstrap endpoint unavailable"))?;
        return match bootstrap(&stream, &request, policy, directory) {
            Err(error) if matches!(error.kind(), io::ErrorKind::InvalidData | io::ErrorKind::AlreadyExists) => {
                stream.write_all(b"HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nCache-Control: no-store\r\nConnection: close\r\n\r\n")
            }
            other => other,
        };
    }
    let kind = policy.authenticate(&mut request)?;
    request.response_stream = Some(stream.try_clone()?);
    let method = request.method;
    if request.websocket.is_some() {
        // The fd3 worker owns this duplicate once the open is admitted; on a
        // refusal or failure the response below goes out on the original.
        request.upgrade_stream = Some(stream.try_clone()?);
    }
    // Typed pre-admission busy and retained uncertainty remain distinguishable.
    // Other failures use the ordinary unavailable response.
    // The client sees one uniform 503; the operator's journal gets the
    // reason (an admitted request that failed in delivery, an fd3 refusal,
    // an unrepresentable app response), or a survey cannot say what broke.
    let response = dispatch(request, kind, policy).unwrap_or_else(|error| {
        eprintln!("spk-host: dispatch unavailable ({method:?}): {error}");
        dispatch_error_response(method, &error)
    });
    stream.write_all(&response)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::DirBuilderExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    include!("http_entrance_gitweb_probe.rs");

    #[test]
    fn admission_bounds_principals_and_apps_independently() {
        let state = Arc::new(Mutex::new(Admission::default()));
        let mut held = Vec::new();
        for principal in 0..8 {
            for _ in 0..2 {
                held.push(
                    AdmissionGuard::reserve(&state, &principal.to_string())
                        .unwrap()
                        .unwrap(),
                );
            }
            assert!(AdmissionGuard::reserve(&state, &principal.to_string())
                .unwrap()
                .is_none());
        }
        assert!(AdmissionGuard::reserve(&state, "new").unwrap().is_none());
        let other = Arc::new(Mutex::new(Admission::default()));
        assert!(AdmissionGuard::reserve(&other, "new").unwrap().is_some());
        drop(held);
        assert!(AdmissionGuard::reserve(&state, "new").unwrap().is_some());
        assert!(String::from_utf8(admission_response(Method::Get, "busy"))
            .unwrap()
            .contains("new-request"));
        assert!(
            String::from_utf8(admission_response(Method::Get, "uncertain"))
                .unwrap()
                .contains("exact-recovery-only")
        );
    }
    #[test]
    fn principal_turns_are_fair_across_multiple_routes() {
        let state = Arc::new(Mutex::new(Admission::default()));
        let make = |principal: &str| {
            let (stream, _) = UnixStream::pair().unwrap();
            let mut policy = policy();
            policy.fixed_subject = principal.into();
            ParsedRequest {
                index: 0,
                request: parsed("GET / HTTP/1.1\r\nHost: friend.example.test\r\n\r\n").unwrap(),
                kind: EntranceKind::Browser,
                policy,
                stream,
                queued_at: Instant::now(),
                _guard: AdmissionGuard::reserve(&state, principal).unwrap().unwrap(),
            }
        };
        let pending = VecDeque::from([make("a"), make("a"), make("b"), make("c")]);
        let mut served = HashMap::from([("a".into(), 4), ("b".into(), 2), ("c".into(), 3)]);
        assert_eq!(fair_pending_index(&pending, &served), Some(2));
        served.insert("b".into(), 5);
        assert_eq!(fair_pending_index(&pending, &served), Some(3));
    }
    #[test]
    fn held_reader_does_not_block_another_members_dispatch() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!("fair-reader-{}-{nonce}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let make = |name: &str, subject: &str| {
            let directory = root.join(name);
            fs::create_dir(&directory).unwrap();
            let socket = directory.join("http.sock");
            let listener = UnixListener::bind(&socket).unwrap();
            let metadata = fs::symlink_metadata(&socket).unwrap();
            let mut policy = policy();
            policy.fixed_subject = subject.into();
            PrivateHttpEntrance {
                listener,
                socket,
                socket_dev: metadata.dev(),
                socket_ino: metadata.ino(),
                _lock: File::create(directory.join(".lock")).unwrap(),
                policy,
            }
        };
        let a = make("a", "80008");
        let b = make("b", "90009");
        let a_path = a.socket.clone();
        let b_path = b.socket.clone();
        let (mut control, mut stop) = UnixStream::pair().unwrap();
        let (seen, events) = mpsc::channel();
        let worker = std::thread::spawn(move || {
            let fds = [control.as_raw_fd()];
            assert!(PrivateHttpEntrance::serve_dynamic_with_aux(vec![a,b],&fds,|event,_|match event {
                Ok((index,_,_,_))=>{seen.send(index).unwrap();Ok(Some(b"HTTP/1.1 200 OK\r\nContent-Length: 1\r\nConnection: close\r\n\r\nb".to_vec()))},
                Err(_)=>{let mut byte=[0];control.read_exact(&mut byte)?;Err(refuse("fixture complete"))},
            }).is_err());
        });
        let mut slow = UnixStream::connect(a_path).unwrap();
        slow.write_all(b"G").unwrap();
        let mut fast = UnixStream::connect(b_path).unwrap();
        fast.set_read_timeout(Some(Duration::from_secs(1))).unwrap();
        fast.write_all(b"GET / HTTP/1.1\r\nHost: friend.example.test\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\n\r\n").unwrap();
        assert_eq!(events.recv_timeout(Duration::from_secs(1)).unwrap(), 1);
        let mut response = String::new();
        fast.read_to_string(&mut response).unwrap();
        assert!(response.ends_with('b'));
        drop(slow);
        stop.write_all(&[1]).unwrap();
        worker.join().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn two_private_poll_channels_report_only_the_ready_participant() {
        let (mut a, mut a_writer) = UnixStream::pair().unwrap();
        let (mut b, mut b_writer) = UnixStream::pair().unwrap();
        let mut polls = [
            libc::pollfd {
                fd: a.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: b.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
        ];
        b_writer.write_all(b"b").unwrap();
        assert!(poll_entrances(&mut polls, 100).unwrap());
        assert_eq!(polls[0].revents & libc::POLLIN, 0);
        assert_ne!(polls[1].revents & libc::POLLIN, 0);
        let mut consumed = [0u8; 1];
        b.read_exact(&mut consumed).unwrap();
        for poll in &mut polls {
            poll.revents = 0;
        }
        a_writer.write_all(b"a").unwrap();
        assert!(poll_entrances(&mut polls, 100).unwrap());
        assert_ne!(polls[0].revents & libc::POLLIN, 0);
        assert_eq!(polls[1].revents & libc::POLLIN, 0);
        a.read_exact(&mut consumed).unwrap();
    }

    #[test]
    fn auxiliary_poll_routes_two_agents_by_stable_index() {
        let runtime = std::env::var("XDG_RUNTIME_DIR").unwrap();
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            Path::new(&runtime).join(format!("mini-spk-multipoll-{}-{nonce}", std::process::id()));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let socket = directory.join("http.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        let metadata = fs::symlink_metadata(&socket).unwrap();
        let entrance = PrivateHttpEntrance {
            listener,
            socket,
            socket_dev: metadata.dev(),
            socket_ino: metadata.ino(),
            _lock: File::create(directory.join(".lock")).unwrap(),
            policy: policy(),
        };
        let (agent_a, mut writer_a) = UnixStream::pair().unwrap();
        let (agent_b, mut writer_b) = UnixStream::pair().unwrap();
        let (seen_tx, seen_rx) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let mut agents = [agent_a, agent_b];
            let fds = [agents[0].as_raw_fd(), agents[1].as_raw_fd()];
            let mut count = 0;
            let result =
                PrivateHttpEntrance::serve_dynamic_with_aux(vec![entrance], &fds, |event, _| {
                    let index = event.err().ok_or_else(|| refuse("unexpected human poll"))?;
                    let mut byte = [0u8; 1];
                    agents[index].read_exact(&mut byte)?;
                    seen_tx.send(index).unwrap();
                    count += 1;
                    if count == 2 {
                        Err(refuse("poll fixture complete"))
                    } else {
                        Ok(None)
                    }
                });
            assert!(result.is_err());
        });
        writer_b.write_all(b"b").unwrap();
        assert_eq!(seen_rx.recv_timeout(Duration::from_secs(1)).unwrap(), 1);
        writer_a.write_all(b"a").unwrap();
        assert_eq!(seen_rx.recv_timeout(Duration::from_secs(1)).unwrap(), 0);
        worker.join().unwrap();
        fs::remove_file(directory.join(".lock")).unwrap();
        fs::remove_dir(directory).unwrap();
    }

    #[test]
    fn dynamic_poll_adds_route_without_closing_an_existing_upgraded_stream() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!("hot-poll-{}-{nonce}", std::process::id()));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let make = |name: &str, session: &str| {
            let directory = root.join(name);
            fs::DirBuilder::new()
                .mode(0o700)
                .create(&directory)
                .unwrap();
            let socket = directory.join("http.sock");
            let listener = UnixListener::bind(&socket).unwrap();
            let meta = fs::symlink_metadata(&socket).unwrap();
            let mut policy = policy();
            policy.fixed_session = session.into();
            PrivateHttpEntrance {
                listener,
                socket,
                socket_dev: meta.dev(),
                socket_ino: meta.ino(),
                _lock: File::create(directory.join(".lock")).unwrap(),
                policy,
            }
        };
        let a = make("a", "6208");
        let b = make("b", "6209");
        let a_path = a.socket.clone();
        let b_path = b.socket.clone();
        let (mut control, mut commands) = UnixStream::pair().unwrap();
        let (seen, events) = std::sync::mpsc::channel();
        let worker = std::thread::spawn(move || {
            let mut pending = Some(b);
            let mut active_a: Option<UnixStream> = None;
            let fds = [control.as_raw_fd()];
            let result = PrivateHttpEntrance::serve_dynamic_with_aux(
                vec![a],
                &fds,
                |event, routes| {
                    match event {
                        Err(0) => {
                            let mut command = [0];
                            control.read_exact(&mut command)?;
                            if command[0] == 2 {
                                return Err(refuse("fixture complete"));
                            }
                            routes.push(pending.take().unwrap());
                            // A remains a live accepted transport while B is added.
                            let stream = active_a.as_mut().unwrap();
                            let mut payload = [0; 4];
                            stream.read_exact(&mut payload)?;
                            stream.write_all(&payload)?;
                            seen.send(2).unwrap();
                            Ok(None)
                        }
                        Ok((index, mut request, _, _)) => {
                            if index == 0 {
                                let mut stream = request.upgrade_stream.take().unwrap();
                                stream.write_all(b"HTTP/1.1 101 Switching Protocols\r\n\r\n")?;
                                active_a = Some(stream);
                                seen.send(0).unwrap();
                                Ok(Some(Vec::new()))
                            } else {
                                seen.send(index).unwrap();
                                Ok(Some(b"HTTP/1.1 200 OK\r\nContent-Length: 1\r\nConnection: close\r\n\r\nb".to_vec()))
                            }
                        }
                        Err(_) => unreachable!(),
                    }
                },
            );
            assert!(result.is_err());
        });
        let mut client_a = UnixStream::connect(a_path).unwrap();
        client_a
            .set_read_timeout(Some(Duration::from_secs(2)))
            .unwrap();
        client_a.write_all(b"GET /live HTTP/1.1\r\nHost: friend.example.test\r\nOrigin: https://friend.example.test\r\nConnection: Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\n\r\n").unwrap();
        assert_eq!(events.recv_timeout(Duration::from_secs(2)).unwrap(), 0);
        let mut head = [0; 36];
        client_a.read_exact(&mut head).unwrap();
        assert_eq!(&head, b"HTTP/1.1 101 Switching Protocols\r\n\r\n");
        client_a.write_all(b"live").unwrap();
        commands.write_all(&[1]).unwrap();
        assert_eq!(events.recv_timeout(Duration::from_secs(2)).unwrap(), 2);
        let mut echo = [0; 4];
        client_a.read_exact(&mut echo).unwrap();
        assert_eq!(&echo, b"live");
        let mut client_b = UnixStream::connect(b_path).unwrap();
        client_b
            .set_read_timeout(Some(Duration::from_secs(2)))
            .unwrap();
        client_b.write_all(b"GET / HTTP/1.1\r\nHost: friend.example.test\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\n\r\n").unwrap();
        assert_eq!(events.recv_timeout(Duration::from_secs(2)).unwrap(), 1);
        let mut response = Vec::new();
        client_b.read_to_end(&mut response).unwrap();
        assert!(response.ends_with(b"\r\n\r\nb"));
        commands.write_all(&[2]).unwrap();
        worker.join().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    fn policy() -> CustodianPolicy {
        let hash = |value: &str| Sha256::digest(value.as_bytes()).into();
        CustodianPolicy {
            expected_host: "friend.example.test".into(),
            fixed_app: "6100".into(),
            fixed_subject: "8".into(),
            fixed_session: "6208".into(),
            fixed_session_kind: EntranceKind::Browser,
            export_capture: false,
            export_capture_path: None,
            fixed_ticket: "6408".into(),
            browser_token_sha256: hash("browser-token-abcdefghijklmnopqrstuvwxyz"),
            bootstrap_token_sha256: hash("bootstrap-token-abcdefghijklmnopqrstuvwxyz"),
            api_token_sha256: hash("api-token-abcdefghijklmnopqrstuvwxyz123"),
        }
    }

    fn api_policy() -> CustodianPolicy {
        CustodianPolicy {
            fixed_session_kind: EntranceKind::Api,
            ..policy()
        }
    }

    fn parsed(raw: &str) -> io::Result<ReceivedRequest> {
        let bytes = raw.as_bytes();
        let end = bytes
            .windows(4)
            .position(|part| part == b"\r\n\r\n")
            .unwrap();
        let (mut request, body_len) = parse_head(&bytes[..end])?;
        if bytes.len() != end + 4 + body_len {
            return Err(refuse("test frame body mismatch"));
        }
        request.body.extend_from_slice(&bytes[end + 4..]);
        Ok(request)
    }

    #[test]
    fn browser_unsafe_requires_same_origin_and_strips_session_cookie() {
        let raw = "POST /repo.git/git-receive-pack HTTP/1.1\r\nHost: friend.example.test\r\nOrigin: https://friend.example.test\r\nSec-Fetch-Site: same-origin\r\nCookie: theme=light; __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\nContent-Length: 3\r\nContent-Type: application/x-git-receive-pack-request\r\n\r\nabc";
        let mut request = parsed(raw).unwrap();
        assert_eq!(
            policy().authenticate(&mut request).unwrap(),
            EntranceKind::Browser
        );
        assert_eq!(request.path_and_query, "repo.git/git-receive-pack");
        assert_eq!(request.body, b"abc");
        assert_eq!(
            request
                .ordinary_headers
                .iter()
                .find(|(name, _)| name == "cookie")
                .unwrap()
                .1,
            "theme=light"
        );
        assert!(request.authorization.is_none() && request.cookie.is_none());
        let mut missing_origin =
            parsed(&raw.replace("Origin: https://friend.example.test\r\n", "")).unwrap();
        assert!(policy().authenticate(&mut missing_origin).is_err());
        let mut wrong_origin =
            parsed(&raw.replace("https://friend.example.test", "https://evil.example.test"))
                .unwrap();
        assert!(policy().authenticate(&mut wrong_origin).is_err());
        let mut cross_site =
            parsed(&raw.replace("Sec-Fetch-Site: same-origin", "Sec-Fetch-Site: cross-site"))
                .unwrap();
        assert!(policy().authenticate(&mut cross_site).is_err());
        let empty_write = "POST /gitweb.cgi HTTP/1.1\r\nHost: friend.example.test\r\nOrigin: https://friend.example.test\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\nContent-Length: 0\r\n\r\n";
        let mut request = parsed(empty_write).unwrap();
        assert_eq!(
            policy().authenticate(&mut request).unwrap(),
            EntranceKind::Browser
        );
        assert!(request.body.is_empty());
    }

    /// A browser WebSocket open is a streamed dispatch: an RFC 6455 GET
    /// becomes the `WEBSOCKET` method, its subprotocol list is signed, and the
    /// cookie route holds it to the same-origin rule of an unsafe method
    /// (cross-site WebSocket hijacking is refused before Mini).
    #[test]
    fn browser_websocket_open_is_a_streamed_same_origin_request() {
        let raw = "GET /socket.io/?EIO=3&transport=websocket HTTP/1.1\r\nHost: friend.example.test\r\nOrigin: https://friend.example.test\r\nSec-Fetch-Site: same-origin\r\nSec-Fetch-Mode: websocket\r\nConnection: keep-alive, Upgrade\r\nUpgrade: websocket\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\nSec-WebSocket-Protocol: chat\r\nSec-WebSocket-Extensions: permessage-deflate\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\n\r\n";
        let mut request = parsed(raw).unwrap();
        assert_eq!(request.method, Method::WebSocket);
        assert_eq!(request.method.as_str(), "WEBSOCKET");
        assert_eq!(
            request.websocket.as_ref().unwrap().accept,
            "s3pPLMBiTxaQ9kYGzzhZRbK+xOo="
        );
        assert_eq!(
            request.ordinary_headers,
            [("sec-websocket-protocol".to_owned(), "chat".to_owned())]
        );
        assert_eq!(
            policy().authenticate(&mut request).unwrap(),
            EntranceKind::Browser
        );
        let mut no_origin =
            parsed(&raw.replace("Origin: https://friend.example.test\r\n", "")).unwrap();
        assert!(policy().authenticate(&mut no_origin).is_err());
        let mut cross =
            parsed(&raw.replace("https://friend.example.test", "https://evil.example.test"))
                .unwrap();
        assert!(policy().authenticate(&mut cross).is_err());
        assert!(
            parsed(&raw.replace("Sec-WebSocket-Version: 13", "Sec-WebSocket-Version: 8")).is_err()
        );
        assert!(
            parsed(&raw.replace("Connection: keep-alive, Upgrade", "Connection: keep-alive"))
                .is_err()
        );
        assert!(parsed(&raw.replace("GET /socket.io", "POST /socket.io")).is_err());
        assert!(parsed(&raw.replace("Upgrade: websocket", "Upgrade: h2c")).is_err());
        let stray = "GET / HTTP/1.1\r\nHost: friend.example.test\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n\r\n";
        assert!(parsed(stray).is_err());
        let plain =
            parsed("GET / HTTP/1.1\r\nHost: friend.example.test\r\nConnection: keep-alive\r\n\r\n")
                .unwrap();
        assert_eq!(plain.method, Method::Get);
        assert!(plain.websocket.is_none());
    }

    #[test]
    fn direct_bookmark_navigation_is_safe_but_cross_site_and_unsafe_none_are_refused() {
        let raw = "GET /gitweb.cgi HTTP/1.1\r\nHost: friend.example.test\r\nSec-Fetch-Site: none\r\nSec-Fetch-Mode: navigate\r\nSec-Fetch-Dest: document\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\n\r\n";
        let mut request = parsed(raw).unwrap();
        assert_eq!(
            policy().authenticate(&mut request).unwrap(),
            EntranceKind::Browser
        );
        let mut cross_site =
            parsed(&raw.replace("Sec-Fetch-Site: none", "Sec-Fetch-Site: cross-site")).unwrap();
        assert!(policy().authenticate(&mut cross_site).is_err());
        let mut wrong_mode =
            parsed(&raw.replace("Sec-Fetch-Mode: navigate", "Sec-Fetch-Mode: cors")).unwrap();
        assert!(policy().authenticate(&mut wrong_mode).is_err());
        let unsafe_raw = raw.replace("GET /gitweb.cgi", "POST /gitweb.cgi");
        let mut unsafe_none = parsed(&unsafe_raw).unwrap();
        assert!(policy().authenticate(&mut unsafe_none).is_err());
    }

    #[test]
    fn api_bearer_is_separate_and_security_headers_never_reach_app() {
        let raw = "GET /repo.git/info/refs?service=git-upload-pack HTTP/1.1\r\nHost: friend.example.test\r\nAuthorization: Bearer api-token-abcdefghijklmnopqrstuvwxyz123\r\nContent-Length: 0\r\n\r\n";
        let mut request = parsed(raw).unwrap();
        assert_eq!(
            api_policy().authenticate(&mut request).unwrap(),
            EntranceKind::Api
        );
        assert!(request.ordinary_headers.is_empty());
        assert!(parsed(&raw.replace(
            "Content-Length: 0",
            "X-Sandstorm-Permissions: write\r\nContent-Length: 0"
        ))
        .is_err());
        assert!(parsed(&raw.replace(
            "Content-Length: 0",
            "Content-Length: 0\r\nContent-Length: 0"
        ))
        .is_err());
        assert!(parsed(&raw.replace(
            "Content-Length: 0",
            "Transfer-Encoding: chunked\r\nContent-Length: 0"
        ))
        .is_err());
        assert!(parsed(&raw.replace(
            "Content-Length: 0",
            "User-Agent: bad\u{7f}value\r\nContent-Length: 0"
        ))
        .is_err());
        assert!(parsed(&raw.replace("/repo.git/info/refs", "/repo.git/\tinfo/refs")).is_err());
        let mut both = parsed(&raw.replace("Content-Length: 0", "Cookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\nContent-Length: 0")).unwrap();
        assert!(api_policy().authenticate(&mut both).is_err());
        let mut wrong_kind = parsed(raw).unwrap();
        assert!(policy().authenticate(&mut wrong_kind).is_err());
    }

    #[test]
    fn transport_deadline_and_unavailable_response_do_not_deliver_app_call() {
        let (mut client, server) = UnixStream::pair().unwrap();
        client
            .write_all(b"GET /__mini/bootstrap HTTP/1.1\r\nHost: friend.example.test\r\n\r\n")
            .unwrap();
        let worker = std::thread::spawn(move || unavailable(server, &api_policy()).unwrap());
        let mut response = String::new();
        client.read_to_string(&mut response).unwrap();
        worker.join().unwrap();
        assert!(response.starts_with("HTTP/1.1 404 Not Found"));
        let (mut client, server) = UnixStream::pair().unwrap();
        client.write_all(b"GET / HTTP/1.1\r\nHost: friend.example.test\r\nAuthorization: Bearer api-token-abcdefghijklmnopqrstuvwxyz123\r\n\r\n").unwrap();
        let worker = std::thread::spawn(move || unavailable(server, &api_policy()).unwrap());
        let mut response = String::new();
        client.read_to_string(&mut response).unwrap();
        worker.join().unwrap();
        assert!(response.starts_with("HTTP/1.1 503 Service Unavailable"));
        assert!(response.ends_with("Mini dispatch admission unavailable\n"));
        let (mut client, server) = UnixStream::pair().unwrap();
        client.write_all(b"HEAD / HTTP/1.1\r\nHost: friend.example.test\r\nAuthorization: Bearer api-token-abcdefghijklmnopqrstuvwxyz123\r\n\r\n").unwrap();
        let worker = std::thread::spawn(move || unavailable(server, &api_policy()).unwrap());
        let mut response = String::new();
        client.read_to_string(&mut response).unwrap();
        worker.join().unwrap();
        assert!(response.ends_with("\r\n\r\n"));
        assert!(!response.contains("Mini dispatch admission unavailable\n"));
    }

    #[test]
    fn owner_private_socket_binds_one_fixed_custodian_and_refuses_second_instance() {
        let runtime = std::env::var("XDG_RUNTIME_DIR").unwrap();
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            Path::new(&runtime).join(format!("mini-spk-http-{}-{nonce}", std::process::id()));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let digest = |value: &str| format!("{:x}", Sha256::digest(value.as_bytes()));
        let config = serde_json::json!({
            "protocol": "mini-spk-custodian-v1",
            "expectedHost": "friend.example.test",
            "fixedApp": "6100",
            "fixedSubject": "8",
            "fixedSession": "6208",
            "fixedSessionKind": "web",
            "fixedTicket": "6408",
            "browserTokenSha256": digest("browser-token-abcdefghijklmnopqrstuvwxyz"),
            "bootstrapTokenSha256": digest("bootstrap-token-abcdefghijklmnopqrstuvwxyz"),
            "apiTokenSha256": digest("api-token-abcdefghijklmnopqrstuvwxyz123"),
        });
        let config_path = directory.join("custodian.json");
        fs::write(&config_path, serde_json::to_vec(&config).unwrap()).unwrap();
        fs::set_permissions(&config_path, fs::Permissions::from_mode(0o600)).unwrap();
        let entrance = PrivateHttpEntrance::bind(&directory).unwrap();
        assert!(PrivateHttpEntrance::bind(&directory).is_err());
        let mut client = UnixStream::connect(directory.join("http.sock")).unwrap();
        client.write_all(b"GET /gitweb.cgi HTTP/1.1\r\nHost: friend.example.test\r\nCookie: __Host-mini_spk_session=browser-token-abcdefghijklmnopqrstuvwxyz\r\n\r\n").unwrap();
        let server = std::thread::spawn(move || {
            let (peer, _) = entrance.listener.accept().unwrap();
            assert_eq!(peer_uid(&peer), Some(unsafe { libc::geteuid() }));
            unavailable(peer, &entrance.policy).unwrap();
            entrance
        });
        let mut response = String::new();
        client.read_to_string(&mut response).unwrap();
        assert!(response.starts_with("HTTP/1.1 503 Service Unavailable"));
        drop(server.join().unwrap());
        assert!(!directory.join("http.sock").exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn incomplete_http_frame_expires_on_one_absolute_deadline() {
        let (mut client, mut server) = UnixStream::pair().unwrap();
        client
            .write_all(b"POST /repo.git/git-receive-pack HTTP/1.1\r\nHost: friend.example.test\r\n")
            .unwrap();
        let start = Instant::now();
        let error = read_request_until(&mut server, start + Duration::from_millis(30)).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::TimedOut);
        assert!(start.elapsed() < Duration::from_secs(1));
    }

    #[test]
    fn exact_owned_refused_socket_rebinds_after_stopped_listener() {
        let runtime = std::env::var("XDG_RUNTIME_DIR").unwrap();
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            Path::new(&runtime).join(format!("mini-spk-stale-{}-{nonce}", std::process::id()));
        initialize_custodian(
            &directory,
            "friend-a.localhost:18443",
            "6100",
            "8",
            "6208",
            "6408",
            "web",
        )
        .unwrap();
        let socket = directory.join("http.sock");
        let stale = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        let old = fs::symlink_metadata(&socket).unwrap();
        drop(stale);
        let entrance = PrivateHttpEntrance::bind(&directory).unwrap();
        let new = fs::symlink_metadata(&socket).unwrap();
        assert_ne!(old.ino(), new.ino());
        assert!(UnixStream::connect(&socket).is_ok());
        assert!(PrivateHttpEntrance::bind(&directory).is_err());
        assert_eq!(fs::symlink_metadata(&socket).unwrap().ino(), new.ino());
        drop(entrance);
        assert!(!socket.exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn private_bootstrap_sets_host_cookie_once_without_url_secret() {
        let runtime = std::env::var("XDG_RUNTIME_DIR").unwrap();
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            Path::new(&runtime).join(format!("mini-spk-bootstrap-{}-{nonce}", std::process::id()));
        initialize_custodian(
            &directory,
            "friend-a.localhost:18443",
            "6100",
            "8",
            "6208",
            "6408",
            "web",
        )
        .unwrap();
        assert!(initialize_custodian(
            &directory,
            "friend-a.localhost:18443",
            "6100",
            "8",
            "6208",
            "6408",
            "web"
        )
        .is_err());
        let token = fs::read_to_string(directory.join("bootstrap.token")).unwrap();
        let config = fs::read_to_string(directory.join("custodian.json")).unwrap();
        assert_eq!(token.len(), 64);
        assert!(!config.contains(&token));
        let policy = CustodianPolicy::load(&directory).unwrap();
        let (mut client, server) = UnixStream::pair().unwrap();
        client.write_all(b"GET /__mini/bootstrap HTTP/1.1\r\nHost: friend-a.localhost:18443\r\nSec-Fetch-Site: none\r\n\r\n").unwrap();
        let worker = std::thread::spawn({
            let directory = directory.clone();
            let policy = policy.clone();
            move || handle_stream(server, &policy, Some(&directory)).unwrap()
        });
        let mut form = String::new();
        client.read_to_string(&mut form).unwrap();
        worker.join().unwrap();
        assert!(form.starts_with("HTTP/1.1 200 OK"));
        assert!(form.contains("action=\"/__mini/bootstrap\""));
        assert!(!form.contains(&token));
        let posted = format!("token={token}");
        let request = format!("POST /__mini/bootstrap HTTP/1.1\r\nHost: friend-a.localhost:18443\r\nOrigin: https://friend-a.localhost:18443\r\nSec-Fetch-Site: same-origin\r\nContent-Type: application/x-www-form-urlencoded\r\nContent-Length: {}\r\n\r\n{posted}", posted.len());
        let (mut client, server) = UnixStream::pair().unwrap();
        client.write_all(request.as_bytes()).unwrap();
        let worker = std::thread::spawn({
            let directory = directory.clone();
            let policy = policy.clone();
            move || handle_stream(server, &policy, Some(&directory)).unwrap()
        });
        let mut response = String::new();
        client.read_to_string(&mut response).unwrap();
        worker.join().unwrap();
        assert!(response.starts_with("HTTP/1.1 303 See Other\r\nLocation: /\r\n"));
        assert!(response.contains("; Secure; HttpOnly; SameSite=Strict; Path=/"));
        assert!(!response.contains(&token));
        assert!(directory.join("bootstrap.used").exists());
        let (mut client, server) = UnixStream::pair().unwrap();
        client.write_all(request.as_bytes()).unwrap();
        let worker = std::thread::spawn({
            let directory = directory.clone();
            move || handle_stream(server, &policy, Some(&directory)).unwrap()
        });
        let mut replay = String::new();
        client.read_to_string(&mut replay).unwrap();
        worker.join().unwrap();
        assert!(replay.starts_with("HTTP/1.1 403 Forbidden"));
        assert!(!replay.contains("Set-Cookie"));
        fs::remove_dir_all(directory).unwrap();
    }
}
