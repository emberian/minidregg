//! Fixed public paid-entry operations behind the deployment's TLS reverse proxy.
//! No authority is accepted from HTTP: source admission and pricing stay in Host.
//! V1 retains its explicitly bounded legacy scan. V2 status uses exact source keys;
//! claim routes carry only closed signed source commands and exact lookups.
use super::{host_image_sha256, path, Args, Result, SOCKET};
use crate::transport;
use serde_json::{json, Value};
use std::collections::{HashMap, VecDeque};
use std::io::{Read, Write};
use std::net::{IpAddr, SocketAddr, TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

const MAX_HEAD: usize = 8192;
const MAX_BODY: usize = 4096;
const MAX_RESPONSE: usize = 16 * 1024;
const WORKERS: usize = 4;
const QUEUED: usize = 8;
const HOST_WORK: usize = 2;
// Legacy op112 serializes the whole public view. Only one such poll may hold
// Host capacity, leaving the other permit for a quote. Replace this scan with
// a source-owned exact key/signature read when that operation is available.
const STATUS_WORK: usize = 1;
const MAX_STATUS_VIEW: usize = 2 * 1024 * 1024;
const MAX_STATUS_JSON: usize = 4 * 1024 * 1024;
const POLL_SECONDS: u64 = 5;
const REQUEST_TIME: Duration = Duration::from_secs(5);
const MAX_RATE_CLIENTS: usize = 1024;

#[derive(Debug, PartialEq)]
struct HttpError(u16, &'static str);
type HttpResult<T> = std::result::Result<T, HttpError>;
#[derive(Debug)]
struct Request {
    method: String,
    target: String,
    headers: HashMap<String, String>,
    body: Vec<u8>,
}
struct Response {
    status: u16,
    body: Value,
}
impl Response {
    fn error(error: HttpError) -> Self {
        Self {
            status: error.0,
            body: json!({"error":error.1}),
        }
    }
    fn ok(body: Value) -> Self {
        Self { status: 200, body }
    }
}
fn os_string(value: std::ffi::OsString, label: &str) -> Result<String> {
    value
        .into_string()
        .map_err(|_| format!("{label} must be UTF-8"))
}
fn remaining(deadline: Instant) -> std::io::Result<Duration> {
    let left = deadline.saturating_duration_since(Instant::now());
    if left.is_zero() {
        Err(std::io::Error::new(
            std::io::ErrorKind::TimedOut,
            "request deadline",
        ))
    } else {
        Ok(left)
    }
}
fn token(value: &str) -> bool {
    !value.is_empty()
        && value
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || b"!#$%&'*+-.^_|~".contains(&c) || c == 96)
}
fn parse_head(bytes: &[u8]) -> HttpResult<(Request, usize)> {
    if bytes.len() > MAX_HEAD {
        return Err(HttpError(431, "headersTooLarge"));
    }
    let text = std::str::from_utf8(bytes).map_err(|_| HttpError(400, "invalidHeaders"))?;
    let head = text
        .strip_suffix("\r\n\r\n")
        .ok_or(HttpError(400, "invalidHeaders"))?;
    let mut lines = head.split("\r\n");
    let words: Vec<_> = lines.next().unwrap_or("").split(' ').collect();
    if words.len() != 3
        || !token(words[0])
        || words[2] != "HTTP/1.1"
        || !words[1].starts_with('/')
        || words[1].len() > 256
        || !words[1].bytes().all(|c| (33..=126).contains(&c))
    {
        return Err(HttpError(400, "invalidRequestLine"));
    }
    let mut headers = HashMap::new();
    for line in lines {
        let (name, value) = line
            .split_once(':')
            .ok_or(HttpError(400, "invalidHeader"))?;
        if !token(name) || !value.bytes().all(|c| c == b'\t' || (32..=126).contains(&c)) {
            return Err(HttpError(400, "invalidHeader"));
        }
        if headers.len() >= 32 {
            return Err(HttpError(431, "tooManyHeaders"));
        }
        if headers
            .insert(name.to_ascii_lowercase(), value.trim().to_owned())
            .is_some()
        {
            return Err(HttpError(400, "duplicateHeader"));
        }
    }
    if headers.get("host").is_none_or(|v| v.is_empty()) {
        return Err(HttpError(400, "missingHost"));
    }
    if headers.contains_key("transfer-encoding") {
        return Err(HttpError(400, "unsupportedFraming"));
    }
    if headers.contains_key("expect") {
        return Err(HttpError(417, "unsupportedExpectation"));
    }
    let length = match headers.get("content-length") {
        Some(value) => {
            if value.is_empty() || !value.bytes().all(|c| c.is_ascii_digit()) {
                return Err(HttpError(400, "invalidContentLength"));
            }
            value
                .parse::<usize>()
                .map_err(|_| HttpError(413, "bodyTooLarge"))?
        }
        None if words[0] == "POST" => return Err(HttpError(411, "contentLengthRequired")),
        None => 0,
    };
    if length > MAX_BODY {
        return Err(HttpError(413, "bodyTooLarge"));
    }
    if words[0] != "POST" && length != 0 {
        return Err(HttpError(400, "unexpectedBody"));
    }
    Ok((
        Request {
            method: words[0].to_owned(),
            target: words[1].to_owned(),
            headers,
            body: Vec::new(),
        },
        length,
    ))
}
fn read_request(stream: &mut TcpStream, deadline: Instant) -> HttpResult<Request> {
    let mut bytes = Vec::new();
    let mut chunk = [0u8; 1024];
    let end = loop {
        if let Some(at) = bytes.windows(4).position(|w| w == b"\r\n\r\n") {
            break at + 4;
        }
        if bytes.len() >= MAX_HEAD {
            return Err(HttpError(431, "headersTooLarge"));
        }
        stream
            .set_read_timeout(Some(
                remaining(deadline).map_err(|_| HttpError(408, "readTimeout"))?,
            ))
            .map_err(|_| HttpError(400, "readFailed"))?;
        let count = stream
            .read(&mut chunk)
            .map_err(|_| HttpError(408, "readTimeout"))?;
        if count == 0 {
            return Err(HttpError(400, "incompleteRequest"));
        }
        bytes.extend_from_slice(&chunk[..count]);
    };
    let (mut request, length) = parse_head(&bytes[..end])?;
    request.body.extend_from_slice(&bytes[end..]);
    while request.body.len() < length {
        stream
            .set_read_timeout(Some(
                remaining(deadline).map_err(|_| HttpError(408, "readTimeout"))?,
            ))
            .map_err(|_| HttpError(400, "readFailed"))?;
        let count = stream
            .read(&mut chunk)
            .map_err(|_| HttpError(408, "readTimeout"))?;
        if count == 0 {
            return Err(HttpError(400, "incompleteBody"));
        }
        request.body.extend_from_slice(&chunk[..count]);
    }
    if request.body.len() != length {
        return Err(HttpError(400, "extraRequestBytes"));
    }
    // One request per connection. Reject already-buffered pipelining too.
    stream
        .set_nonblocking(true)
        .map_err(|_| HttpError(400, "readFailed"))?;
    let extra = stream.peek(&mut chunk[..1]);
    stream
        .set_nonblocking(false)
        .map_err(|_| HttpError(400, "readFailed"))?;
    match extra {
        Ok(count) if count > 0 => return Err(HttpError(400, "extraRequestBytes")),
        Err(error) if error.kind() != std::io::ErrorKind::WouldBlock => {
            return Err(HttpError(400, "readFailed"))
        }
        _ => {}
    }
    Ok(request)
}
fn write_response(stream: &mut TcpStream, response: Response, deadline: Instant) {
    let (status, body) = match serde_json::to_vec(&response.body) {
        Ok(body) if body.len() <= MAX_RESPONSE => (response.status, body),
        _ => (503, br#"{"error":"responseTooLarge"}"#.to_vec()),
    };
    let reason = match status {
        200 => "OK",
        400 => "Bad Request",
        404 => "Not Found",
        405 => "Method Not Allowed",
        408 => "Request Timeout",
        411 => "Length Required",
        413 => "Content Too Large",
        415 => "Unsupported Media Type",
        417 => "Expectation Failed",
        422 => "Unprocessable Content",
        429 => "Too Many Requests",
        431 => "Request Header Fields Too Large",
        _ => "Service Unavailable",
    };
    let retry = if status == 429 || status == 503 {
        "Retry-After: 10\r\n"
    } else {
        ""
    };
    let head = format!("HTTP/1.1 {status} {reason}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nCache-Control: no-store\r\nX-Content-Type-Options: nosniff\r\nConnection: close\r\n{retry}\r\n", body.len());
    let mut output = head.into_bytes();
    output.extend_from_slice(&body);
    let mut written = 0;
    while written < output.len() {
        let Ok(left) = remaining(deadline) else {
            return;
        };
        if stream.set_write_timeout(Some(left)).is_err() {
            return;
        }
        match stream.write(&output[written..]) {
            Ok(0) | Err(_) => return,
            Ok(count) => written += count,
        }
    }
}
fn lower_hex(value: &str, size: usize) -> bool {
    value.len() == size
        && mini_sdk::hex::is_lower(value)
}
fn decimal(value: &Value, positive: bool) -> bool {
    value.as_str().is_some_and(|s| {
        !s.is_empty()
            && s.len() <= 20
            && s.bytes().all(|c| c.is_ascii_digit())
            && (s.len() == 1 || !s.starts_with('0'))
            && s.parse::<u64>().is_ok_and(|n| !positive || n > 0)
    })
}
fn quote_body(body: &[u8]) -> HttpResult<Vec<u8>> {
    let value: Value = serde_json::from_slice(body).map_err(|_| HttpError(400, "invalidQuote"))?;
    let object = value.as_object().ok_or(HttpError(400, "invalidQuote"))?;
    if object.len() != 4
        || !object
            .keys()
            .all(|k| matches!(k.as_str(), "miniKey" | "mode" | "weeks" | "starterCredit"))
        || !value["miniKey"].as_str().is_some_and(|s| lower_hex(s, 64))
        || !matches!(value["mode"].as_str(), Some("enrol" | "renew"))
        || !decimal(&value["weeks"], true)
        || !(value["starterCredit"].is_null() || decimal(&value["starterCredit"], false))
    {
        return Err(HttpError(400, "invalidQuote"));
    }
    serde_json::to_vec(&value).map_err(|_| HttpError(400, "invalidQuote"))
}
// Closed route table; no operation number or command name comes from HTTP.
fn paid_route(target:&str)->Option<(HostRead,bool,&'static str)> {
    Some(match target {
        "/mini/v2/status" => (HostRead::PaidStatus,true,""),
        "/mini/v2/quote" => (HostRead::PaidQuote,true,""),
        "/mini/v2/claim/plan" => (HostRead::ClaimPlan,false,"canonicalPlan"),
        "/mini/v2/claim/assemble" => (HostRead::ClaimAssemble,false,"canonicalIngress"),
        "/mini/v2/claim/submit" => (HostRead::ClaimSubmit,false,"canonicalOutcome"),
        "/mini/v2/claim/lookup" => (HostRead::ClaimLookup,false,"canonicalOutcome"),
        _ => return None,
    })
}
fn paid_body(operation:HostRead,body:&[u8])->HttpResult<&[u8]> {
    if body.is_empty() || body.len()>4096 { return Err(HttpError(400,"invalidPaidBody")); }
    let request=[vec![operation as u8],body.to_vec()].concat();
    if !transport::allowed_operation(&request, false) { return Err(HttpError(400,"invalidPaidBody")); }
    Ok(body)
}
fn https_url(value: &Value) -> bool {
    value.as_str().is_some_and(|s| {
        let Some(rest) = s.strip_prefix("https://") else {
            return false;
        };
        !rest.is_empty()
            && !rest.starts_with('/')
            && s.len() <= 2048
            && s.bytes()
                .all(|c| (33..=126).contains(&c) && !b"@#\\".contains(&c))
    })
}
fn metadata(configured: Value, profile: &Value, sha: &str) -> Result<Value> {
    let object = configured
        .as_object()
        .ok_or("metadata must be a JSON object")?;
    if !object.keys().all(|k| {
        matches!(
            k.as_str(),
            "sshLogin" | "clientBundleUrl" | "clientBundleSha256" | "birthContextUrl"
        )
    }) {
        return Err("metadata contains a field outside the public whitelist".into());
    }
    let login = configured["sshLogin"]
        .as_str()
        .ok_or("metadata sshLogin missing")?;
    transport::remote_destination(login)?;
    if !https_url(&configured["clientBundleUrl"])
        || !configured["clientBundleSha256"]
            .as_str()
            .is_some_and(|s| lower_hex(s, 64))
        || object.get("birthContextUrl").is_some_and(|v| !https_url(v))
    {
        return Err("metadata requires HTTPS bundle URLs and a lowercase SHA-256".into());
    }
    let mut result = configured;
    for field in ["domain", "semantics"] {
        let value = profile[field]
            .as_str()
            .filter(|s| !s.is_empty() && s.len() <= 80 && s.bytes().all(|c| c.is_ascii_digit()))
            .ok_or("invalid public profile identity")?;
        result[field] = json!(value);
    }
    result["type"] = json!("minidregg-enrollment-bootstrap-v1");
    result["hostSha256"] = json!(sha);
    result["memoVersions"] = json!(["enrol:v1"]);
    result["quoteType"] = json!("minidregg-pay-enrollment-quote-v1");
    result["priceReserved"] = json!(false);
    result["pollAfterSeconds"] = json!(POLL_SECONDS);
    result["limits"] = json!({"quoteBodyBytes":MAX_BODY,"quotesPerMinute":QUOTE_RATE.per_minute,
        "statusPerMinute":STATUS_RATE.per_minute,"statusConcurrency":STATUS_WORK,
        "hostConcurrency":HOST_WORK,"statusViewBytes":MAX_STATUS_VIEW,
        "statusDecodedBytes":MAX_STATUS_JSON});
    Ok(result)
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum HostRead {
    PaidStatus = 181,
    PaidQuote = 182,
    ClaimPlan = 183,
    ClaimAssemble = 184,
    ClaimSubmit = 185,
    ClaimLookup = 186,
    Profile = 6,
    Quote = 121,
    Enrollment = 112,
    InspectEnrollment = 8,
}
trait Dispatch: Send + Sync {
    fn call(&self, operation: HostRead, payload: &[u8], deadline: Instant) -> Result<Vec<u8>>;
}
struct PinnedHost {
    socket: PathBuf,
    config: PathBuf,
    sha: String,
}
impl Dispatch for PinnedHost {
    fn call(&self, operation: HostRead, payload: &[u8], deadline: Instant) -> Result<Vec<u8>> {
        transport::invoke_pinned_deadline(
            &self.socket,
            &self.config,
            &self.sha,
            operation as u8,
            payload,
            deadline,
        )
    }
}
fn host_call(
    host: &dyn Dispatch,
    operation: HostRead,
    payload: &[u8],
    deadline: Instant,
) -> HttpResult<Vec<u8>> {
    remaining(deadline).map_err(|_| HttpError(503, "hostTimeout"))?;
    let response = host
        .call(operation, payload, deadline)
        .map_err(|_| HttpError(503, "hostUnavailable"))?;
    if response.first() == Some(&255) {
        return Err(HttpError(422, "hostRefused"));
    }
    if response.first() != Some(&(operation as u8)) {
        return Err(HttpError(503, "invalidHostResponse"));
    }
    Ok(response[1..].to_vec())
}
fn host_json(
    host: &dyn Dispatch,
    operation: HostRead,
    payload: &[u8],
    deadline: Instant,
) -> HttpResult<Value> {
    let body = host_call(host, operation, payload, deadline)?;
    serde_json::from_slice(&body).map_err(|_| HttpError(503, "invalidHostResponse"))
}
fn enrollment(
    host: &dyn Dispatch,
    key: &str,
    signature: Option<&str>,
    deadline: Instant,
) -> HttpResult<Value> {
    let view = host_call(host, HostRead::Enrollment, b"", deadline)?;
    if view.len() > MAX_STATUS_VIEW {
        return Err(HttpError(503, "statusViewTooLarge"));
    }
    let kind = b"pay-enrolment-view";
    let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind);
    payload.extend_from_slice(&view);
    let decoded = host_call(host, HostRead::InspectEnrollment, &payload, deadline)?;
    if decoded.len() > MAX_STATUS_JSON {
        return Err(HttpError(503, "statusViewTooLarge"));
    }
    let decoded: Value =
        serde_json::from_slice(&decoded).map_err(|_| HttpError(503, "invalidEnrollmentView"))?;
    if decoded["view"] != "DREGG/PAY/ENROLMENT-VIEW/v3" {
        return Err(HttpError(503, "invalidEnrollmentView"));
    }
    let entries = decoded["entries"]
        .as_array()
        .ok_or(HttpError(503, "invalidEnrollmentView"))?;
    let mut matched = entries
        .iter()
        .filter(|entry| entry["miniKey"].as_str() == Some(key));
    let entry = matched.next().map(|row| {
        json!({
            "miniKey":row["miniKey"], "sshBlob":row["sshBlob"], "subject":row["subject"],
            "index":row["index"], "lease":row["lease"]
        })
    });
    if matched.next().is_some() {
        return Err(HttpError(503, "invalidEnrollmentView"));
    }
    // Presentation of the source's lease interval, not a new admission rule.
    // Keep an expired entry visible so renewal can retain its stable identity.
    let hour = decoded["clock"]["hour"]
        .as_u64()
        .ok_or(HttpError(503, "invalidEnrollmentView"))?;
    let state = match entry.as_ref() {
        None => "notObserved",
        Some(row) if row["lease"].is_null() => "noLease",
        Some(row) => {
            let expires = row["lease"]["expiresAt"]
                .as_u64()
                .ok_or(HttpError(503, "invalidEnrollmentView"))?;
            if hour < expires {
                "enrolled"
            } else {
                "expired"
            }
        }
    };
    let decision = if let Some(signature) = signature {
        let rows = decoded["journal"]
            .as_array()
            .ok_or(HttpError(503, "invalidEnrollmentView"))?;
        let mut matched = rows
            .iter()
            .filter(|row| row["signature"].as_str() == Some(signature));
        let decision = matched.next().cloned();
        if matched.next().is_some() {
            return Err(HttpError(503, "invalidEnrollmentView"));
        }
        decision
    } else {
        None
    };
    Ok(
        json!({"type":"minidregg-enrollment-status-v1","miniKey":key,
        "state":state,
        "entry":entry,"clock":{"hour":decoded["clock"]["hour"]},
        "pollAfterSeconds":POLL_SECONDS,"paymentDecision":decision}),
    )
}
#[derive(Clone, Copy)]
struct RatePolicy {
    per_minute: usize,
    burst: usize,
    burst_window: Duration,
}
// One quote + plan + assembly + submission must fit one normal flow.
// The total per-minute and shared Host concurrency budgets remain unchanged.
const QUOTE_RATE: RatePolicy = RatePolicy {
    per_minute: 6,
    burst: 4,
    burst_window: Duration::from_secs(10),
};
const STATUS_RATE: RatePolicy = RatePolicy {
    per_minute: 12,
    burst: 2,
    burst_window: Duration::from_secs(POLL_SECONDS),
};
/// What one rate budget belongs to. An IPv6 site is routinely delegated a
/// whole /64, so one holder can spray 2^64 source addresses; the budget is
/// per /64. IPv4 (including v4-mapped IPv6) stays per address.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum RateKey {
    V4(u32),
    V6Prefix64(u64),
}
fn rate_key(ip: IpAddr) -> RateKey {
    match ip {
        IpAddr::V4(v4) => RateKey::V4(u32::from(v4)),
        IpAddr::V6(v6) => match v6.to_ipv4_mapped() {
            Some(v4) => RateKey::V4(u32::from(v4)),
            None => RateKey::V6Prefix64((u128::from(v6) >> 64) as u64),
        },
    }
}
#[derive(Default)]
struct RateLimit {
    clients: HashMap<RateKey, VecDeque<Instant>>,
}
impl RateLimit {
    fn allow(&mut self, ip: IpAddr, now: Instant, policy: RatePolicy) -> bool {
        let key = rate_key(ip);
        self.clients.retain(|_, times| {
            while times
                .front()
                .is_some_and(|time| now.duration_since(*time) >= Duration::from_secs(60))
            {
                times.pop_front();
            }
            !times.is_empty()
        });
        // A full table evicts the least recently active budget instead of
        // refusing every newcomer: a full table must not lock out a fresh
        // client. An evicted holder restarts with an empty budget, which is
        // what any new key already gets, so eviction adds no admission rate
        // beyond the number of keys a holder controls.
        if !self.clients.contains_key(&key) && self.clients.len() >= MAX_RATE_CLIENTS {
            let oldest = self
                .clients
                .iter()
                .min_by_key(|(_, times)| times.back().copied())
                .map(|(key, _)| *key);
            if let Some(oldest) = oldest {
                self.clients.remove(&oldest);
            }
        }
        let times = self.clients.entry(key).or_default();
        if times.len() >= policy.per_minute
            || times
                .iter()
                .filter(|time| now.duration_since(**time) < policy.burst_window)
                .count()
                >= policy.burst
        {
            return false;
        }
        times.push_back(now);
        true
    }
}
struct Permit<'a>(&'a AtomicUsize);
impl Drop for Permit<'_> {
    fn drop(&mut self) {
        self.0.fetch_sub(1, Ordering::AcqRel);
    }
}
fn permit(counter: &AtomicUsize, capacity: usize) -> HttpResult<Permit<'_>> {
    counter
        .fetch_update(Ordering::AcqRel, Ordering::Acquire, |n| {
            (n < capacity).then_some(n + 1)
        })
        .map(|_| Permit(counter))
        .map_err(|_| HttpError(503, "hostBusy"))
}
struct App {
    metadata: Value,
    host: Arc<dyn Dispatch>,
    trusted_proxy: Option<IpAddr>,
    rates: Mutex<RateLimit>,
    status_rates: Mutex<RateLimit>,
    live: AtomicUsize,
    status_live: AtomicUsize,
}
impl App {
    fn handle(&self, request: Request, peer: IpAddr, deadline: Instant) -> Response {
        match self.handle_inner(request, peer, deadline) {
            Ok(body) => Response::ok(body),
            Err(error) => Response::error(error),
        }
    }
    fn client(&self, request: &Request, peer: IpAddr) -> HttpResult<IpAddr> {
        if self.trusted_proxy == Some(peer) {
            request
                .headers
                .get("x-real-ip")
                .and_then(|s| s.parse().ok())
                .ok_or(HttpError(400, "missingClientAddress"))
        } else {
            Ok(peer)
        }
    }
    fn handle_inner(&self, request: Request, peer: IpAddr, deadline: Instant) -> HttpResult<Value> {
        if request.target == "/mini/v2/metadata" {
            if request.method != "GET" { return Err(HttpError(405, "methodNotAllowed")); }
            let mut metadata = self.metadata.clone();
            metadata["type"] = json!("minidregg-enrollment-bootstrap-v2");
            metadata["memoVersions"] = json!(["enrol:v2"]);
            metadata["quoteType"] = json!("payQuote");
            metadata["statusType"] = json!("payStatus");
            metadata["expiryClock"] = json!("processingChainHour");
            metadata["recovery"] = json!("acceptCurrentQuote");
            metadata["limits"]["sourceJsonResponseBytes"] = json!(8192);
            return Ok(metadata);
        }
        if let Some((operation, json_input, output_field)) = paid_route(&request.target) {
            if request.method != "POST" { return Err(HttpError(405, "methodNotAllowed")); }
            let expected_content_type = if json_input { "application/json" } else { "application/octet-stream" };
            if request.headers.get("content-type").map(String::as_str) != Some(expected_content_type) {
                return Err(HttpError(415, "invalidContentType"));
            }
            // Preserve original JSON bytes: the source duplicate-key parser must
            // see duplicates rather than a serde-normalized last-key-wins value.
            let payload = paid_body(operation, &request.body)?;
            let client = self.client(&request, peer)?;
            let status = operation == HostRead::PaidStatus || operation == HostRead::ClaimLookup;
            let allowed = if status {
                self.status_rates.lock().map_err(|_|HttpError(503,"unavailable"))?
                    .allow(client,Instant::now(),STATUS_RATE)
            } else {
                self.rates.lock().map_err(|_|HttpError(503,"unavailable"))?
                    .allow(client,Instant::now(),QUOTE_RATE)
            };
            if !allowed { return Err(HttpError(429,"paidRateLimited")); }
            let _status = if status { Some(permit(&self.status_live,STATUS_WORK)?) } else { None };
            let _host = permit(&self.live,HOST_WORK)?;
            let bytes = host_call(&*self.host,operation,payload,deadline)?;
            if json_input {
                if bytes.len() > 8192 { return Err(HttpError(503,"sourceResponseTooLarge")); }
                let result:Value=serde_json::from_slice(&bytes).map_err(|_|HttpError(503,"invalidHostResponse"))?;
                if operation==HostRead::PaidStatus {
                    let requested:Value=serde_json::from_slice(&request.body).map_err(|_|HttpError(503,"invalidHostResponse"))?;
                    return crate::pay_status::parse(&result,&requested).map(|v|v.raw).map_err(|_|HttpError(503,"invalidHostResponse"));
                }
                let expected = "payQuote";
                if result["type"] != expected || (operation==HostRead::PaidQuote && result["priceReserved"] != false) {
                    return Err(HttpError(503,"invalidHostResponse"));
                }
                return Ok(result);
            }
            if bytes.len() > 4096 { return Err(HttpError(503,"sourceResponseTooLarge")); }
            return Ok(json!({"type":"payClaimWire","operation":(operation as u8).to_string(),
                (output_field):super::hex(&bytes)}));
        }
        if request.target == "/mini/v1/metadata" {
            if request.method != "GET" {
                return Err(HttpError(405, "methodNotAllowed"));
            }
            return Ok(self.metadata.clone());
        }
        if request.target == "/mini/v1/quote" {
            if request.method != "POST" {
                return Err(HttpError(405, "methodNotAllowed"));
            }
            if request.headers.get("content-type").map(String::as_str) != Some("application/json") {
                return Err(HttpError(415, "jsonRequired"));
            }
            let payload = quote_body(&request.body)?;
            let client = self.client(&request, peer)?;
            if !self
                .rates
                .lock()
                .map_err(|_| HttpError(503, "unavailable"))?
                .allow(client, Instant::now(), QUOTE_RATE)
            {
                return Err(HttpError(429, "quoteRateLimited"));
            }
            let _permit = permit(&self.live, HOST_WORK)?;
            let quote = host_json(&*self.host, HostRead::Quote, &payload, deadline)?;
            if quote["type"] != "minidregg-pay-enrollment-quote-v1"
                || quote["priceReserved"] != false
            {
                return Err(HttpError(503, "invalidQuoteResponse"));
            }
            return Ok(quote);
        }
        if let Some(tail) = request.target.strip_prefix("/mini/v1/enrollment/") {
            if request.method != "GET" {
                return Err(HttpError(405, "methodNotAllowed"));
            }
            let (key, signature) = if let Some((key, query)) = tail.split_once('?') {
                let signature = query
                    .strip_prefix("signature=")
                    .filter(|s| lower_hex(s, 128))
                    .ok_or(HttpError(400, "invalidSignatureQuery"))?;
                (key, Some(signature))
            } else {
                (tail, None)
            };
            if !lower_hex(key, 64) {
                return Err(HttpError(400, "invalidMiniKey"));
            }
            let client = self.client(&request, peer)?;
            if !self
                .status_rates
                .lock()
                .map_err(|_| HttpError(503, "unavailable"))?
                .allow(client, Instant::now(), STATUS_RATE)
            {
                return Err(HttpError(429, "statusRateLimited"));
            }
            let _status =
                permit(&self.status_live, STATUS_WORK).map_err(|_| HttpError(503, "statusBusy"))?;
            let _permit = permit(&self.live, HOST_WORK)?;
            return enrollment(&*self.host, key, signature, deadline);
        }
        Err(HttpError(404, "notFound"))
    }
}
fn workers<T: Send + 'static>(
    receiver: mpsc::Receiver<T>,
    handler: Arc<dyn Fn(T) + Send + Sync>,
) -> Vec<thread::JoinHandle<()>> {
    let receiver = Arc::new(Mutex::new(receiver));
    (0..WORKERS)
        .map(|_| {
            let receiver = Arc::clone(&receiver);
            let handler = Arc::clone(&handler);
            thread::spawn(move || loop {
                let received = match receiver.lock() {
                    Ok(rx) => rx.recv(),
                    Err(_) => return,
                };
                match received {
                    Ok(job) => handler(job),
                    Err(_) => return,
                }
            })
        })
        .collect()
}
fn private_listener(address: IpAddr) -> bool {
    match address {
        IpAddr::V4(ip) => ip.is_loopback() || ip.is_private(),
        IpAddr::V6(ip) => ip.is_loopback() || ip.segments()[0] & 0xfe00 == 0xfc00,
    }
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let check = match args.optional("check") {
        None => false,
        Some(v) if v == "true" => true,
        Some(v) if v == "false" => false,
        Some(_) => return Err("--check must be true or false".into()),
    };
    let host = path(args.required("host")?);
    let config = path(args.required("config")?);
    let listen: SocketAddr = os_string(args.required("listen")?, "listen")?
        .parse()
        .map_err(|_| "listen must be a literal IP:PORT")?;
    let metadata_path = path(args.required("metadata")?);
    let trusted_proxy: Option<IpAddr> = args
        .optional("trusted-proxy")
        .map(|v| {
            os_string(v, "trusted proxy")?
                .parse()
                .map_err(|_| "trusted proxy must be a literal IP".to_owned())
        })
        .transpose()?;
    args.finish()?;
    if !private_listener(listen.ip()) {
        return Err("bootstrap requires a loopback or private listen IP behind TLS".into());
    }
    let socket = SOCKET.get().ok_or("bootstrap requires --socket")?.clone();
    if !socket.is_absolute() {
        return Err("bootstrap requires an absolute local public socket".into());
    }
    if std::fs::read(socket.with_extension("mode")).map_err(|e| e.to_string())? != b"public-v1" {
        return Err("bootstrap requires a public-v1 socket".into());
    }
    if transport::read_config(&config)? != transport::read_config(&socket.with_extension("config"))?
    {
        return Err("bootstrap config does not match the public socket pin".into());
    }
    let sha = host_image_sha256(&host)?;
    let dispatcher = Arc::new(PinnedHost {
        socket,
        config,
        sha: sha.clone(),
    });
    let profile = host_json(
        &*dispatcher,
        HostRead::Profile,
        b"",
        Instant::now() + REQUEST_TIME,
    )
    .map_err(|e| format!("bootstrap profile: {}", e.1))?;
    let mut bytes = Vec::new();
    std::fs::File::open(metadata_path)
        .map_err(|e| e.to_string())?
        .take((MAX_RESPONSE + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > MAX_RESPONSE {
        return Err("public metadata too large".into());
    }
    let configured: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    let app = Arc::new(App {
        metadata: metadata(configured, &profile, &sha)?,
        host: dispatcher,
        trusted_proxy,
        rates: Mutex::new(RateLimit::default()),
        status_rates: Mutex::new(RateLimit::default()),
        status_live: AtomicUsize::new(0),
        live: AtomicUsize::new(0),
    });
    if check {
        return super::print_json(&app.metadata);
    }
    let listener = TcpListener::bind(listen).map_err(|e| e.to_string())?;
    let (sender, receiver) = mpsc::sync_channel::<(TcpStream, Instant)>(QUEUED);
    let joins = workers(
        receiver,
        Arc::new(move |(mut stream, accepted)| {
            let peer = match stream.peer_addr() {
                Ok(peer) => peer.ip(),
                Err(_) => return,
            };
            let response = match read_request(&mut stream, accepted + REQUEST_TIME) {
                Ok(request) => app.handle(request, peer, Instant::now() + REQUEST_TIME),
                Err(error) => Response::error(error),
            };
            write_response(&mut stream, response, Instant::now() + REQUEST_TIME);
        }),
    );
    eprintln!(
        "enrollment bootstrap listening on {}",
        listener.local_addr().map_err(|e| e.to_string())?
    );
    let result = loop {
        match listener.accept() {
            Ok((stream, _)) => match sender.try_send((stream, Instant::now())) {
                Ok(()) => {}
                Err(mpsc::TrySendError::Full((mut stream, _))) => write_response(
                    &mut stream,
                    Response::error(HttpError(503, "busy")),
                    Instant::now() + Duration::from_millis(100),
                ),
                Err(mpsc::TrySendError::Disconnected(_)) => {
                    break Err("bootstrap workers stopped".into())
                }
            },
            Err(error) if error.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(error) => break Err(error.to_string()),
        }
    };
    drop(sender);
    for join in joins {
        let _ = join.join();
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Condvar;

    fn request(method: &str, target: &str, body: Value) -> Request {
        Request {
            method: method.into(),
            target: target.into(),
            headers: HashMap::from([("content-type".into(), "application/json".into())]),
            body: serde_json::to_vec(&body).unwrap(),
        }
    }
    #[test]
    fn paid_routes_are_closed_and_preserve_source_json_bytes() {
        assert!(paid_route("/mini/v2/claim/187").is_none());
        assert!(paid_route("/mini/v2/claim/lookup?operation=185").is_none());
        let duplicate=br#"{"kind":"purchase","kind":"claim"}"#;
        assert_eq!(paid_body(HostRead::PaidQuote,duplicate).unwrap(),duplicate);
        assert!(paid_body(HostRead::PaidQuote,b"[]").is_err());
        assert!(paid_body(HostRead::ClaimPlan,&vec![1;2049]).is_err());
        assert!(paid_body(HostRead::ClaimLookup,&vec![1;4097]).is_err());
        let pair=crate::participant_enrollment::pair(&[1,2,3],&[4;64]).unwrap();
        assert!(paid_body(HostRead::ClaimAssemble,&pair).is_ok());
        assert!(paid_body(HostRead::ClaimAssemble,&pair[..pair.len()-1]).is_err());
    }

    #[test]
    fn all_paid_routes_dispatch_only_their_fixed_operation() {
        let peer="127.0.0.1".parse().unwrap();
        for (route,operation,key) in [
            ("/mini/v2/status",HostRead::PaidStatus,"type"),
            ("/mini/v2/quote",HostRead::PaidQuote,"type"),
            ("/mini/v2/claim/plan",HostRead::ClaimPlan,"canonicalPlan"),
            ("/mini/v2/claim/assemble",HostRead::ClaimAssemble,"canonicalIngress"),
            ("/mini/v2/claim/submit",HostRead::ClaimSubmit,"canonicalOutcome"),
            ("/mini/v2/claim/lookup",HostRead::ClaimLookup,"canonicalOutcome")]
        {
            let (app,fake)=app();
            let mut request=request("POST",route,json!({"identityKey":"aa".repeat(32)}));
            if operation as u8>=183 {
                request.headers.insert("content-type".into(),"application/octet-stream".into());
                request.body=if operation==HostRead::ClaimAssemble {crate::participant_enrollment::pair(&[1,2],&[3;64]).unwrap()} else {vec![1,2,3]};
            }
            let response=app.handle(request,peer,Instant::now()+REQUEST_TIME);
            assert_eq!(response.status,200,"{route}");
            assert!(response.body.get(key).is_some(),"{route}: {:?}",response.body);
            assert_eq!(*fake.calls.lock().unwrap(),vec![operation]);
        }
    }

    #[test]
    fn paid_quote_and_legacy_quote_share_one_rate_budget() {
        let (app,fake)=app();
        let peer="127.0.0.1".parse().unwrap();
        assert_eq!(app.handle(request("POST","/mini/v1/quote",quote()),peer,Instant::now()+REQUEST_TIME).status,200);
        assert_eq!(app.handle(request("POST","/mini/v2/quote",json!({})),peer,Instant::now()+REQUEST_TIME).status,200);
        assert_eq!(app.handle(request("POST","/mini/v2/claim/plan",json!({})),peer,Instant::now()+REQUEST_TIME).status,415);
        assert_eq!(app.handle(request("POST","/mini/v2/quote",json!({})),peer,Instant::now()+REQUEST_TIME).status,200);
        assert_eq!(app.handle(request("POST","/mini/v2/quote",json!({})),peer,Instant::now()+REQUEST_TIME).status,200);
        assert_eq!(app.handle(request("POST","/mini/v2/quote",json!({})),peer,Instant::now()+REQUEST_TIME).status,429);
        assert_eq!(fake.calls.lock().unwrap().len(),4);
    }

    #[test]
    fn complete_claim_workflow_fits_one_shared_rate_budget() {
        let (app,fake)=app();let peer="127.0.0.1".parse().unwrap();
        assert_eq!(app.handle(request("POST","/mini/v2/quote",json!({})),peer,Instant::now()+REQUEST_TIME).status,200);
        for (route,body) in [("plan",vec![1,2]),("assemble",crate::participant_enrollment::pair(&[1,2],&[3;64]).unwrap()),("submit",vec![1,2,3])] {
            let mut req=request("POST",&format!("/mini/v2/claim/{route}"),Value::Null);
            req.body=body;req.headers.insert("content-type".into(),"application/octet-stream".into());
            assert_eq!(app.handle(req,peer,Instant::now()+REQUEST_TIME).status,200,"{route}");
        }
        assert_eq!(*fake.calls.lock().unwrap(),vec![HostRead::PaidQuote,HostRead::ClaimPlan,HostRead::ClaimAssemble,HostRead::ClaimSubmit]);
        assert_eq!(app.handle(request("POST","/mini/v2/quote",json!({})),peer,Instant::now()+REQUEST_TIME).status,429);
    }

    struct FixedPaidStatus(Value);
    impl Dispatch for FixedPaidStatus {
        fn call(&self,operation:HostRead,_:&[u8],_:Instant)->Result<Vec<u8>> {
            assert_eq!(operation,HostRead::PaidStatus);
            Ok([vec![operation as u8],serde_json::to_vec(&self.0).unwrap()].concat())
        }
    }
    #[test]
    fn typed_paid_status_preserves_pending_and_refuses_incomplete_host_json() {
        let peer="127.0.0.1".parse().unwrap();
        let body=json!({"identityKey":"aa".repeat(32),"signature":"bb".repeat(64),"originalRecipient":"cc".repeat(32)});
        let source=crate::pay_status::fixture(&body,json!({"state":"pendingV2","amountAtomic":"522","slot":"99","index":"0","reason":"termsStale"}));
        let (mut app,_)=app();app.host=Arc::new(FixedPaidStatus(source.clone()));
        let response=app.handle(request("POST","/mini/v2/status",body.clone()),peer,Instant::now()+REQUEST_TIME);
        assert_eq!(response.status,200);assert_eq!(response.body,source);
        app.host=Arc::new(FixedPaidStatus(json!({"type":"payStatus","leaseState":"notEnrolled"})));
        let response=app.handle(request("POST","/mini/v2/status",body),peer,Instant::now()+REQUEST_TIME);
        assert_eq!(response.status,503);assert_eq!(response.body["error"],"invalidHostResponse");
    }

    fn quote() -> Value {
        json!({"miniKey":"aa".repeat(32),"mode":"enrol","weeks":"1","starterCredit":null})
    }
    struct Fake {
        calls: Mutex<Vec<HostRead>>,
    }
    impl Dispatch for Fake {
        fn call(&self, operation: HostRead, payload: &[u8], _: Instant) -> Result<Vec<u8>> {
            self.calls.lock().unwrap().push(operation);
            let value = match operation {
                HostRead::Quote => {
                    assert_eq!(serde_json::from_slice::<Value>(payload).unwrap(), quote());
                    json!({"type":"minidregg-pay-enrollment-quote-v1","priceReserved":false,"amountAtomic":"501"})
                }
                HostRead::Enrollment => {
                    assert!(payload.is_empty());
                    return Ok([vec![112], b"canonical-view".to_vec()].concat());
                }
                HostRead::InspectEnrollment => {
                    let kind = b"pay-enrolment-view";
                    assert_eq!(&payload[..2], &(kind.len() as u16).to_le_bytes());
                    assert_eq!(&payload[2..2 + kind.len()], kind);
                    assert_eq!(&payload[2 + kind.len()..], b"canonical-view");
                    json!({"view":"DREGG/PAY/ENROLMENT-VIEW/v3","clock":{"hour":21},
                        "entries":[
                            {"miniKey":"aa".repeat(32),"sshBlob":"public-ssh","subject":"101","index":7,"lease":{"expiresAt":22}},
                            {"miniKey":"bb".repeat(32),"sshBlob":"other-ssh","subject":"202","index":8,"lease":null}],
                        "journal":[{"signature":"cc".repeat(64),"reason":"enrolled"},
                            {"signature":"dd".repeat(64),"reason":"other"}]})
                }
                HostRead::PaidStatus => {
                    let request:Value=serde_json::from_slice(payload).unwrap();
                    let payment=if request.get("signature").is_some(){json!({"state":"pendingV2","amountAtomic":"522","slot":"99","index":"0","reason":"termsStale"})}else{json!({"state":"notRequested"})};
                    crate::pay_status::fixture(&request,payment)
                },
                HostRead::PaidQuote => json!({"type":"payQuote","priceReserved":false}),
                HostRead::ClaimPlan | HostRead::ClaimAssemble | HostRead::ClaimSubmit | HostRead::ClaimLookup => {
                    return Ok(vec![operation as u8,1,2,3]);
                }
                HostRead::Profile => panic!("not requested by route"),
            };
            let mut reply = vec![operation as u8];
            reply.extend(serde_json::to_vec(&value).unwrap());
            Ok(reply)
        }
    }
    fn app() -> (App, Arc<Fake>) {
        let fake = Arc::new(Fake {
            calls: Mutex::new(Vec::new()),
        });
        (
            App {
                metadata: json!({"type":"test"}),
                host: fake.clone(),
                trusted_proxy: None,
                rates: Mutex::new(RateLimit::default()),
                status_rates: Mutex::new(RateLimit::default()),
                status_live: AtomicUsize::new(0),
                live: AtomicUsize::new(0),
            },
            fake,
        )
    }
    #[test]
    fn framing_refuses_smuggling_and_unbounded_bodies() {
        for bad in [
            "POST /mini/v1/quote HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\ncontent-length: 2\r\n\r\n",
            "POST /mini/v1/quote HTTP/1.1\r\nHost: x\r\nContent-Length: 2\r\nTransfer-Encoding: chunked\r\n\r\n",
            "POST /mini/v1/quote HTTP/1.1\r\nHost: x\r\nContent-Length: +2\r\n\r\n",
            "POST /mini/v1/quote HTTP/1.1\r\nHost: x\r\nContent-Length: 4097\r\n\r\n",
            "POST /mini/v1/quote HTTP/1.1\r\nHost: x\r\n\r\n",
            "GET /mini/v1/metadata HTTP/1.1\r\n Host: x\r\n\r\n",
            "GET /mini/v1/metadata HTTP/1.1\r\n\r\n",
            "GET https://x/mini/v1/metadata HTTP/1.1\r\nHost: x\r\n\r\n",
            "GET /mini/v1/metadata HTTP/1.1\r\nHost: x\r\nContent-Length: 1\r\n\r\n",
        ] { assert!(parse_head(bad.as_bytes()).is_err(),"{bad}"); }
        let (_, length) =
            parse_head(b"POST /mini/v1/quote HTTP/1.1\r\nHost: x\r\nContent-Length: 4096\r\n\r\n")
                .unwrap();
        assert_eq!(length, 4096);
    }
    #[test]
    fn fixed_routes_and_exact_filters_expose_no_other_rows() {
        let (app, fake) = app();
        let peer = "127.0.0.1".parse().unwrap();
        let deadline = Instant::now() + REQUEST_TIME;
        assert_eq!(
            app.handle(request("POST", "/mini/v1/quote", quote()), peer, deadline)
                .status,
            200
        );
        let target = format!(
            "/mini/v1/enrollment/{}?signature={}",
            "aa".repeat(32),
            "cc".repeat(64)
        );
        let response = app.handle(request("GET", &target, Value::Null), peer, deadline);
        assert_eq!(response.status, 200);
        assert_eq!(response.body["entry"]["miniKey"], "aa".repeat(32));
        assert_eq!(response.body["entry"]["sshBlob"], "public-ssh");
        assert_eq!(response.body["entry"]["subject"], "101");
        assert_eq!(response.body["paymentDecision"]["reason"], "enrolled");
        assert!(!response.body.to_string().contains("other"));
        let target = format!("/mini/v1/enrollment/{}", "ee".repeat(32));
        let missing = app.handle(request("GET", &target, Value::Null), peer, deadline);
        assert_eq!(missing.body["state"], "notObserved");
        assert!(missing.body["entry"].is_null());
        assert_eq!(
            *fake.calls.lock().unwrap(),
            vec![
                HostRead::Quote,
                HostRead::Enrollment,
                HostRead::InspectEnrollment,
                HostRead::Enrollment,
                HostRead::InspectEnrollment
            ]
        );
    }
    #[test]
    fn unknown_routes_queries_and_ops_never_dispatch() {
        let (app, fake) = app();
        let peer = "127.0.0.1".parse().unwrap();
        let deadline = Instant::now() + REQUEST_TIME;
        for target in [
            "/mini/v1/invoke/117",
            "/mini/v1/metadata?op=6",
            "/mini/v1/enrollment/aa?op=112",
            "/mini/v1/enrollment/../../operator",
        ] {
            assert_ne!(
                app.handle(request("GET", target, Value::Null), peer, deadline)
                    .status,
                200
            );
        }
        let mut body = quote();
        body["operation"] = json!(117);
        assert_eq!(
            app.handle(request("POST", "/mini/v1/quote", body), peer, deadline)
                .status,
            400
        );
        assert_eq!(
            app.handle(
                request("GET", "/mini/v1/quote", Value::Null),
                peer,
                deadline
            )
            .status,
            405
        );
        assert!(fake.calls.lock().unwrap().is_empty());
    }
    #[test]
    fn quote_shape_is_strict_and_canonical() {
        for field in ["miniKey", "mode", "weeks", "starterCredit"] {
            let mut body = quote();
            body.as_object_mut().unwrap().remove(field);
            assert!(quote_body(&serde_json::to_vec(&body).unwrap()).is_err());
        }
        for value in [
            json!("01"),
            json!("-1"),
            json!(1),
            json!("0"),
            json!("18446744073709551616"),
        ] {
            let mut body = quote();
            body["weeks"] = value;
            assert!(quote_body(&serde_json::to_vec(&body).unwrap()).is_err());
        }
        assert!(quote_body(b"[]").is_err());
        assert!(quote_body(b"{").is_err());
        assert!(quote_body(&serde_json::to_vec(&quote()).unwrap()).is_ok());
    }
    #[test]
    fn rate_limit_has_burst_minute_and_memory_bounds() {
        let now = Instant::now();
        let ip = "127.0.0.1".parse().unwrap();
        let mut rate = RateLimit::default();
        for second in [0, 10, 20, 30, 40, 50] {
            assert!(rate.allow(ip, now + Duration::from_secs(second), QUOTE_RATE));
        }
        assert!(!rate.allow(ip, now + Duration::from_secs(59), QUOTE_RATE));
        assert!(rate.allow(ip, now + Duration::from_secs(60), QUOTE_RATE));
        let mut rate = RateLimit::default();
        for _ in 0..QUOTE_RATE.burst { assert!(rate.allow(ip, now, QUOTE_RATE)); }
        assert!(!rate.allow(ip, now, QUOTE_RATE));
        for n in 1..MAX_RATE_CLIENTS {
            assert!(rate.allow(
                IpAddr::V4(std::net::Ipv4Addr::from(n as u32)),
                now,
                QUOTE_RATE
            ));
        }
        // Full: a fresh client evicts the least recently active budget.
        assert_eq!(rate.clients.len(), MAX_RATE_CLIENTS);
        assert!(rate.allow("192.0.2.1".parse().unwrap(), now + Duration::from_secs(1), QUOTE_RATE));
        assert_eq!(rate.clients.len(), MAX_RATE_CLIENTS);
        assert!(rate.allow(
            "192.0.2.1".parse().unwrap(),
            now + Duration::from_secs(60),
            QUOTE_RATE
        ));
    }
    #[test]
    fn one_ipv6_slash64_is_one_budget_and_cannot_lock_out_a_fresh_ipv4_client() {
        let now = Instant::now();
        let mut rate = RateLimit::default();
        // 10k distinct /128s inside 2001:db8:0:1::/64 share one budget.
        let mut admitted = 0;
        for host in 0..10_000u128 {
            let ip = IpAddr::V6(std::net::Ipv6Addr::from((0x2001_0db8_0000_0001u128 << 64) | host));
            if rate.allow(ip, now, QUOTE_RATE) {
                admitted += 1;
            }
        }
        assert_eq!(admitted, QUOTE_RATE.burst);
        assert_eq!(rate.clients.len(), 1);
        // A fresh IPv4 client still has room and its own budget.
        assert!(rate.allow("198.51.100.7".parse().unwrap(), now, QUOTE_RATE));
        assert_eq!(rate.clients.len(), 2);
        // v4-mapped IPv6 is the same budget as the IPv4 address.
        let mapped: IpAddr = "::ffff:198.51.100.7".parse().unwrap();
        assert_eq!(rate_key(mapped), rate_key("198.51.100.7".parse().unwrap()));
        // Even 2000 distinct /64s cannot lock out a fresh client: the table
        // stays bounded and evicts the least recently active budget.
        let mut rate = RateLimit::default();
        for prefix in 0..2_000u128 {
            let ip = IpAddr::V6(std::net::Ipv6Addr::from(((0x2001_0db8u128 << 32 | prefix) << 64) | 1));
            assert!(rate.allow(ip, now, QUOTE_RATE));
        }
        assert_eq!(rate.clients.len(), MAX_RATE_CLIENTS);
        assert!(rate.allow("203.0.113.9".parse().unwrap(), now, QUOTE_RATE));
        assert_eq!(rate.clients.len(), MAX_RATE_CLIENTS);
    }
    #[test]
    fn spoofed_real_ip_cannot_bypass_quote_limit() {
        let (mut app, _) = app();
        let peer = "127.0.0.1".parse().unwrap();
        for n in 1..=QUOTE_RATE.burst + 1 {
            let expected = if n <= QUOTE_RATE.burst { 200 } else { 429 };
            let mut request = request("POST", "/mini/v1/quote", quote());
            request
                .headers
                .insert("x-real-ip".into(), format!("192.0.2.{n}"));
            assert_eq!(
                app.handle(request, peer, Instant::now() + REQUEST_TIME)
                    .status,
                expected
            );
        }
        app.trusted_proxy = Some(peer);
        let request = request("POST", "/mini/v1/quote", quote());
        assert_eq!(
            app.handle(request, peer, Instant::now() + REQUEST_TIME)
                .status,
            400
        );
    }
    #[test]
    fn metadata_whitelist_does_not_copy_internal_profile_or_config() {
        let base = json!({"sshLogin":"mini@example.org","clientBundleUrl":"https://example.org/mini",
            "clientBundleSha256":"ab".repeat(32)});
        let profile = json!({"domain":"123","semantics":"456","storageRoot":"/secret","providerKey":"hidden"});
        let output = metadata(base.clone(), &profile, &"11".repeat(32)).unwrap();
        assert_eq!(output["domain"], "123");
        assert_eq!(output["memoVersions"], json!(["enrol:v1"]));
        assert!(output.get("storageRoot").is_none());
        assert!(output.get("providerKey").is_none());
        let mut unsafe_metadata = base;
        unsafe_metadata["operatorSocket"] = json!("/private");
        assert!(metadata(unsafe_metadata, &profile, &"11".repeat(32)).is_err());
        assert!(!private_listener("0.0.0.0".parse().unwrap()));
        assert!(!private_listener("8.8.8.8".parse().unwrap()));
        assert!(private_listener("10.10.1.10".parse().unwrap()));
    }
    #[test]
    fn host_work_permits_are_global_and_released() {
        let counter = AtomicUsize::new(0);
        let first = permit(&counter, HOST_WORK).unwrap();
        let second = permit(&counter, HOST_WORK).unwrap();
        assert!(permit(&counter, HOST_WORK).is_err());
        drop(first);
        assert!(permit(&counter, HOST_WORK).is_ok());
        drop(second);
        assert_eq!(counter.load(Ordering::Acquire), 0);
    }
    #[test]
    fn status_rate_is_separate_and_spoofed_addresses_do_not_bypass_it() {
        let (app, fake) = app();
        let peer = "127.0.0.1".parse().unwrap();
        let target = format!("/mini/v1/enrollment/{}", "aa".repeat(32));
        for n in 1..=STATUS_RATE.burst + 1 {
            let expected = if n <= STATUS_RATE.burst { 200 } else { 429 };
            let mut poll = request("GET", &target, Value::Null);
            poll.headers
                .insert("x-real-ip".into(), format!("192.0.2.{n}"));
            let response = app.handle(poll, peer, Instant::now() + REQUEST_TIME);
            assert_eq!(response.status, expected);
            if expected == 429 {
                assert_eq!(response.body["error"], "statusRateLimited");
            }
        }
        assert_eq!(fake.calls.lock().unwrap().len(), 4);
        assert_eq!(
            app.handle(
                request("POST", "/mini/v1/quote", quote()),
                peer,
                Instant::now() + REQUEST_TIME
            )
            .status,
            200
        );
        assert_eq!(app.live.load(Ordering::Acquire), 0);
        assert_eq!(app.status_live.load(Ordering::Acquire), 0);
        let now = Instant::now();
        let mut rate = RateLimit::default();
        for second in (0..60).step_by(5) {
            assert!(rate.allow(peer, now + Duration::from_secs(second), STATUS_RATE));
        }
        assert!(!rate.allow(peer, now + Duration::from_secs(59), STATUS_RATE));
        assert!(rate.allow(peer, now + Duration::from_secs(60), STATUS_RATE));
    }

    struct BlockingStatus {
        fake: Fake,
        started: mpsc::Sender<()>,
        gate: (Mutex<bool>, Condvar),
        live: AtomicUsize,
        peak: AtomicUsize,
    }
    impl Dispatch for BlockingStatus {
        fn call(&self, operation: HostRead, payload: &[u8], deadline: Instant) -> Result<Vec<u8>> {
            let live = self.live.fetch_add(1, Ordering::SeqCst) + 1;
            let _release = Permit(&self.live);
            self.peak.fetch_max(live, Ordering::SeqCst);
            if operation == HostRead::Enrollment {
                self.started.send(()).unwrap();
                let (released, waited) = self
                    .gate
                    .1
                    .wait_timeout_while(
                        self.gate.0.lock().unwrap(),
                        deadline.saturating_duration_since(Instant::now()),
                        |released| !*released,
                    )
                    .unwrap();
                if waited.timed_out() && !*released {
                    return Err("test Host deadline".into());
                }
            }
            self.fake.call(operation, payload, deadline)
        }
    }
    #[test]
    fn status_flood_leaves_quote_capacity_and_releases_every_permit() {
        let (mut app, _) = app();
        let (started, receiver) = mpsc::channel();
        let host = Arc::new(BlockingStatus {
            fake: Fake {
                calls: Mutex::new(Vec::new()),
            },
            started,
            gate: (Mutex::new(false), Condvar::new()),
            live: AtomicUsize::new(0),
            peak: AtomicUsize::new(0),
        });
        app.host = host.clone();
        let app = Arc::new(app);
        let worker = app.clone();
        let target = format!("/mini/v1/enrollment/{}", "aa".repeat(32));
        let worker_target = target.clone();
        let pending = thread::spawn(move || {
            worker.handle(
                request("GET", &worker_target, Value::Null),
                "192.0.2.1".parse().unwrap(),
                Instant::now() + REQUEST_TIME,
            )
        });
        receiver.recv_timeout(Duration::from_secs(2)).unwrap();
        for n in 2..34 {
            let denied = app.handle(
                request("GET", &target, Value::Null),
                format!("192.0.2.{n}").parse().unwrap(),
                Instant::now() + REQUEST_TIME,
            );
            assert_eq!(denied.status, 503);
            assert_eq!(denied.body["error"], "statusBusy");
            assert_eq!(app.live.load(Ordering::Acquire), 1);
        }
        let quoted = app.handle(
            request("POST", "/mini/v1/quote", quote()),
            "192.0.2.100".parse().unwrap(),
            Instant::now() + REQUEST_TIME,
        );
        assert_eq!(quoted.status, 200);
        assert_eq!(host.peak.load(Ordering::SeqCst), HOST_WORK);
        assert_eq!(app.live.load(Ordering::Acquire), 1);
        *host.gate.0.lock().unwrap() = true;
        host.gate.1.notify_all();
        assert_eq!(pending.join().unwrap().status, 200);
        assert_eq!(app.live.load(Ordering::Acquire), 0);
        assert_eq!(app.status_live.load(Ordering::Acquire), 0);
    }

    struct ViewHost {
        view: Value,
        oversized_wire: bool,
        calls: AtomicUsize,
    }
    impl Dispatch for ViewHost {
        fn call(&self, operation: HostRead, _: &[u8], _: Instant) -> Result<Vec<u8>> {
            self.calls.fetch_add(1, Ordering::Relaxed);
            let mut response = vec![operation as u8];
            match operation {
                HostRead::Enrollment if self.oversized_wire => {
                    response.resize(MAX_STATUS_VIEW + 2, 0)
                }
                HostRead::Enrollment => response.extend_from_slice(b"view"),
                HostRead::InspectEnrollment => {
                    response.extend_from_slice(&serde_json::to_vec(&self.view).unwrap())
                }
                _ => panic!("unexpected status operation"),
            }
            Ok(response)
        }
    }
    fn status_view(hour: u64, lease: Value) -> Value {
        json!({"view":"DREGG/PAY/ENROLMENT-VIEW/v3","clock":{"hour":hour},
            "entries":[{"miniKey":"aa".repeat(32),"sshBlob":"ssh","subject":"101",
                "index":7,"lease":lease}],"journal":[]})
    }
    #[test]
    fn lease_expiry_is_visible_without_discarding_identity_or_exact_decision() {
        for (hour, lease, state) in [
            (21, json!({"expiresAt":22}), "enrolled"),
            (22, json!({"expiresAt":22}), "expired"),
            (23, json!({"expiresAt":22}), "expired"),
            (23, Value::Null, "noLease"),
        ] {
            let host = ViewHost {
                view: status_view(hour, lease.clone()),
                oversized_wire: false,
                calls: AtomicUsize::new(0),
            };
            let status =
                enrollment(&host, &"aa".repeat(32), None, Instant::now() + REQUEST_TIME).unwrap();
            assert_eq!(status["state"], state);
            assert_eq!(status["entry"]["lease"], lease);
            assert_eq!(status["entry"]["miniKey"], "aa".repeat(32));
        }
    }
    #[test]
    fn growing_journal_is_filtered_but_oversize_fails_before_unbounded_inspection() {
        let mut view = status_view(21, json!({"expiresAt":22}));
        let signature = "cc".repeat(64);
        let mut rows: Vec<Value> = (0..10_000)
            .map(|n| {
                json!({
            "signature":format!("{n:0128x}"),"reason":"unrelated"})
            })
            .collect();
        rows.push(json!({"signature":signature,"reason":"exact"}));
        view["journal"] = json!(rows);
        let host = ViewHost {
            view,
            oversized_wire: false,
            calls: AtomicUsize::new(0),
        };
        let status = enrollment(
            &host,
            &"aa".repeat(32),
            Some(&signature),
            Instant::now() + REQUEST_TIME,
        )
        .unwrap();
        assert_eq!(status["paymentDecision"]["reason"], "exact");
        assert!(serde_json::to_vec(&status).unwrap().len() < MAX_RESPONSE);
        assert!(!status.to_string().contains("unrelated"));
        for oversized_wire in [true, false] {
            let (mut app, _) = app();
            let host = Arc::new(ViewHost {
                view: json!({"padding":"x".repeat(MAX_STATUS_JSON)}),
                oversized_wire,
                calls: AtomicUsize::new(0),
            });
            app.host = host.clone();
            let target = format!("/mini/v1/enrollment/{}", "aa".repeat(32));
            let failed = app.handle(
                request("GET", &target, Value::Null),
                "192.0.2.1".parse().unwrap(),
                Instant::now() + REQUEST_TIME,
            );
            assert_eq!(failed.status, 503);
            assert_eq!(failed.body["error"], "statusViewTooLarge");
            assert_eq!(
                host.calls.load(Ordering::Relaxed),
                if oversized_wire { 1 } else { 2 }
            );
            assert_eq!(app.live.load(Ordering::Acquire), 0);
            assert_eq!(app.status_live.load(Ordering::Acquire), 0);
        }
    }

    #[test]
    fn worker_pool_and_queue_are_bounded() {
        let (sender, receiver) = mpsc::sync_channel::<()>(QUEUED);
        let gate = Arc::new((Mutex::new(false), Condvar::new()));
        let active = Arc::new(AtomicUsize::new(0));
        let (started_tx, started_rx) = mpsc::channel();
        let gate2 = gate.clone();
        let active2 = active.clone();
        let joins = workers(
            receiver,
            Arc::new(move |_| {
                let n = active2.fetch_add(1, Ordering::SeqCst) + 1;
                assert!(n <= WORKERS);
                started_tx.send(()).unwrap();
                let (lock, condition) = &*gate2;
                let _ready = condition
                    .wait_while(lock.lock().unwrap(), |ready| !*ready)
                    .unwrap();
                active2.fetch_sub(1, Ordering::SeqCst);
            }),
        );
        for _ in 0..WORKERS {
            sender.send(()).unwrap();
        }
        for _ in 0..WORKERS {
            started_rx.recv_timeout(Duration::from_secs(2)).unwrap();
        }
        for _ in 0..QUEUED {
            sender.try_send(()).unwrap();
        }
        assert!(matches!(
            sender.try_send(()),
            Err(mpsc::TrySendError::Full(()))
        ));
        *gate.0.lock().unwrap() = true;
        gate.1.notify_all();
        drop(sender);
        for join in joins {
            join.join().unwrap();
        }
        assert_eq!(active.load(Ordering::SeqCst), 0);
    }
    #[test]
    fn pipelining_is_rejected_and_trickle_cannot_extend_read_deadline() {
        let listener = TcpListener::bind("127.0.0.1:0").unwrap();
        let mut client = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        client
            .write_all(
                b"GET /mini/v1/metadata HTTP/1.1\r\nHost: x\r\n\r\nGET /next HTTP/1.1\r\n\r\n",
            )
            .unwrap();
        let (mut server, _) = listener.accept().unwrap();
        assert_eq!(
            read_request(&mut server, Instant::now() + REQUEST_TIME).unwrap_err(),
            HttpError(400, "extraRequestBytes")
        );
        drop(client);
        let mut client = TcpStream::connect(listener.local_addr().unwrap()).unwrap();
        let (mut server, _) = listener.accept().unwrap();
        let writer = thread::spawn(move || {
            for _ in 0..50 {
                if client.write_all(b"G").is_err() {
                    break;
                }
                thread::sleep(Duration::from_millis(20));
            }
        });
        let start = Instant::now();
        assert_eq!(
            read_request(&mut server, start + Duration::from_millis(70)).unwrap_err(),
            HttpError(408, "readTimeout")
        );
        assert!(start.elapsed() < Duration::from_millis(500));
        drop(server);
        writer.join().unwrap();
    }
}
