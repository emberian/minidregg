//! Two JSON-RPC transports with one contract: `call(method, params)` returns the envelope's
//! `result`, or a named refusal. Neither decodes anything; decoding is `decode.rs`.
//!
//! * [`CurlTransport`]: `/usr/bin/curl` spawned per call with a bounded private spool, the shape
//!   of the provider bridge (`native/grain-runtime/src/provider.rs`, `forward`). The endpoint URL
//!   (which carries the provider credential) reaches curl on stdin as `--config -`, never argv.
//! * [`FixtureTransport`]: every call answered from a file named by [`fixture_key`]. This is what
//!   the tests and the J-PAY-1 journey hook use.

use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

use crate::model::{Reason, Refusal};

pub trait Transport {
    /// A name safe to print: never the URL (it may carry a credential).
    fn label(&self) -> &str;
    /// POST one JSON-RPC request; return its `result`.
    fn call(&self, method: &str, params: Value) -> Result<Value, Refusal>;
}

/// The envelope every transport sends. `id` is fixed: one call is one request.
pub fn envelope(method: &str, params: &Value) -> Value {
    json!({ "jsonrpc": "2.0", "id": 1, "method": method, "params": params })
}

/// The `result` of a JSON-RPC envelope, with an `error` surfaced as a named refusal
/// (Bread's `rpc_result`).
pub fn rpc_result(resp: Value) -> Result<Value, Refusal> {
    let mut resp = match resp {
        Value::Object(map) => map,
        _ => return Err(Refusal::malformed("rpc response is not an object")),
    };
    if let Some(err) = resp.get("error") {
        return Err(Refusal::new(Reason::RpcError, format!("rpc error: {err}")));
    }
    resp.remove("result")
        .ok_or_else(|| Refusal::malformed("rpc response missing `result`"))
}

// ---------------------------------------------------------------------------------- fixtures

/// The file (relative to one endpoint's fixture directory) that answers a call.
///
/// | method | params the watcher sends | file |
/// |---|---|---|
/// | `getSlot` | `[{commitment}]` | `getSlot/finalized.json` |
/// | `getBlockTime` | `[slot]` | `getBlockTime/<slot>.json` |
/// | `getTokenAccountsByOwner` | `[owner, {mint}, {encoding, commitment}]` | `getTokenAccountsByOwner/<owner>.<mint>.json` |
/// | `getSignaturesForAddress` | `[account, {commitment, limit, before?, until?}]` | `getSignaturesForAddress/<account>[.before.<signature>][.until.<signature>].json` |
/// | `getTransaction` | `[signature, {encoding, commitment, maxSupportedTransactionVersion}]` | `getTransaction/<signature>.json` |
///
/// Keys and signatures are the base58 text the watcher sent. Each file holds a whole JSON-RPC
/// response envelope (`{"jsonrpc":"2.0","id":1,"result":…}` or `…"error":…`). Before looking a
/// call up, the request is checked for the commitment and encoding PAY.md §3.2 requires, so a
/// fixture run also proves every request asks for `finalized`.
pub fn fixture_key(method: &str, params: &Value) -> Result<String, String> {
    let arr = params.as_array().ok_or("params not an array")?;
    let text = |i: usize| -> Result<&str, String> {
        arr.get(i)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{method} param {i} is not a string"))
    };
    let opts = |i: usize| -> Result<&serde_json::Map<String, Value>, String> {
        arr.get(i)
            .and_then(Value::as_object)
            .ok_or_else(|| format!("{method} param {i} is not an object"))
    };
    let finalized = |o: &serde_json::Map<String, Value>| -> Result<(), String> {
        match o.get("commitment").and_then(Value::as_str) {
            Some("finalized") => Ok(()),
            other => Err(format!("{method} asked for commitment {other:?}, not finalized")),
        }
    };
    match method {
        "getSlot" => {
            finalized(opts(0)?)?;
            Ok("getSlot/finalized.json".into())
        }
        "getBlockTime" => {
            let slot = arr
                .first()
                .and_then(Value::as_u64)
                .ok_or("getBlockTime slot not an integer")?;
            Ok(format!("getBlockTime/{slot}.json"))
        }
        "getTokenAccountsByOwner" => {
            let owner = text(0)?;
            let mint = opts(1)?
                .get("mint")
                .and_then(Value::as_str)
                .ok_or("getTokenAccountsByOwner filter is not {mint}")?;
            let o = opts(2)?;
            finalized(o)?;
            if o.get("encoding").and_then(Value::as_str) != Some("jsonParsed") {
                return Err("getTokenAccountsByOwner not jsonParsed".into());
            }
            Ok(format!("getTokenAccountsByOwner/{owner}.{mint}.json"))
        }
        "getSignaturesForAddress" => {
            let account = text(0)?;
            let o = opts(1)?;
            finalized(o)?;
            if o.get("limit").and_then(Value::as_u64).is_none() {
                return Err("getSignaturesForAddress without a limit".into());
            }
            let mut name = format!("getSignaturesForAddress/{account}");
            for bound in ["before", "until"] {
                if let Some(b) = o.get(bound) {
                    let b = b.as_str().ok_or_else(|| format!("`{bound}` not a string"))?;
                    name.push_str(&format!(".{bound}.{b}"));
                }
            }
            name.push_str(".json");
            Ok(name)
        }
        "getTransaction" => {
            let sig = text(0)?;
            let o = opts(1)?;
            finalized(o)?;
            if o.get("encoding").and_then(Value::as_str) != Some("jsonParsed")
                || o.get("maxSupportedTransactionVersion").and_then(Value::as_u64) != Some(0)
            {
                return Err("getTransaction not jsonParsed with maxSupportedTransactionVersion 0".into());
            }
            Ok(format!("getTransaction/{sig}.json"))
        }
        other => Err(format!("fixture transport has no rule for method {other}")),
    }
}

pub struct FixtureTransport {
    label: String,
    dir: PathBuf,
}

impl FixtureTransport {
    /// The endpoint's label is the directory's last component.
    pub fn new(dir: impl Into<PathBuf>) -> Self {
        let dir = dir.into();
        let label = dir
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_else(|| "fixture".into());
        FixtureTransport { label, dir }
    }
}

impl Transport for FixtureTransport {
    fn label(&self) -> &str {
        &self.label
    }

    fn call(&self, method: &str, params: Value) -> Result<Value, Refusal> {
        let key = fixture_key(method, &params)
            .map_err(|e| Refusal::new(Reason::Transport, format!("fixture request refused: {e}")))?;
        let path = self.dir.join(&key);
        let bytes = fs::read(&path)
            .map_err(|_| Refusal::new(Reason::Transport, format!("fixture has no answer: {key}")))?;
        let value: Value = serde_json::from_slice(&bytes)
            .map_err(|e| Refusal::malformed(format!("fixture {key} not JSON: {e}")))?;
        rpc_result(value)
    }
}

// -------------------------------------------------------------------------------------- curl

pub const CURL: &str = "/usr/bin/curl";
pub const DEFAULT_MAX_RESPONSE: usize = 4 << 20;
pub const DEFAULT_TIMEOUT: Duration = Duration::from_secs(30);

pub struct CurlTransport {
    label: String,
    url: String,
    spool: PathBuf,
    timeout: Duration,
    max_response: usize,
    counter: AtomicU64,
}

/// `https://…`, or plain `http://` only to loopback (the provider bridge's rule).
pub fn validate_endpoint(url: &str) -> Result<(), String> {
    let (scheme, rest) = url.split_once("://").ok_or("endpoint URL lacks a scheme")?;
    let authority = rest.split(['/', '?']).next().unwrap_or("");
    if authority.is_empty() || authority.contains('@') {
        return Err("endpoint URL must name a host and carry no userinfo".into());
    }
    if url.bytes().any(|b| b.is_ascii_control() || b == b'"' || b == b'\\' || b == b' ') {
        return Err("endpoint URL contains a control, quote, backslash or space".into());
    }
    match scheme {
        "https" => Ok(()),
        "http"
            if authority == "127.0.0.1"
                || authority.starts_with("127.0.0.1:")
                || authority == "[::1]"
                || authority.starts_with("[::1]:") =>
        {
            Ok(())
        }
        "http" => Err("plain HTTP endpoint is permitted only on loopback".into()),
        _ => Err("endpoint must use https".into()),
    }
}

impl CurlTransport {
    /// `spool` must be a private directory the watcher owns; each call creates and removes
    /// its own files there.
    pub fn new(
        label: impl Into<String>,
        url: impl Into<String>,
        spool: impl Into<PathBuf>,
    ) -> Result<Self, String> {
        let url = url.into();
        validate_endpoint(&url)?;
        Ok(CurlTransport {
            label: label.into(),
            url,
            spool: spool.into(),
            timeout: DEFAULT_TIMEOUT,
            max_response: DEFAULT_MAX_RESPONSE,
            counter: AtomicU64::new(0),
        })
    }

    pub fn with_bounds(mut self, timeout: Duration, max_response: usize) -> Self {
        self.timeout = timeout;
        self.max_response = max_response;
        self
    }

    fn post(&self, body: &[u8]) -> Result<Vec<u8>, Refusal> {
        let n = self.counter.fetch_add(1, Ordering::Relaxed);
        let prefix = format!("pay-rpc-{}-{}-{n:08}", std::process::id(), self.label);
        let request = self.spool.join(format!("{prefix}.request"));
        let response = self.spool.join(format!("{prefix}.response"));
        let result = self.post_spooled(body, &request, &response);
        let _ = fs::remove_file(&request);
        let _ = fs::remove_file(&response);
        result
    }

    fn post_spooled(&self, body: &[u8], request: &Path, response: &Path) -> Result<Vec<u8>, Refusal> {
        let t = |detail: String| Refusal::new(Reason::Transport, format!("{}: {detail}", self.label));
        write_private(request, body).map_err(t)?;
        create_private(response).map_err(t)?;
        let protocol = if self.url.starts_with("https://") {
            "=https"
        } else {
            "=http"
        };
        let mut command = Command::new(CURL);
        command
            .env_clear()
            .current_dir(&self.spool)
            .arg("--disable")
            .args(["--silent", "--fail", "--http1.1", "--request", "POST"])
            .args(["--proto", protocol, "--noproxy", "*", "--proxy", ""])
            .args(["--max-redirs", "0", "--connect-timeout", "10"])
            .args(["--max-time", &self.timeout.as_secs().max(1).to_string()])
            .args(["--max-filesize", &self.max_response.to_string()])
            .args(["--header", "Content-Type: application/json"])
            .args(["--header", "Accept-Encoding: identity"])
            .arg("--data-binary")
            .arg(format!("@{}", request.display()))
            .arg("--output")
            .arg(response)
            .args(["--config", "-"])
            .stdin(Stdio::piped())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        // Kernel backstop: the response file cannot grow past the bound even if the peer
        // omits Content-Length.
        let file_limit = self.max_response as libc::rlim_t;
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
                    Err(std::io::Error::last_os_error())
                }
            });
        }
        let mut child = command.spawn().map_err(|e| t(format!("spawn curl: {e}")))?;
        let url_written = child.stdin.take().is_some_and(|mut stdin| {
            stdin
                .write_all(format!("url = \"{}\"\n", self.url).as_bytes())
                .is_ok()
        });
        if !url_written {
            let _ = child.kill();
        }
        let started = Instant::now();
        let status = loop {
            match child.try_wait() {
                Ok(Some(status)) => break Some(status),
                Ok(None) => {}
                Err(_) => break None,
            }
            let oversized = fs::metadata(response)
                .is_ok_and(|meta| meta.len() > self.max_response as u64);
            if oversized || started.elapsed() > self.timeout + Duration::from_secs(1) {
                let _ = child.kill();
            }
            thread::sleep(Duration::from_millis(10));
        };
        if !url_written || !status.is_some_and(|s| s.success()) {
            return Err(t(format!(
                "curl did not complete ({})",
                status.map_or("no status".into(), |s| s.to_string())
            )));
        }
        read_bounded(response, self.max_response).map_err(t)
    }
}

impl Transport for CurlTransport {
    fn label(&self) -> &str {
        &self.label
    }

    fn call(&self, method: &str, params: Value) -> Result<Value, Refusal> {
        let body = serde_json::to_vec(&envelope(method, &params))
            .map_err(|e| Refusal::new(Reason::Transport, format!("encode request: {e}")))?;
        let bytes = self.post(&body)?;
        let value: Value = serde_json::from_slice(&bytes).map_err(|e| {
            Refusal::malformed(format!("{}: {method} response not JSON: {e}", self.label))
        })?;
        rpc_result(value)
    }
}

fn write_private(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|e| format!("spool create: {e}"))?;
    file.write_all(bytes).map_err(|e| format!("spool write: {e}"))
}

fn create_private(path: &Path) -> Result<(), String> {
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map(drop)
        .map_err(|e| format!("spool create: {e}"))
}

fn read_bounded(path: &Path, bound: usize) -> Result<Vec<u8>, String> {
    let mut file = File::open(path).map_err(|e| format!("spool read: {e}"))?;
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take(bound as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("spool read: {e}"))?;
    if bytes.len() > bound {
        return Err("response exceeds bound".into());
    }
    Ok(bytes)
}
