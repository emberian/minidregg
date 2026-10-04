//! The discord role (the mirror's session account): post to the mirrored
//! channel's webhook, read the channel with the bot token. The webhook URL (it
//! carries the webhook's token) and the bot token stay here; the caller names
//! neither the channel nor the webhook, so the token is usable for exactly the
//! one channel the operator configured.
use super::{refuse, secret_file, Broker, Note, Refusal};
use serde_json::{json, Value};
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::path::Path;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};


pub const SECRETS_TYPE: &str = "mini-discord-mirror-secrets-v1";
const MAX_POST: usize = 16_384;
const MAX_READ: usize = 1 << 20;
const MAX_TIME_S: u32 = 20;
static SEQ: AtomicU64 = AtomicU64::new(0);

pub struct Secrets {
    pub webhook_url: String,
    pub channel_url: String,
    pub bot_token: String,
}

impl Drop for Secrets {
    fn drop(&mut self) {
        for s in [&mut self.webhook_url, &mut self.bot_token] {
            // SAFETY: zero bytes are valid UTF-8.
            unsafe { s.as_bytes_mut().fill(0) };
        }
    }
}

/// A URL that can sit inside a curl config string without escaping. HTTPS,
/// or plain HTTP to a loopback address (a test's fake Discord).
pub fn plain_url(url: &str) -> bool {
    let scheme_ok = url.starts_with("https://") || url.starts_with("http://127.0.0.1:") || url.starts_with("http://[::1]:");
    scheme_ok && url.len() <= 2048 && url.bytes().all(|b| b.is_ascii_graphic() && b != b'"' && b != b'\\')
}

impl Secrets {
    /// Read the mirror's secrets (re-read on every call: a rotation needs no restart).
    pub fn load(path: &Path) -> Result<Self, String> {
        secret_file(path, "the Discord mirror secrets", 8192)?;
        let mut bytes = std::fs::read(path).map_err(|_| "the Discord mirror secrets are unreadable")?;
        let parsed = serde_json::from_slice::<Value>(&bytes);
        crate::wire::zero(&mut bytes);
        let v = parsed.map_err(|_| "the Discord mirror secrets are not JSON")?;
        let fields = ["type", "webhookUrl", "channelUrl", "botToken"];
        if v.as_object().is_none_or(|m| m.len() != fields.len() || m.keys().any(|k| !fields.contains(&k.as_str()))) || v["type"] != SECRETS_TYPE {
            return Err(format!("the Discord mirror secrets must be exactly {fields:?} of {SECRETS_TYPE}"));
        }
        let s = Secrets {
            webhook_url: v["webhookUrl"].as_str().unwrap_or("").to_owned(),
            channel_url: v["channelUrl"].as_str().unwrap_or("").to_owned(),
            bot_token: v["botToken"].as_str().unwrap_or("").to_owned(),
        };
        if !plain_url(&s.webhook_url) || !plain_url(&s.channel_url) || s.channel_url.contains('?') {
            return Err("webhookUrl and channelUrl must be plain https URLs (channelUrl without a query)".into());
        }
        if s.bot_token.is_empty() || s.bot_token.len() > 256 || !s.bot_token.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'_' | b'-')) {
            return Err("botToken has characters a Discord token does not".into());
        }
        Ok(s)
    }
}

fn secrets(broker: &Broker) -> Result<Secrets, Refusal> {
    let d = broker.config.discord.as_ref().ok_or_else(|| refuse("discord-not-configured", "this broker holds no Discord mirror secrets"))?;
    Secrets::load(&d.mirror).map_err(|e| refuse("discord-secrets", e))
}

/// curl with its config (URL and any secret header) on stdin; the response
/// body to a private spool file read back bounded. Returns (status, body).
fn curl(spool: &Path, config: &str, method: &str, body: Option<&[u8]>) -> Result<(u16, Vec<u8>), Refusal> {
    let seq = SEQ.fetch_add(1, Ordering::SeqCst);
    let out = spool.join(format!("discord-{}-{seq}.out", std::process::id()));
    let input = spool.join(format!("discord-{}-{seq}.in", std::process::id()));
    let mk = |p: &Path, bytes: &[u8]| -> Result<(), Refusal> {
        let mut f = std::fs::OpenOptions::new().write(true).create_new(true).mode(0o600).open(p).map_err(|e| refuse("spool", e.to_string()))?;
        f.write_all(bytes).map_err(|e| refuse("spool", e.to_string()))
    };
    mk(&out, b"")?;
    let mut cmd = Command::new(super::CURL);
    cmd.env_clear()
        .arg("--disable")
        .args(["--silent", "--show-error", "--max-redirs", "0", "--max-time", &MAX_TIME_S.to_string()])
        .args(["--max-filesize", &MAX_READ.to_string(), "--request", method, "--output"])
        .arg(&out)
        .args(["--write-out", "%{http_code}"]);
    if let Some(body) = body {
        if let Err(e) = mk(&input, body) {
            let _ = std::fs::remove_file(&out);
            return Err(e);
        }
        cmd.args(["--header", "Content-Type: application/json", "--data-binary"]).arg(format!("@{}", input.display()));
    }
    cmd.args(["--config", "-"]).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::null());
    let result = (|| {
        let mut child = cmd.spawn().map_err(|e| refuse("not-sent", format!("spawn curl: {e}")))?;
        {
            let mut stdin = child.stdin.take().ok_or_else(|| refuse("not-sent", "curl stdin"))?;
            let mut bytes = config.as_bytes().to_vec();
            let w = stdin.write_all(&bytes);
            crate::wire::zero(&mut bytes);
            w.map_err(|_| refuse("not-sent", "curl config"))?;
        }
        let output = child.wait_with_output().map_err(|_| refuse("upstream-uncertain", "curl"))?;
        let code = String::from_utf8_lossy(&output.stdout).trim().parse::<u16>().unwrap_or(0);
        if !output.status.success() || code == 0 {
            return Err(refuse("upstream-uncertain", format!("curl ended {}", output.status)));
        }
        let mut body = Vec::new();
        std::fs::File::open(&out).and_then(|f| f.take(MAX_READ as u64).read_to_end(&mut body)).map_err(|e| refuse("spool", e.to_string()))?;
        Ok((code, body))
    })();
    let _ = std::fs::remove_file(&out);
    let _ = std::fs::remove_file(&input);
    result
}

/// `discord-post {"body": OBJECT}`: POST it to the mirrored channel's webhook (`wait=true`).
pub fn post(broker: &Broker, request: &Value, note: &mut Note) -> Result<Value, Refusal> {
    if request.as_object().is_none_or(|m| m.keys().any(|k| k != "op" && k != "body")) || !request["body"].is_object() {
        return Err(refuse("bad-request", "discord-post takes exactly {body: object}"));
    }
    let body = serde_json::to_vec(&request["body"]).map_err(|_| refuse("bad-request", "body encode"))?;
    if body.len() > MAX_POST {
        return Err(refuse("bad-request", "body exceeds 16 KiB"));
    }
    let s = secrets(broker)?;
    let url = if s.webhook_url.contains('?') { format!("{}&wait=true", s.webhook_url) } else { format!("{}?wait=true", s.webhook_url) };
    let (code, response) = curl(&broker.config.spool, &format!("url = \"{url}\"\n"), "POST", Some(&body))?;
    note.set("status", code);
    if response.windows(s.bot_token.len()).any(|w| w == s.bot_token.as_bytes()) {
        return Err(refuse("upstream-withheld", "the response echoed a custody secret and was withheld"));
    }
    Ok(json!({"ok":true,"status":code}))
}

fn snowflake(s: &str) -> bool {
    !s.is_empty() && s.len() <= 20 && s.bytes().all(|b| b.is_ascii_digit())
}

/// `discord-read {"before": SNOWFLAKE|null, "limit": 1..=50}`: one page of the
/// mirrored channel, read with the bot token. Returns the status and body text.
pub fn read(broker: &Broker, request: &Value, note: &mut Note) -> Result<Value, Refusal> {
    if request.as_object().is_none_or(|m| m.keys().any(|k| !["op", "before", "limit"].contains(&k.as_str()))) {
        return Err(refuse("bad-request", "discord-read takes {before, limit}"));
    }
    let limit = request["limit"].as_u64().filter(|n| (1..=50).contains(n)).ok_or_else(|| refuse("bad-request", "limit must be 1..=50"))?;
    let before = match request.get("before") {
        None | Some(Value::Null) => None,
        Some(v) => Some(v.as_str().filter(|s| snowflake(s)).ok_or_else(|| refuse("bad-request", "before must be a snowflake"))?),
    };
    let s = secrets(broker)?;
    let url = match before {
        Some(id) => format!("{}?before={id}&limit={limit}", s.channel_url),
        None => format!("{}?limit={limit}", s.channel_url),
    };
    let config = format!("url = \"{url}\"\nheader = \"Authorization: Bot {}\"\n", s.bot_token);
    let (code, body) = curl(&broker.config.spool, &config, "GET", None)?;
    note.set("status", code);
    if body.windows(s.bot_token.len()).any(|w| w == s.bot_token.as_bytes()) {
        return Err(refuse("upstream-withheld", "the response echoed a custody secret and was withheld"));
    }
    let text = String::from_utf8(body).map_err(|_| refuse("upstream", "channel response is not UTF-8"))?;
    Ok(json!({"ok":true,"status":code,"body":text}))
}
