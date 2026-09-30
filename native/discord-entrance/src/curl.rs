//! Outbound webhook calls through `/usr/bin/curl`, pay-watcher's shape.
//!
//! The URL carries a secret (an interaction token, or a channel webhook's token), so it
//! reaches curl on stdin as `--config -` and never appears on argv. The JSON body is written
//! to a private spool file (created exclusively, 0600) and removed after the call.

use std::fs::OpenOptions;
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

pub const CURL: &str = "/usr/bin/curl";

static SPOOL_SEQ: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone)]
pub struct Poster {
    pub curl: PathBuf,
    pub spool: PathBuf,
    pub max_time_s: u32,
}

/// A URL that can be written inside a curl config string without escaping.
pub fn is_plain_url(url: &str) -> bool {
    (url.starts_with("https://") || url.starts_with("http://"))
        && url.len() <= 2048
        && url.bytes().all(|b| b.is_ascii_graphic() && b != b'"' && b != b'\\')
}

impl Poster {
    /// Send `body` as JSON; returns the HTTP status.
    pub fn send(&self, method: &str, url: &str, body: &[u8]) -> Result<u16, String> {
        if !is_plain_url(url) {
            return Err("refusing a URL with characters outside plain ASCII".into());
        }
        if !matches!(method, "POST" | "PATCH") {
            return Err(format!("unsupported method {method}"));
        }
        let seq = SPOOL_SEQ.fetch_add(1, Ordering::Relaxed);
        let path = self.spool.join(format!("body-{}-{seq}.json", std::process::id()));
        {
            let mut f = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .open(&path)
                .map_err(|e| format!("spool {}: {e}", path.display()))?;
            f.write_all(body).map_err(|e| format!("spool write: {e}"))?;
        }
        let result = self.run_curl(method, url, &path);
        let _ = std::fs::remove_file(&path);
        result
    }

    fn run_curl(&self, method: &str, url: &str, body: &std::path::Path) -> Result<u16, String> {
        let mut child = Command::new(&self.curl)
            .arg("--disable")
            .args(["--silent", "--show-error", "--max-time"])
            .arg(self.max_time_s.to_string())
            .args(["--request", method, "--header", "Content-Type: application/json"])
            .arg("--data-binary")
            .arg(format!("@{}", body.display()))
            .args(["--output", "/dev/null", "--write-out", "%{http_code}", "--config", "-"])
            .env_clear()
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .map_err(|e| format!("spawn curl: {e}"))?;
        {
            let mut stdin = child.stdin.take().ok_or("curl stdin")?;
            stdin
                .write_all(format!("url = \"{url}\"\n").as_bytes())
                .map_err(|e| format!("curl config: {e}"))?;
        }
        let out = child.wait_with_output().map_err(|e| format!("curl: {e}"))?;
        let code = String::from_utf8_lossy(&out.stdout).trim().parse::<u16>().unwrap_or(0);
        if !out.status.success() || code == 0 {
            return Err(format!(
                "curl failed ({}): {}",
                out.status,
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Ok(code)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn plain_url_rule() {
        assert!(is_plain_url("https://discord.com/api/v10/webhooks/1/abc/messages/@original"));
        assert!(!is_plain_url("https://x/\"\nurl=evil"));
        assert!(!is_plain_url("https://x/ a"));
        assert!(!is_plain_url("file:///etc/passwd"));
    }
}
