//! Per-exchange trace for whole-action accounting. Off unless `MINI_TRACE`
//! names an absolute file; then every Host exchange, client process spawn and
//! shell line appends one JSON line: what it was, bytes out/in, milliseconds,
//! and the pid/parent pid (child `mini` processes inherit the variable, so a
//! whole action reassembles from one file). Tracing never changes a request.
use std::fs::OpenOptions;
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::sync::OnceLock;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

fn target() -> Option<&'static std::path::PathBuf> {
    static TARGET: OnceLock<Option<std::path::PathBuf>> = OnceLock::new();
    TARGET
        .get_or_init(|| {
            std::env::var_os("MINI_TRACE")
                .map(std::path::PathBuf::from)
                .filter(|path| path.is_absolute())
        })
        .as_ref()
}

pub(crate) fn enabled() -> bool {
    target().is_some()
}

/// One traced event that started at `start`.
pub(crate) fn record(kind: &str, what: &str, bytes_out: usize, bytes_in: usize, start: Instant) {
    let Some(path) = target() else { return };
    let ms = start.elapsed().as_secs_f64() * 1000.0;
    let at = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_millis()).unwrap_or(0);
    let line = serde_json::json!({"t":at as u64,"pid":std::process::id(),"ppid":unsafe { libc_getppid() },
        "kind":kind,"what":what,"out":bytes_out,"in":bytes_in,"ms":(ms * 1000.0).round() / 1000.0});
    let mut text = line.to_string();
    text.push('\n');
    // One O_APPEND write per event keeps lines whole across processes.
    if let Ok(mut file) = OpenOptions::new().create(true).append(true).mode(0o600).open(path) {
        let _ = file.write_all(text.as_bytes());
    }
}

unsafe extern "C" {
    #[link_name = "getppid"]
    fn libc_getppid() -> i32;
}

#[cfg(test)]
mod tests {
    #[test]
    fn trace_is_off_without_an_absolute_target() {
        // The test process is started without MINI_TRACE.
        if std::env::var_os("MINI_TRACE").is_none() {
            assert!(!super::enabled());
            super::record("host", "op1", 1, 1, std::time::Instant::now());
        }
    }
}
