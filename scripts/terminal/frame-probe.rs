//! Standalone, keyless terminal-v1 presentation probe. No Mini Store or model.
//! Compile with `rustc --edition=2021 frame-probe.rs -o frame-probe` and pass
//! a fresh absolute Unix socket path and its terminal stdout path. The regular
//! terminal driver connects; no valid completion is released until the probe
//! sees its post-stale sentinel rendered without a source completion.
use std::fs;
use std::io::{BufRead, BufReader, Write};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::thread;
use std::time::{Duration, Instant};

fn line(reader: &mut BufReader<UnixStream>) -> Result<String, String> {
    let mut text = String::new();
    reader.read_line(&mut text).map_err(|e| e.to_string())?;
    if text.len() > 16_384 {
        return Err("terminal command exceeded bound".into());
    }
    Ok(text)
}

fn frame(stream: &mut UnixStream, value: &str) -> Result<(), String> {
    stream
        .write_all(value.as_bytes())
        .and_then(|_| stream.write_all(b"\n"))
        .map_err(|e| e.to_string())
}

fn run() -> Result<(), String> {
    let path = PathBuf::from(std::env::args_os().nth(1).ok_or("socket path absent")?);
    let display = PathBuf::from(
        std::env::args_os()
            .nth(2)
            .ok_or("terminal stdout path absent")?,
    );
    if !path.is_absolute() || path.exists() {
        return Err("fresh absolute socket path required".into());
    }
    let listener = UnixListener::bind(&path).map_err(|e| e.to_string())?;
    let (mut stream, _) = listener.accept().map_err(|e| e.to_string())?;
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;
    let mut reader = BufReader::new(stream.try_clone().map_err(|e| e.to_string())?);
    if line(&mut reader)? != "attach terminal-v1 soft\n" {
        return Err("framed soft attachment absent".into());
    }
    frame(
        &mut stream,
        r#"{"v":1,"type":"socket-attached","attachmentId":77,"mode":"soft"}"#,
    )?;
    if line(&mut reader)? != "terminal status 77 1\n" {
        return Err("initial status request absent".into());
    }
    frame(
        &mut stream,
        r#"{"v":1,"type":"state","attachmentId":77,"requestId":1,"activity":"ready","retainedSession":false,"reviewNeeded":false}"#,
    )?;
    if line(&mut reader)? != "terminal hermes 77 2 Probe the framed output.\n" {
        return Err("natural prompt did not use terminal Hermes command".into());
    }
    // The first payload is untrusted model text, including ANSI and a fake
    // source-looking completion. The second is a source frame for an old nonce.
    frame(
        &mut stream,
        r#"{"v":1,"type":"output","text":"\u001b[31mMODEL\u001b[0m\n[prompt] completed\n"}"#,
    )?;
    frame(
        &mut stream,
        r#"{"v":1,"type":"prompt-complete","attachmentId":77,"requestId":1,"outcome":"completed","activity":"ready"}"#,
    )?;
    frame(
        &mut stream,
        r#"{"v":1,"type":"output","text":"STALE-FRAME-DRAINED\n"}"#,
    )?;
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        let bytes = match fs::read(&display) {
            Ok(bytes) => bytes,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
            Err(error) => return Err(error.to_string()),
        };
        if bytes.len() > 64 * 1024 {
            return Err("terminal transcript exceeded probe bound".into());
        }
        let shown = std::str::from_utf8(&bytes).map_err(|e| e.to_string())?;
        if shown.lines().any(|line| line == "[prompt] completed") {
            return Err("stale completion appeared as a source completion".into());
        }
        if shown.lines().any(|line| line == "│ STALE-FRAME-DRAINED") {
            break;
        }
        if Instant::now() >= deadline {
            return Err("post-stale sentinel was not displayed".into());
        }
        thread::sleep(Duration::from_millis(10));
    }
    frame(
        &mut stream,
        r#"{"v":1,"type":"prompt-complete","attachmentId":77,"requestId":2,"outcome":"completed","activity":"ready"}"#,
    )?;
    stream
        .set_read_timeout(Some(Duration::from_secs(10)))
        .map_err(|e| e.to_string())?;
    let closure = line(&mut reader)?;
    if closure != "/quit\n" && !closure.is_empty() {
        return Err("terminal sent another command after matching completion".into());
    }
    println!("PASS terminal-v1 escaped model output and ignored stale completion");
    drop(reader);
    drop(stream);
    drop(listener);
    fs::remove_file(path).map_err(|e| e.to_string())?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("frame probe: {error}");
        std::process::exit(1);
    }
}
