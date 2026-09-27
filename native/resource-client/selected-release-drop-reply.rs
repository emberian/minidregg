//! One-shot transport fault fixture: forward one exact op20 socket envelope,
//! retain the complete native reply privately, and close without delivering it.
//! No Mini ingress or Outcome encoding/decoding occurs here.
use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::Path;
use std::time::Duration;

const MAX_FRAME: usize = 12_200_000;

fn frame(stream: &mut UnixStream) -> Result<Vec<u8>, String> {
    let mut prefix = [0u8; 4];
    stream
        .read_exact(&mut prefix)
        .map_err(|e| format!("frame length: {e}"))?;
    let size = u32::from_le_bytes(prefix) as usize;
    if !(1..=MAX_FRAME).contains(&size) {
        return Err("frame outside fixture bound".into());
    }
    let mut bytes = Vec::with_capacity(size + 4);
    bytes.extend_from_slice(&prefix);
    bytes.resize(size + 4, 0);
    stream
        .read_exact(&mut bytes[4..])
        .map_err(|e| format!("frame body: {e}"))?;
    Ok(bytes)
}

fn retain(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(path)
        .map_err(|e| format!("create {}: {e}", path.display()))?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(|e| format!("retain {}: {e}", path.display()))
}

fn run(args: &[String]) -> Result<(), String> {
    if args.len() != 5 {
        return Err(
            "usage: selected-release-drop-reply UPSTREAM.sock PROXY.sock REQUEST.frame REPLY.frame"
                .into(),
        );
    }
    let upstream = Path::new(&args[1]);
    let proxy = Path::new(&args[2]);
    let request_path = Path::new(&args[3]);
    let reply_path = Path::new(&args[4]);
    if proxy.exists() || request_path.exists() || reply_path.exists() {
        return Err("proxy socket or retained frame already exists".into());
    }
    let listener = UnixListener::bind(proxy).map_err(|e| format!("bind proxy: {e}"))?;
    let (mut client, _) = listener.accept().map_err(|e| format!("accept: {e}"))?;
    client
        .set_read_timeout(Some(Duration::from_secs(30)))
        .map_err(|e| e.to_string())?;
    let request = frame(&mut client)?;
    let envelope = &request[4..];
    if envelope.len() < 38 || envelope[0] != 2 {
        return Err("fixture requires pinned v2 envelope".into());
    }
    let config_len = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
    let opcode = 5usize
        .checked_add(config_len)
        .and_then(|n| n.checked_add(32))
        .ok_or("invalid envelope length")?;
    if envelope.get(opcode) != Some(&20) {
        return Err("fixture requires exactly one selected-release submit op20".into());
    }
    retain(request_path, &request)?;
    let mut host = UnixStream::connect(upstream).map_err(|e| format!("connect upstream: {e}"))?;
    host.set_write_timeout(Some(Duration::from_secs(30)))
        .map_err(|e| e.to_string())?;
    host.set_read_timeout(Some(Duration::from_secs(600)))
        .map_err(|e| e.to_string())?;
    host.write_all(&request)
        .map_err(|e| format!("forward request: {e}"))?;
    let reply = frame(&mut host)?;
    retain(reply_path, &reply)?;
    // Drop the client with no response only after the complete native reply is
    // durably retained. The caller must perform an independent exact lookup.
    Ok(())
}

fn main() {
    if let Err(error) = run(&std::env::args().collect::<Vec<_>>()) {
        eprintln!("selected-release-drop-reply: {error}");
        std::process::exit(1);
    }
}
