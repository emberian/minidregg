//! Exact native selected-release ingress transport. Lean authors and admits the
//! ingress; this module retains bytes and transports only the two Host opcodes.
use super::{
    absolute, create_private, hex, host_image_sha256, inspect, print_json,
    sync_directory_ancestors, utf8_path, Result,
};
use crate::transport::{self, HOST_MAX_FRAME};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

const FORMAT: &str = "minidregg-selected-release-attempt-v1";

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn bounded(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|error| format!("cannot open {}: {error}", path.display()))?
        .take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err(format!("{} must contain 1..={limit} bytes", path.display()));
    }
    Ok(bytes)
}

fn new_path(directory: &Path) -> Result<(PathBuf, PathBuf, PathBuf)> {
    for index in 0..10_000 {
        let base = format!("request-{index:04}");
        let marker = directory.join(format!("{base}.json"));
        let frame = directory.join(format!("{base}.frame"));
        let outcome = directory.join(format!("{base}.bin"));
        if !marker.exists() && !frame.exists() && !outcome.exists() {
            return Ok((marker, frame, outcome));
        }
    }
    Err("selected-release attempt exhausted evidence names".into())
}

struct Attempt {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    host_sha: String,
    ingress: Vec<u8>,
}

fn retained(directory: &Path) -> Result<Attempt> {
    let manifest_bytes = bounded(&directory.join("attempt.json"), 65_536)?;
    let manifest: Value = serde_json::from_slice(&manifest_bytes)
        .map_err(|error| format!("invalid selected-release manifest: {error}"))?;
    if manifest.get("format").and_then(Value::as_str) != Some(FORMAT) {
        return Err("not a selected-release attempt".into());
    }
    let field = |name: &str| -> Result<&str> {
        manifest
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("selected-release manifest lacks {name}"))
    };
    let host = PathBuf::from(field("host")?);
    let config = PathBuf::from(field("config")?);
    let socket = PathBuf::from(field("socket")?);
    let host_sha = field("hostSha256")?.to_owned();
    if !host.is_absolute()
        || !config.is_absolute()
        || !socket.is_absolute()
        || config != absolute(&directory.join("config.json"))?
        || host_image_sha256(&host)? != host_sha
    {
        return Err("selected-release attempt identity or Host image changed".into());
    }
    let ingress = bounded(&directory.join("ingress.bin"), HOST_MAX_FRAME - 1)?;
    let config_bytes = bounded(&config, 65_536)?;
    if digest(&ingress) != field("ingressSha256")?
        || digest(&config_bytes) != field("configSha256")?
    {
        return Err("retained selected-release ingress or config changed".into());
    }
    Ok(Attempt {
        host,
        config,
        socket,
        host_sha,
        ingress,
    })
}

fn latest_lookup_absent_with<F>(
    directory: &Path,
    attempt: &Attempt,
    inspect_outcome: F,
) -> Result<bool>
where
    F: FnOnce(&Path, &Path) -> Result<Value>,
{
    let mut latest = None;
    for index in 0..10_000 {
        let path = directory.join(format!("request-{index:04}.json"));
        if path.exists() {
            latest = Some(index);
        }
    }
    let Some(index) = latest else {
        return Ok(false);
    };
    let marker: Value = serde_json::from_slice(&bounded(
        &directory.join(format!("request-{index:04}.json")),
        4096,
    )?)
    .map_err(|error| format!("invalid retained request marker: {error}"))?;
    if marker.get("operation").and_then(Value::as_u64) != Some(21) {
        return Ok(false);
    }
    if marker.get("ingressSha256").and_then(Value::as_str)
        != Some(digest(&attempt.ingress).as_str())
        || marker.get("socket").and_then(Value::as_str) != Some(utf8_path(&attempt.socket)?)
    {
        return Err("retained lookup marker differs from exact ingress or selected socket".into());
    }
    let frame = bounded(
        &directory.join(format!("request-{index:04}.frame")),
        HOST_MAX_FRAME,
    )?;
    if frame.first() != Some(&21) {
        return Ok(false);
    }
    let binary = bounded(
        &directory.join(format!("request-{index:04}.bin")),
        HOST_MAX_FRAME - 1,
    )?;
    if frame[1..] != binary {
        return Err("retained lookup outcome differs from exact reply frame".into());
    }
    let binary_path = directory.join(format!("request-{index:04}.bin"));
    let mut inspection_path = None;
    for replay_index in 0..10_000 {
        let candidate = directory.join(format!(
            "request-{index:04}.reinspect-{replay_index:04}.json"
        ));
        if !candidate.exists() {
            inspection_path = Some(candidate);
            break;
        }
    }
    let inspection_path =
        inspection_path.ok_or("selected-release lookup exhausted reinspection names")?;
    // The cached JSON is only presentation. The pinned Lean Host must decode
    // the exact retained binary again at the moment a resubmit is authorized.
    let value = inspect_outcome(&binary_path, &inspection_path)?;
    Ok(value.get("type").and_then(Value::as_str) == Some("absent"))
}

fn latest_lookup_absent(directory: &Path, attempt: &Attempt) -> Result<bool> {
    latest_lookup_absent_with(directory, attempt, |binary, presentation| {
        inspect(
            &attempt.host,
            &attempt.config,
            "outcome",
            binary,
            presentation,
        )
    })
}

fn invoke(directory: &Path, attempt: &Attempt, operation: u8, stem: &str) -> Result<()> {
    let (marker_path, frame_path, outcome_path) = new_path(directory)?;
    // This marker precedes the call. If the reply is lost, no caller may infer
    // that Mini did not commit the exact ingress.
    let marker = json!({"operation":operation,"kind":stem,
        "ingressSha256":digest(&attempt.ingress),
        "socket":utf8_path(&attempt.socket)?});
    let mut marker_bytes = serde_json::to_vec(&marker).map_err(|e| e.to_string())?;
    marker_bytes.push(b'\n');
    create_private(&marker_path, &marker_bytes)?;
    sync_directory_ancestors(directory)?;
    let reply = transport::invoke_pinned(
        &attempt.socket,
        &attempt.config,
        &attempt.host_sha,
        operation,
        &attempt.ingress,
    )
    .map_err(|error| {
        format!("selected-release response uncertain; exact ingress retained: {error}")
    })?;
    create_private(&frame_path, &reply)?;
    sync_directory_ancestors(directory)?;
    if reply.first() == Some(&255) {
        return Err(format!(
            "Host refused selected release; exact refusal retained in {}",
            frame_path.display()
        ));
    }
    if reply.first() != Some(&operation) {
        return Err("selected-release reply operation mismatch; exact frame retained".into());
    }
    create_private(&outcome_path, &reply[1..])?;
    let json_path = outcome_path.with_extension("outcome.json");
    let value = inspect(
        &attempt.host,
        &attempt.config,
        "outcome",
        &outcome_path,
        &json_path,
    )?;
    print_json(&value)?;
    match value.get("type").and_then(Value::as_str) {
        Some("confirmed") => Ok(()),
        Some("absent") if operation == 21 => Ok(()),
        Some(other) => Err(format!(
            "selected-release {stem} returned {other}; exact outcome retained"
        )),
        None => Err("selected-release outcome lacks type; exact outcome retained".into()),
    }
}

pub(super) fn submit(
    host: &Path,
    config: &Path,
    socket: &Path,
    ingress: &Path,
    directory: &Path,
) -> Result<()> {
    let input = bounded(ingress, HOST_MAX_FRAME - 1)?;
    let config_bytes = bounded(config, 65_536)?;
    let host = absolute(host)?;
    let socket = absolute(socket)?;
    let directory = absolute(directory)?;
    let host_sha = host_image_sha256(&host)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|error| {
            format!(
                "cannot create private attempt {}: {error}",
                directory.display()
            )
        })?;
    let retained_config = directory.join("config.json");
    create_private(&retained_config, &config_bytes)?;
    create_private(&directory.join("ingress.bin"), &input)?;
    let manifest = json!({
        "format": FORMAT,
        "host": utf8_path(&host)?,
        "hostSha256": host_sha,
        "config": utf8_path(&retained_config)?,
        "configSha256": digest(&config_bytes),
        "socket": utf8_path(&socket)?,
        "ingressSha256": digest(&input),
        "operation": "selected-release-submit"
    });
    let mut manifest_bytes = serde_json::to_vec_pretty(&manifest).map_err(|e| e.to_string())?;
    manifest_bytes.push(b'\n');
    create_private(&directory.join("attempt.json"), &manifest_bytes)?;
    sync_directory_ancestors(&directory)?;
    let attempt = retained(&directory)?;
    invoke(&directory, &attempt, 20, "submit")
}

pub(super) fn lookup(directory: &Path, override_socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let mut attempt = retained(&directory)?;
    if let Some(socket) = override_socket {
        attempt.socket = absolute(socket)?;
    }
    invoke(&directory, &attempt, 21, "lookup")
}

pub(super) fn retry_submit(directory: &Path, override_socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let mut attempt = retained(&directory)?;
    if let Some(socket) = override_socket {
        attempt.socket = absolute(socket)?;
    }
    if !latest_lookup_absent(&directory, &attempt)? {
        return Err("exact selected-release resubmit requires a retained absent lookup".into());
    }
    invoke(&directory, &attempt, 20, "submit")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::net::UnixListener;
    use std::thread;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch() -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = PathBuf::from(format!("/tmp/sr-{}-{nonce}", std::process::id()));
        fs::create_dir(&path).unwrap();
        path
    }

    #[test]
    fn bounded_ingress_and_absent_gate() {
        let directory = scratch();
        let attempt = Attempt {
            host: directory.join("host"),
            config: directory.join("config"),
            socket: directory.join("socket"),
            host_sha: String::new(),
            ingress: b"exact".to_vec(),
        };
        let inspect_absent = |_: &Path, _: &Path| Ok(json!({"type":"absent"}));
        assert!(!latest_lookup_absent_with(&directory, &attempt, inspect_absent).unwrap());
        fs::write(directory.join("request-0000.json"), b"{\"operation\":20}").unwrap();
        assert!(!latest_lookup_absent_with(&directory, &attempt, inspect_absent).unwrap());
        fs::write(
            directory.join("request-0001.json"),
            serde_json::to_vec(&json!({
            "operation":21,"ingressSha256":digest(&attempt.ingress),
            "socket":attempt.socket.to_str().unwrap()}))
            .unwrap(),
        )
        .unwrap();
        fs::write(directory.join("request-0001.frame"), b"\x15outcome").unwrap();
        fs::write(directory.join("request-0001.bin"), b"outcome").unwrap();
        fs::write(
            directory.join("request-0001.outcome.json"),
            b"{\"type\":\"absent\"}",
        )
        .unwrap();
        assert!(latest_lookup_absent_with(&directory, &attempt, inspect_absent).unwrap());
        // A forged cached projection cannot authorize a retry when a fresh
        // source decode of the retained binary says confirmed.
        assert!(!latest_lookup_absent_with(&directory, &attempt, |_, _| Ok(
            json!({"type":"confirmed"})
        ))
        .unwrap());
        fs::write(directory.join("request-0002.json"), b"{\"operation\":20}").unwrap();
        assert!(!latest_lookup_absent_with(&directory, &attempt, inspect_absent).unwrap());
        fs::write(directory.join("ingress.bin"), b"").unwrap();
        assert!(bounded(&directory.join("ingress.bin"), 3).is_err());
        fs::write(directory.join("ingress.bin"), b"abcd").unwrap();
        assert!(bounded(&directory.join("ingress.bin"), 3).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn lost_or_mismatched_reply_keeps_exact_ingress_and_blocks_resubmit() {
        for response in [None, Some(21u8)] {
            let root = scratch();
            let host = root.join("host");
            let config = root.join("config.json");
            let ingress = root.join("source.bin");
            let socket = root.join("host.sock");
            let attempt = root.join("attempt");
            fs::write(&host, b"pinned-image").unwrap();
            fs::write(&config, b"{}\n").unwrap();
            fs::write(&ingress, b"host-authored-exact-ingress").unwrap();
            let listener = UnixListener::bind(&socket).unwrap();
            let peer = thread::spawn(move || {
                let (mut stream, _) = listener.accept().unwrap();
                let mut prefix = [0u8; 4];
                stream.read_exact(&mut prefix).unwrap();
                let mut request = vec![0; u32::from_le_bytes(prefix) as usize];
                stream.read_exact(&mut request).unwrap();
                assert!(request.ends_with(b"host-authored-exact-ingress"));
                if let Some(operation) = response {
                    stream.write_all(&1u32.to_le_bytes()).unwrap();
                    stream.write_all(&[operation]).unwrap();
                }
            });
            let error = submit(&host, &config, &socket, &ingress, &attempt).unwrap_err();
            assert!(error.contains("uncertain"), "{error}");
            peer.join().unwrap();
            assert_eq!(
                fs::read(attempt.join("ingress.bin")).unwrap(),
                b"host-authored-exact-ingress"
            );
            assert!(attempt.join("request-0000.json").exists());
            assert!(!latest_lookup_absent(&attempt, &retained(&attempt).unwrap()).unwrap());
            assert!(retry_submit(&attempt, None)
                .unwrap_err()
                .contains("absent lookup"));
            fs::write(attempt.join("ingress.bin"), b"changed").unwrap();
            assert!(retained(&attempt)
                .err()
                .unwrap()
                .contains("ingress or config changed"));
            fs::remove_dir_all(root).unwrap();
        }
    }
}
