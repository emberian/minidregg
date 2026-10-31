//! Exact native selected-release ingress transport. Lean authors and admits the
//! ingress; this module retains bytes and transports only the two Host opcodes.
use super::{
    absolute, create_private, hex, host_image_sha256, inspect, print_json,
    utf8_path, Result,
};
use crate::transport::{self, HOST_MAX_FRAME};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self};
use std::path::{Path, PathBuf};

const FORMAT: &str = "minidregg-selected-release-attempt-v1";

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
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
    let manifest_bytes = crate::fsio::read_bounded(&directory.join("attempt.json"), 65_536)?;
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
    let ingress = crate::fsio::read_bounded(&directory.join("ingress.bin"), HOST_MAX_FRAME - 1)?;
    let config_bytes = crate::fsio::read_bounded(&config, 65_536)?;
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


fn invoke(directory: &Path, attempt: &Attempt, operation: u8, stem: &str) -> Result<Value> {
    let (marker_path, frame_path, outcome_path) = new_path(directory)?;
    // This marker precedes the call. If the reply is lost, no caller may infer
    // that Mini did not commit the exact ingress.
    let marker = json!({"operation":operation,"kind":stem,
        "ingressSha256":digest(&attempt.ingress),
        "socket":utf8_path(&attempt.socket)?});
    let mut marker_bytes = serde_json::to_vec(&marker).map_err(|e| e.to_string())?;
    marker_bytes.push(b'\n');
    create_private(&marker_path, &marker_bytes)?;
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
    if reply.first().is_some_and(|b| crate::is_outcome_frame(*b)) {
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
        Some("confirmed") => Ok(value),
        Some("absent") if operation == 21 => Ok(value),
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
    let input = crate::fsio::read_bounded(ingress, HOST_MAX_FRAME - 1)?;
    let config_bytes = crate::fsio::read_bounded(config, 65_536)?;
    let host = absolute(host)?;
    let socket = absolute(socket)?;
    let directory = absolute(directory)?;
    let host_sha = host_image_sha256(&host)?;
    crate::fsio::create_private_dir(&directory)?;
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
    let attempt = retained(&directory)?;
    invoke(&directory, &attempt, mini_sdk::host_operations::SELECTED_RELEASE_SUBMIT, "submit").map(|_| ())
}

pub(super) fn lookup(directory: &Path, override_socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let mut attempt = retained(&directory)?;
    if let Some(socket) = override_socket {
        attempt.socket = absolute(socket)?;
    }
    invoke(&directory, &attempt, mini_sdk::host_operations::SELECTED_RELEASE_LOOKUP, "lookup").map(|_| ())
}

/// Whole-action recovery consumes the existing source-authorized absent gate.
/// A failed/uncertain lookup stops before dispatch; confirmed history is enough.
/// Absence allows only the same retained ingress, never a newly planned intent.
pub(super) fn recover(directory: &Path, override_socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let mut attempt = retained(&directory)?;
    if let Some(socket) = override_socket {
        attempt.socket = absolute(socket)?;
    }
    let lookup = invoke(&directory, &attempt, mini_sdk::host_operations::SELECTED_RELEASE_LOOKUP, "lookup")?;
    // invoke retains the exact reply frame and derives this outcome by the
    // pinned Host's native decoder. Reuse that checked value immediately;
    // cached presentation alone never authorizes a submit.
    if lookup["type"] == "absent" {
        invoke(&directory, &attempt, mini_sdk::host_operations::SELECTED_RELEASE_SUBMIT, "submit")?;
    }
    Ok(())
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
    fn bounded_ingress_reads_refuse_empty_and_oversized() {
        let directory = scratch();
        fs::write(directory.join("ingress.bin"), b"").unwrap();
        assert!(crate::fsio::read_bounded(&directory.join("ingress.bin"), 3).is_err());
        fs::write(directory.join("ingress.bin"), b"abcd").unwrap();
        assert!(crate::fsio::read_bounded(&directory.join("ingress.bin"), 3).is_err());
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
            // The exchange recovery consumer may look up unknown effects,
            // but losing that lookup reply must never trigger another submit.
            fs::remove_file(&socket).unwrap();
            let listener = UnixListener::bind(&socket).unwrap();
            let lookup_peer = thread::spawn(move || {
                let (mut stream, _) = listener.accept().unwrap();
                let mut prefix = [0u8; 4];
                stream.read_exact(&mut prefix).unwrap();
                let mut request = vec![0; u32::from_le_bytes(prefix) as usize];
                stream.read_exact(&mut request).unwrap();
                assert!(request.ends_with(b"host-authored-exact-ingress"));
            });
            assert!(recover(&attempt, None).unwrap_err().contains("uncertain"));
            lookup_peer.join().unwrap();
            let marker: Value = serde_json::from_slice(&fs::read(attempt.join("request-0001.json")).unwrap()).unwrap();
            assert_eq!(marker["operation"], 21);
            assert!(!attempt.join("request-0002.json").exists());
            assert_eq!(fs::read(attempt.join("ingress.bin")).unwrap(), b"host-authored-exact-ingress");
            fs::write(attempt.join("ingress.bin"), b"changed").unwrap();
            assert!(retained(&attempt)
                .err()
                .unwrap()
                .contains("ingress or config changed"));
            fs::remove_dir_all(root).unwrap();
        }
    }
}
