//! Recipient-side exact historical call lookup. The original issuer's
//! attempt manifest, custody key and config are neither loaded nor copied.
//! This confirms an accepted signed call through native op3 only; it does
//! not classify the call as an application birth or authorize current use.

use super::*;
use sha2::{Digest, Sha256};
use std::io::Read;

const MAX_CALL: usize = transport::HOST_MAX_FRAME - 1;
const MAX_CONFIG: usize = 65_536;
const MAX_OUTCOME: usize = 65_536;

fn bounded(path: &Path, maximum: usize) -> Result<Vec<u8>> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| format!("{}: {error}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() == 0 || metadata.len() > maximum as u64 {
        return Err(format!("{} must be a bounded regular file", path.display()));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|error| format!("{}: {error}", path.display()))?
        .take((maximum + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("{}: {error}", path.display()))?;
    if bytes.len() != metadata.len() as usize || bytes.len() > maximum {
        return Err(format!("{} changed during bounded read", path.display()));
    }
    Ok(bytes)
}


fn exact_receipt(value: &Value, expected: [&str; 4]) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("confirmed")
        || value.get("confirmation").and_then(Value::as_str) != Some("replayed")
    {
        return Err("native exact call lookup has no historical replayed receipt".into());
    }
    for (field, wanted) in ["transactionId", "eventId", "acceptedCount", "worldRoot"]
        .into_iter()
        .zip(expected)
    {
        if !mini_sdk::decimal::is_canonical_max(wanted, 80) || value.get(field).and_then(Value::as_str) != Some(wanted) {
            return Err(format!("native exact call historical {field} differs"));
        }
    }
    if expected[2] == "0" {
        return Err("historical call has no accepted transition".into());
    }
    Ok(())
}

fn invoke_lookup(host: &Path, socket: &Path, config: &Path, call: &[u8]) -> Result<Vec<u8>> {
    session_invoke(host, socket, config, 3, call)
}

fn inspect_direct(host: &Path, config: &Path, input: &Path, output: &Path) -> Result<Value> {
    let status = Command::new(host)
        .arg(config)
        .arg("inspect")
        .arg("outcome")
        .arg(input)
        .arg(output)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map_err(|error| format!("cannot inspect exact call outcome: {error}"))?;
    if !status.success() {
        return Err(format!(
            "pinned Host refused exact call outcome inspection: {status}"
        ));
    }
    serde_json::from_slice(&bounded(output, MAX_OUTCOME)?)
        .map_err(|error| format!("historical call Host outcome JSON: {error}"))
}

pub(super) fn lookup(
    host: &Path,
    config: &Path,
    socket: &Path,
    call_path: &Path,
    expected: [&str; 4],
    directory: &Path,
) -> Result<()> {
    print_json(&lookup_verified(
        host, config, socket, call_path, expected, directory,
    )?)
}

pub(super) fn lookup_verified(
    host: &Path,
    config: &Path,
    socket: &Path,
    call_path: &Path,
    expected: [&str; 4],
    directory: &Path,
) -> Result<Value> {
    if !host.is_absolute()
        || !config.is_absolute()
        || !socket.is_absolute()
        || !call_path.is_absolute()
        || !directory.is_absolute()
    {
        return Err("historical call receipt paths must be absolute".into());
    }
    if directory.exists()
        || expected[2] == "0"
        || expected.iter().any(|value| !mini_sdk::decimal::is_canonical_max(value, 80))
    {
        return Err("historical call receipt destination or expected fields are invalid".into());
    }
    let call = bounded(call_path, MAX_CALL)?;
    let config_bytes = bounded(config, MAX_CONFIG)?;
    let host_sha = host_image_sha256(host)?;
    drain::private_dir(directory)?;
    create_private(&directory.join("call.bin"), &call)?;
    let marker = json!({"type":"minidregg-recipient-historical-call-lookup-v1",
        "host":utf8_path(host)?,"hostSha256":host_sha,
        "config":utf8_path(config)?,"configSha256":hex(&Sha256::digest(&config_bytes)),
        "socket":utf8_path(socket)?,"callSha256":hex(&Sha256::digest(&call)),
        "expected":{"transactionId":expected[0],"eventId":expected[1],
            "acceptedCount":expected[2],"worldRoot":expected[3]}});
    create_private(
        &directory.join("lookup-marker.json"),
        &serde_json::to_vec_pretty(&marker).map_err(|error| error.to_string())?,
    )?;
    sync_directory_ancestors(directory)?;

    let frame = invoke_lookup(host, socket, config, &call)?;
    create_private(&directory.join("reply.frame"), &frame)?;
    sync_directory_ancestors(directory)?;
    if host_image_sha256(host)? != host_sha
        || bounded(config, MAX_CONFIG)? != config_bytes
        || bounded(&directory.join("call.bin"), MAX_CALL)? != call
    {
        return Err("historical call Host, config or exact call changed after op3".into());
    }
    let [3, body @ ..] = frame.as_slice() else {
        return Err("historical call op3 returned wrong reply operation; frame retained".into());
    };
    if body.is_empty() || body.len() > MAX_OUTCOME {
        return Err("historical call op3 outcome size is outside profile; frame retained".into());
    }
    let binary = directory.join("outcome.bin");
    create_private(&binary, body)?;
    sync_directory_ancestors(directory)?;
    let json_path = directory.join("outcome.json");
    let outcome = inspect_direct(host, config, &binary, &json_path)?;
    let retained: Value = serde_json::from_slice(&bounded(&json_path, MAX_OUTCOME)?)
        .map_err(|error| format!("historical call retained JSON: {error}"))?;
    if retained != outcome
        || host_image_sha256(host)? != host_sha
        || bounded(config, MAX_CONFIG)? != config_bytes
        || bounded(&directory.join("call.bin"), MAX_CALL)? != call
    {
        return Err("historical call Host, config, input or inspection changed".into());
    }
    exact_receipt(&outcome, expected)?;
    Ok(outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::net::UnixListener;

    #[test]
    fn ordinary_native_op3_lookup_carries_exact_original_call() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = PathBuf::from(format!("/tmp/mcr-{}-{unique:x}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let host = root.join("host");
        let config = root.join("config.json");
        let socket = root.join("public.sock");
        fs::write(&host, b"pinned host image").unwrap();
        fs::write(&config, b"pinned config").unwrap();
        let listener = UnixListener::bind(&socket).unwrap();
        let worker = std::thread::spawn(move || {
            let (mut stream, _) = listener.accept().unwrap();
            let mut length = [0u8; 4];
            stream.read_exact(&mut length).unwrap();
            let mut envelope = vec![0; u32::from_le_bytes(length) as usize];
            stream.read_exact(&mut envelope).unwrap();
            assert_eq!(envelope[0], 2);
            let config_len = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
            assert_eq!(&envelope[5..5 + config_len], b"pinned config");
            let operation = 5 + config_len + 32;
            assert_eq!(envelope[operation], 3);
            assert_eq!(
                &envelope[operation + 1..],
                b"exact accepted composite app birth call"
            );
            let reply = [3u8, 1, 2];
            stream
                .write_all(&(reply.len() as u32).to_le_bytes())
                .unwrap();
            stream.write_all(&reply).unwrap();
        });
        assert_eq!(
            invoke_lookup(
                &host,
                &socket,
                &config,
                b"exact accepted composite app birth call"
            )
            .unwrap(),
            vec![3, 1, 2]
        );
        worker.join().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn replayed_receipt_must_match_all_fields() {
        let valid = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        exact_receipt(&valid, ["1", "2", "3", "4"]).unwrap();
        for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            let mut wrong = valid.clone();
            wrong[field] = json!("8");
            assert!(exact_receipt(&wrong, ["1", "2", "3", "4"]).is_err());
        }
        let mut not_replayed = valid;
        not_replayed["confirmation"] = json!("installed");
        assert!(exact_receipt(&not_replayed, ["1", "2", "3", "4"]).is_err());
        assert!(exact_receipt(&not_replayed, ["01", "2", "3", "4"]).is_err());
    }
}
