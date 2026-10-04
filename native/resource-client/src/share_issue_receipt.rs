//! Recipient-side historical share receipt. This route accepts only exact
//! source ingress, invokes the explicitly selected native read-only op29 or
//! op55, and retains its full reply.
//! It never imports the issuer's approval, signing plan, keys, or submit path.

use super::*;
use sha2::{Digest, Sha256};

const MAX_INGRESS: usize = transport::HOST_MAX_FRAME - 1;
const MAX_OUTCOME: usize = 65_536;
const MAX_CONFIG: usize = 65_536;

#[derive(Clone, Copy)]
enum IssueProfile {
    BareEvent15,
    GrainBackedEvent22,
}

impl IssueProfile {
    fn operation(self) -> u8 {
        match self {
            Self::BareEvent15 => 29,
            Self::GrainBackedEvent22 => 55,
        }
    }

    fn marker(self) -> &'static str {
        match self {
            Self::BareEvent15 => "minidregg-share-issue-recipient-lookup-v1",
            Self::GrainBackedEvent22 => "minidregg-grain-share-issue-recipient-lookup-v1",
        }
    }
}

fn decimal(value: &str, label: &str) -> Result<()> {
    if !mini_sdk::decimal::is_canonical_max(value, 80)
    {
        return Err(format!("share receipt {label} is not canonical decimal"));
    }
    Ok(())
}

fn exact_receipt(value: &Value, expected: [&str; 4]) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("confirmed")
        || value.get("confirmation").and_then(Value::as_str) != Some("replayed")
    {
        return Err("native share issue lookup has no historical receipt".into());
    }
    for (field, wanted) in ["transactionId", "eventId", "acceptedCount", "worldRoot"]
        .into_iter()
        .zip(expected)
    {
        decimal(wanted, field)?;
        if value.get(field).and_then(Value::as_str) != Some(wanted) {
            return Err(format!("native share issue historical {field} differs"));
        }
    }
    if expected[2] == "0" {
        return Err("share issue has no accepted transition".into());
    }
    Ok(())
}

fn invoke_profile(
    host: &Path,
    socket: &Path,
    config: &Path,
    ingress: &[u8],
    profile: IssueProfile,
) -> Result<Vec<u8>> {
    // The only native operation reachable from this recipient route is the
    // source-specific historical lookup. It cannot submit an issue.
    session_invoke(host, socket, config, profile.operation(), ingress)
}

fn invoke_lookup(host: &Path, socket: &Path, config: &Path, ingress: &[u8]) -> Result<Vec<u8>> {
    invoke_profile(host, socket, config, ingress, IssueProfile::BareEvent15)
}

fn inspect_direct(host: &Path, config: &Path, input: &Path, output: &Path) -> Result<Value> {
    // The broker may carry only the explicitly allowed lookup. Presentation is a
    // local, pinned Host operation over the retained exact reply bytes.
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
        .map_err(|error| format!("cannot inspect share issue outcome: {error}"))?;
    if !status.success() {
        return Err(format!(
            "pinned Host refused share issue outcome inspection: {status}"
        ));
    }
    serde_json::from_slice(&crate::fsio::read_bounded(output, MAX_OUTCOME)?)
        .map_err(|error| format!("share issue Host outcome JSON: {error}"))
}

pub(super) fn lookup(
    host: &Path,
    config: &Path,
    socket: &Path,
    ingress_path: &Path,
    expected: [&str; 4],
    directory: &Path,
) -> Result<()> {
    lookup_profile(
        host,
        config,
        socket,
        ingress_path,
        expected,
        directory,
        IssueProfile::BareEvent15,
    )
}

pub(super) fn lookup_grain(
    host: &Path,
    config: &Path,
    socket: &Path,
    ingress_path: &Path,
    expected: [&str; 4],
    directory: &Path,
) -> Result<()> {
    lookup_profile(
        host,
        config,
        socket,
        ingress_path,
        expected,
        directory,
        IssueProfile::GrainBackedEvent22,
    )
}

fn lookup_profile(
    host: &Path,
    config: &Path,
    socket: &Path,
    ingress_path: &Path,
    expected: [&str; 4],
    directory: &Path,
    profile: IssueProfile,
) -> Result<()> {
    if !host.is_absolute()
        || !config.is_absolute()
        || !socket.is_absolute()
        || !ingress_path.is_absolute()
        || !directory.is_absolute()
    {
        return Err("share issue receipt paths must be absolute".into());
    }
    for (field, wanted) in ["transactionId", "eventId", "acceptedCount", "worldRoot"]
        .into_iter()
        .zip(expected)
    {
        decimal(wanted, field)?;
    }
    if expected[2] == "0" || directory.exists() {
        return Err("share issue receipt destination exists or accepted count is zero".into());
    }
    let ingress = crate::fsio::read_bounded(ingress_path, MAX_INGRESS)?;
    let config_bytes = crate::fsio::read_bounded(config, MAX_CONFIG)?;
    let host_sha = host_image_sha256(host)?;
    crate::fsio::ensure_private_dir_durable(directory)?;
    create_private(&directory.join("ingress.bin"), &ingress)?;
    let marker = json!({"type":profile.marker(),
        "host":utf8_path(host)?,"hostSha256":host_sha,
        "config":utf8_path(config)?,
        "configSha256":hex(&Sha256::digest(&config_bytes)),
        "socket":utf8_path(socket)?,
        "ingressSha256":hex(&Sha256::digest(&ingress)),
        "expected":{"transactionId":expected[0],"eventId":expected[1],
            "acceptedCount":expected[2],"worldRoot":expected[3]}});
    create_private(
        &directory.join("lookup-marker.json"),
        &serde_json::to_vec_pretty(&marker).map_err(|error| error.to_string())?,
    )?;
    sync_directory_ancestors(directory)?;

    // A lost reply leaves the marker and exact ingress. The caller may issue
    // another *read-only* lookup in a fresh directory; no submission exists.
    let frame = match profile {
        IssueProfile::BareEvent15 => invoke_lookup(host, socket, config, &ingress)?,
        IssueProfile::GrainBackedEvent22 => {
            invoke_profile(host, socket, config, &ingress, profile)?
        }
    };
    create_private(&directory.join("reply.frame"), &frame)?;
    sync_directory_ancestors(directory)?;
    if host_image_sha256(host)? != host_sha
        || crate::fsio::read_bounded(config, MAX_CONFIG)? != config_bytes
        || crate::fsio::read_bounded(&directory.join("ingress.bin"), MAX_INGRESS)? != ingress
    {
        return Err(format!(
            "share issue Host, config, or exact ingress changed after op{}",
            profile.operation()
        ));
    }
    let [actual, body @ ..] = frame.as_slice() else {
        return Err("share issue lookup returned malformed reply; frame retained".into());
    };
    if *actual != profile.operation() {
        return Err(format!(
            "share issue op{} returned wrong reply operation; frame retained",
            profile.operation()
        ));
    }
    if body.is_empty() || body.len() > MAX_OUTCOME {
        return Err(format!(
            "share issue op{} outcome size is outside profile; frame retained",
            profile.operation()
        ));
    }
    let binary = directory.join("outcome.bin");
    create_private(&binary, body)?;
    sync_directory_ancestors(directory)?;
    let json_path = directory.join("outcome.json");
    let outcome = inspect_direct(host, config, &binary, &json_path)?;
    let retained: Value = serde_json::from_slice(&crate::fsio::read_bounded(&json_path, MAX_OUTCOME)?)
        .map_err(|error| format!("share issue Host outcome JSON: {error}"))?;
    if retained != outcome {
        return Err("share issue Host outcome changed after inspection".into());
    }
    if host_image_sha256(host)? != host_sha
        || crate::fsio::read_bounded(config, MAX_CONFIG)? != config_bytes
        || crate::fsio::read_bounded(&directory.join("ingress.bin"), MAX_INGRESS)? != ingress
    {
        return Err("share issue Host, config, or exact ingress changed after inspection".into());
    }
    exact_receipt(&outcome, expected)?;
    print_json(&outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::net::UnixListener;

    #[test]
    fn receipt_requires_native_replay_and_all_four_exact_fields() {
        let accepted = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        exact_receipt(&accepted, ["1", "2", "3", "4"]).unwrap();
        for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            let mut tampered = accepted.clone();
            tampered[field] = json!("9");
            assert!(exact_receipt(&tampered, ["1", "2", "3", "4"]).is_err());
        }
        let mut wrong = accepted;
        wrong["confirmation"] = json!("installed");
        assert!(exact_receipt(&wrong, ["1", "2", "3", "4"]).is_err());
    }

    #[test]
    fn decimal_pins_reject_noncanonical_values() {
        for bad in ["", "01", "-1", "1 ", "+1"] {
            assert!(decimal(bad, "transactionId").is_err());
        }
    }

    #[test]
    fn transport_sends_only_op29_with_exact_ingress_over_pinned_socket() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = PathBuf::from(format!("/tmp/msr-{}-{unique:x}", std::process::id()));
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
            let mut envelope = vec![0u8; u32::from_le_bytes(length) as usize];
            stream.read_exact(&mut envelope).unwrap();
            assert_eq!(envelope[0], 2);
            let config_len = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
            assert_eq!(&envelope[5..5 + config_len], b"pinned config");
            let operation = 5 + config_len + 32;
            assert_eq!(envelope[operation], 29);
            assert_eq!(&envelope[operation + 1..], b"exact signed issue ingress");
            let reply = [29u8, 1, 2];
            stream
                .write_all(&(reply.len() as u32).to_le_bytes())
                .unwrap();
            stream.write_all(&reply).unwrap();
        });
        assert_eq!(
            invoke_lookup(&host, &socket, &config, b"exact signed issue ingress").unwrap(),
            vec![29, 1, 2]
        );
        worker.join().unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn grain_recipient_profile_sends_only_op55_with_exact_ingress() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = PathBuf::from(format!("/tmp/msr-grain-{}-{unique:x}", std::process::id()));
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
            let mut envelope = vec![0u8; u32::from_le_bytes(length) as usize];
            stream.read_exact(&mut envelope).unwrap();
            let config_len = u32::from_le_bytes(envelope[1..5].try_into().unwrap()) as usize;
            let operation = 5 + config_len + 32;
            assert_eq!(envelope[operation], 55);
            assert_eq!(&envelope[operation + 1..], b"exact grain issue ingress");
            let reply = [55u8, 1, 2];
            stream
                .write_all(&(reply.len() as u32).to_le_bytes())
                .unwrap();
            stream.write_all(&reply).unwrap();
        });
        assert_eq!(
            invoke_profile(
                &host,
                &socket,
                &config,
                b"exact grain issue ingress",
                IssueProfile::GrainBackedEvent22
            )
            .unwrap(),
            vec![55, 1, 2]
        );
        worker.join().unwrap();
        fs::remove_dir_all(root).unwrap();
    }
}
