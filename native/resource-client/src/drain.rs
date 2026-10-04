//! One bounded B consumer wake. All policy decisions and calls come from Host/Main.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
use std::process::Stdio;
use std::time::{Duration, Instant};

fn file_digest(path: &Path) -> Result<String> {
    let mut input = File::open(path).map_err(|e| format!("cannot open {}: {e}", path.display()))?;
    let mut digest = Sha256::new();
    let mut buffer = [0u8; 64 * 1024];
    loop {
        let count = input
            .read(&mut buffer)
            .map_err(|e| format!("cannot hash {}: {e}", path.display()))?;
        if count == 0 {
            return Ok(hex(&digest.finalize()));
        }
        digest.update(&buffer[..count]);
    }
}

fn bounded_catalog_digest(path: &Path, limit: u64) -> Result<String> {
    let meta = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot inspect A catalog input {}: {e}", path.display()))?;
    if !meta.is_file() || meta.len() == 0 || meta.len() > limit {
        return Err(format!(
            "A catalog input {} is not a bounded regular file",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| format!("cannot open A catalog input {}: {e}", path.display()))?
        .take(limit + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read A catalog input {}: {e}", path.display()))?;
    if bytes.is_empty() || bytes.len() as u64 > limit {
        return Err(format!(
            "A catalog input {} changed or exceeds its bound",
            path.display()
        ));
    }
    Ok(hex(&Sha256::digest(&bytes)))
}

pub(super) struct HostUpgrade {
    pub old_host: PathBuf,
    pub new_host: PathBuf,
    pub new_host_sha: String,
    pub socket: PathBuf,
    pub config_bytes: Vec<u8>,
    pub call_bytes: Vec<u8>,
    pub call_sha: String,
    pub evidence_path: PathBuf,
    pub evidence_sha: String,
    pub expected_fields: Value,
}

fn confirmed_fields(value: &Value) -> Result<Value> {
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Err("host upgrade lookup is not confirmed".into());
    }
    let mut fields = serde_json::Map::new();
    for name in ["acceptedCount", "transactionId", "eventId", "worldRoot"] {
        let field = value
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("confirmed outcome lacks {name}"))?;
        if field.is_empty()
            || field.len() > 80
            || !field.bytes().all(|b| b.is_ascii_digit())
            || (field.len() > 1 && field.starts_with('0'))
        {
            return Err(format!("confirmed outcome has noncanonical {name}"));
        }
        fields.insert(name.into(), json!(field));
    }
    Ok(Value::Object(fields))
}

fn require_upgraded_receipt(lookup: &Value, expected: &Value) -> Result<()> {
    if confirmed_fields(lookup)? != *expected {
        return Err("upgraded lookup confirmed a different four-field receipt".into());
    }
    Ok(())
}

fn direct_host(host: &Path, config: &Path, args: &[&Path]) -> Result<()> {
    let mut child = std::process::Command::new(host)
        .arg(config)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| format!("cannot start read-only host {}: {e}", host.display()))?;
    let deadline = Instant::now() + Duration::from_secs(180);
    loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|e| format!("cannot wait for read-only host: {e}"))?
        {
            return if status.success() {
                Ok(())
            } else {
                Err(format!(
                    "read-only host exited {status}; retained read-only outputs require review"
                ))
            };
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return Err("read-only host exceeded 180-second migration deadline".into());
        }
        std::thread::sleep(Duration::from_millis(100));
    }
}

fn canonical_sha(value: &str) -> bool {
    value.len() == 64
        && mini_sdk::hex::is_lower(value)
}

pub(super) fn private_dir(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => sync_directory_ancestors(path)?,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(format!("cannot create {}: {error}", path.display())),
    }
    let meta = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
    if !meta.is_dir()
        || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err(format!(
            "{} must be an owner-private directory",
            path.display()
        ));
    }
    Ok(())
}

unsafe extern "C" {
    fn geteuid() -> u32;
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(
        &fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?,
    )
    .map_err(|error| format!("invalid {}: {error}", path.display()))
}

fn save_state(pending: &Path, state: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(state).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    crate::fsio::replace_private(&pending.join("state.json"), &bytes)
        .map_err(|e| format!("cannot replace durable worker state: {e}"))?;
    sync_directory_ancestors(pending)
}

fn field<'a>(state: &'a Value, name: &str) -> Result<&'a str> {
    state
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("worker state lacks {name}"))
}

fn number(state: &Value, name: &str) -> Result<u64> {
    state
        .get(name)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("worker state lacks {name}"))
}

fn set(state: &mut Value, name: &str, value: Value) {
    state[name] = value;
}

fn attempt(pending: &Path, state: &mut Value, label: &str) -> Result<PathBuf> {
    let serial = number(state, "serial")?
        .checked_add(1)
        .ok_or("worker serial overflow")?;
    set(state, "serial", json!(serial));
    let name = format!("{label}-{serial:08}");
    set(state, label, json!(name));
    save_state(pending, state)?;
    Ok(pending.join(name))
}

fn pin_identity(host: &Path, config: &Path, socket: &Path, key: &Path) -> Result<Value> {
    let config_bytes =
        fs::read(config).map_err(|e| format!("cannot read fn operator config: {e}"))?;
    let public_key = read_secret(key)?.verifying_key().to_bytes();
    Ok(json!({
        "type":"minidregg-b-consumer-worker-pin-v1",
        "host":utf8_path(&absolute(host)?)?, "configPath":utf8_path(&absolute(config)?)?,
        "configHex":hex(&config_bytes), "socket":utf8_path(&absolute(socket)?)?,
        "keyPath":utf8_path(&absolute(key)?)?, "publicKey":hex(&public_key)
    }))
}

fn manifest_digests(config: &Path) -> Result<Value> {
    let value: Value = serde_json::from_slice(&fs::read(config).map_err(|e| e.to_string())?)
        .map_err(|e| format!("invalid fn operator config: {e}"))?;
    let mut digests = serde_json::Map::new();
    if let Some(poll) = value.get("fnPoll") {
        for name in ["originConfigPath", "fnPinPath", "scopePath", "policyPath"] {
            let path = poll
                .get(name)
                .and_then(Value::as_str)
                .ok_or_else(|| format!("fnPoll lacks {name}"))?;
            digests.insert(name.to_owned(), json!(file_digest(Path::new(path))?));
        }
    }
    Ok(Value::Object(digests))
}

fn v2_pin(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    evidence_path: Option<&str>,
    evidence_sha: Option<&str>,
) -> Result<Value> {
    let mut value = pin_identity(host, config, socket, key)?;
    value["type"] = json!("minidregg-b-consumer-worker-pin-v2");
    value["hostSha256"] = json!(file_digest(host)?);
    value["manifestSha256"] = manifest_digests(config)?;
    value["upgradeEvidencePath"] = json!(evidence_path);
    value["upgradeEvidenceSha256"] = json!(evidence_sha);
    Ok(value)
}

/// One version-aware physical pin contract for both ordinary startup and
/// the final host-upgrade recheck. Older pins are not rewritten as newer ones.
fn expected_pin(
    retained: &Value,
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
) -> Result<Value> {
    Ok(match retained.get("type").and_then(Value::as_str) {
        Some("minidregg-b-consumer-worker-pin-v1") => pin_identity(host, config, socket, key)?,
        Some("minidregg-b-consumer-worker-pin-v2") => {
            let evidence_path = retained.get("upgradeEvidencePath").and_then(Value::as_str);
            let evidence_sha = retained
                .get("upgradeEvidenceSha256")
                .and_then(Value::as_str);
            if evidence_path.is_some() != evidence_sha.is_some() {
                return Err("consumer host upgrade evidence is incomplete".into());
            }
            if let (Some(path), Some(sha)) = (evidence_path, evidence_sha) {
                if !canonical_sha(sha) || file_digest(Path::new(path))? != sha {
                    return Err("consumer host upgrade evidence changed".into());
                }
                let evidence = read_json(Path::new(path))?;
                let old_pin_path = field(&evidence, "oldPinPath")?;
                let old_pin_sha = field(&evidence, "oldPinSha256")?;
                if evidence.get("type").and_then(Value::as_str)
                    != Some("minidregg-b-consumer-host-upgrade-v1")
                    || !canonical_sha(old_pin_sha)
                    || file_digest(Path::new(old_pin_path))? != old_pin_sha
                {
                    return Err("consumer previous worker pin evidence changed".into());
                }
            }
            v2_pin(host, config, socket, key, evidence_path, evidence_sha)?
        }
        _ => return Err("consumer worker pin has unsupported version".into()),
    })
}

pub(super) fn pin(
    state_dir: &Path,
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
) -> Result<()> {
    let path = state_dir.join("pin.json");
    if path.exists() {
        let retained = read_json(&path)?;
        let expected = expected_pin(&retained, host, config, socket, key)?;
        if retained != expected {
            return Err(
                "consumer worker pin changed; retain old state for operator review".to_owned(),
            );
        }
    } else {
        let value = v2_pin(host, config, socket, key, None, None)?;
        write_json_new(&path, &value)?;
        sync_directory_ancestors(state_dir)?;
    }
    Ok(())
}

fn a_reply_pin_identity(host: &Path, config: &Path, socket: &Path, key: &Path) -> Result<Value> {
    let config_bytes =
        fs::read(config).map_err(|e| format!("cannot read A operator config: {e}"))?;
    let config_json: Value = serde_json::from_slice(&config_bytes)
        .map_err(|e| format!("invalid A operator config: {e}"))?;
    let catalog = config_json
        .get("fnReplyCatalog")
        .and_then(Value::as_object)
        .ok_or("A reply worker requires fnReplyCatalog")?;
    if config_json
        .get("fnPoll")
        .is_some_and(|value| !value.is_null())
        || config_json
            .get("fnReplyPoll")
            .is_some_and(|value| !value.is_null())
    {
        return Err("A catalog worker config contains another consumer route".into());
    }
    let mut manifests = serde_json::Map::new();
    for name in [
        "originConfigPath",
        "rPinPath",
        "qPinPath",
        "scopePath",
        "policyPath",
    ] {
        let path = catalog
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("fnReplyCatalog lacks {name}"))?;
        let path = Path::new(path);
        if !path.is_absolute() {
            return Err(format!("fnReplyCatalog {name} is not absolute"));
        }
        let bound = if name == "originConfigPath" {
            65_536
        } else {
            8_192
        };
        manifests.insert(name.to_owned(), json!(bounded_catalog_digest(path, bound)?));
    }
    let control_path = catalog
        .get("controlPath")
        .and_then(Value::as_str)
        .ok_or("fnReplyCatalog lacks controlPath")?;
    if !Path::new(control_path).is_absolute() {
        return Err("fnReplyCatalog controlPath is not absolute".into());
    }
    let public_key = read_secret(key)?.verifying_key().to_bytes();
    Ok(json!({
        "type":"minidregg-a-reply-consumer-worker-pin-v2", "route":"a-reply",
        "host":utf8_path(&absolute(host)?)?, "hostSha256":file_digest(host)?,
        "configPath":utf8_path(&absolute(config)?)?, "configHex":hex(&config_bytes),
        "socket":utf8_path(&absolute(socket)?)?, "keyPath":utf8_path(&absolute(key)?)?,
        "publicKey":hex(&public_key), "manifestSha256":Value::Object(manifests),
        "controlPath":control_path
    }))
}

pub(super) fn pin_route(
    state_dir: &Path,
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    route: ConsumerRoute,
) -> Result<()> {
    if !route.reply {
        return pin(state_dir, host, config, socket, key);
    }
    let expected = a_reply_pin_identity(host, config, socket, key)?;
    let path = state_dir.join("pin.json");
    if path.exists() {
        if read_json(&path)? != expected {
            return Err("A reply worker route or durable pin changed".into());
        }
    } else {
        write_json_new(&path, &expected)?;
        sync_directory_ancestors(state_dir)?;
    }
    Ok(())
}

fn load_upgrade(
    state_dir: &Path,
    pending: &Path,
    state: &Value,
    host: &Path,
) -> Result<Option<HostUpgrade>> {
    if field(state, "phase")? != "Sending" {
        return Ok(None);
    }
    let pin = read_json(&state_dir.join("pin.json"))?;
    let Some(evidence_path) = pin.get("upgradeEvidencePath").and_then(Value::as_str) else {
        return Ok(None);
    };
    let evidence_path = PathBuf::from(evidence_path);
    let evidence_sha = pin
        .get("upgradeEvidenceSha256")
        .and_then(Value::as_str)
        .ok_or("upgraded pin lacks evidence digest")?
        .to_owned();
    if file_digest(&evidence_path)? != evidence_sha {
        return Err("host upgrade evidence digest changed".into());
    }
    let evidence = read_json(&evidence_path)?;
    let prepare = pending.join(field(state, "prepare")?);
    let (manifest_host, manifest_config, manifest_socket) = manifest_paths(&prepare)?;
    let new_host = PathBuf::from(field(&evidence, "newHost")?);
    let old_host = PathBuf::from(field(&evidence, "oldHost")?);
    let socket = PathBuf::from(field(&evidence, "socket")?);
    let config = PathBuf::from(field(&evidence, "configPath")?);
    let config_bytes = fs::read(&config).map_err(|e| e.to_string())?;
    if hex(&Sha256::digest(&config_bytes)) != field(&evidence, "configSha256")? {
        return Err("host upgrade config bytes changed".into());
    }
    if manifest_config != prepare.join("config.json")
        || fs::read(&manifest_config).map_err(|e| e.to_string())? != config_bytes
        || manifest_socket.as_deref() != Some(socket.as_path())
    {
        return Err("Sending attempt config or socket differs from upgraded worker pin".into());
    }
    if manifest_host == new_host {
        // A new attempt belongs to the upgraded image. The migration binds only
        // the old retained call, even if a new wake reuses prepare-00000002.
        return Ok(None);
    }
    if manifest_host != old_host {
        return Err("Sending attempt host is neither original nor upgraded image".into());
    }
    if field(&evidence, "attemptConfigPath")? != utf8_path(&manifest_config)?
        || field(&evidence, "attemptConfigSha256")? != file_digest(&manifest_config)?
    {
        return Err("host upgrade does not bind original attempt config snapshot".into());
    }
    let call_bytes = fs::read(prepare.join("call.bin")).map_err(|e| e.to_string())?;
    let call_sha = hex(&Sha256::digest(&call_bytes));
    let new_host_sha = field(&evidence, "newHostSha256")?.to_owned();
    if field(&evidence, "prepare")? != field(state, "prepare")?
        || field(&evidence, "callSha256")? != call_sha
        || new_host != absolute(host)?
        || file_digest(&new_host)? != new_host_sha
        || file_digest(&old_host)? != field(&evidence, "oldHostSha256")?
    {
        return Err("host upgrade no longer binds retained Sending call and images".into());
    }
    let expected_fields = evidence
        .get("confirmedFields")
        .cloned()
        .ok_or("host upgrade evidence lacks original confirmed receipt")?;
    if expected_fields.get("transactionId").is_none()
        || expected_fields.as_object().is_none_or(|m| m.len() != 4)
    {
        return Err("host upgrade evidence has malformed confirmed receipt".into());
    }
    Ok(Some(HostUpgrade {
        old_host,
        new_host,
        new_host_sha,
        socket,
        config_bytes,
        call_bytes,
        call_sha,
        evidence_path,
        evidence_sha,
        expected_fields,
    }))
}

pub(super) struct UpgradeRequest<'a> {
    pub old_host: &'a Path,
    pub new_host: &'a Path,
    pub config: &'a Path,
    pub socket: &'a Path,
    pub key: &'a Path,
    pub state_dir: &'a Path,
    pub known_outcome: &'a Path,
    pub old_sha: &'a str,
    pub new_sha: &'a str,
    pub known_sha: &'a str,
}

pub(super) fn upgrade_host(request: UpgradeRequest<'_>) -> Result<()> {
    let UpgradeRequest {
        old_host,
        new_host,
        config,
        socket,
        key,
        state_dir,
        known_outcome,
        old_sha,
        new_sha,
        known_sha,
    } = request;
    for (label, sha) in [
        ("old", old_sha),
        ("new", new_sha),
        ("known outcome", known_sha),
    ] {
        if !canonical_sha(sha) {
            return Err(format!("{label} SHA-256 must be canonical lowercase hex"));
        }
    }
    private_dir(state_dir)?;
    let socket_dir = socket.parent().ok_or("socket lacks parent")?;
    private_dir(socket_dir)?;
    let _service = transport::service_lock(&socket.with_extension("lock"))?;
    let _global = transport::service_lock(&socket_dir.join("consumer-worker.lock"))?;
    let _worker = transport::service_lock(&state_dir.join("worker.lock"))?;
    let old_host = absolute(old_host)?;
    let new_host = absolute(new_host)?;
    let config = absolute(config)?;
    let socket = absolute(socket)?;
    let key = absolute(key)?;
    if old_host == new_host
        || file_digest(&old_host)? != old_sha
        || file_digest(&new_host)? != new_sha
    {
        return Err("host upgrade image paths or operator-provided digests disagree".into());
    }
    let pin_path = state_dir.join("pin.json");
    if !pin_path.is_file() {
        return Err("host upgrade requires an existing durable worker pin".into());
    }
    if read_json(&pin_path)?.get("type").and_then(Value::as_str)
        == Some("minidregg-a-reply-consumer-worker-pin-v2")
    {
        return Err(
            "A reply worker host upgrade is not supported; retain its original image and pending state for operator review"
                .into(),
        );
    }
    pin(state_dir, &old_host, &config, &socket, &key)?;
    let old_pin_bytes = fs::read(&pin_path).map_err(|e| e.to_string())?;
    let old_pin_sha = hex(&Sha256::digest(&old_pin_bytes));
    let old_pin: Value = serde_json::from_slice(&old_pin_bytes).map_err(|e| e.to_string())?;
    let old_pin_type = field(&old_pin, "type")?.to_owned();
    let pending = state_dir.join("pending");
    private_dir(&pending)?;
    let state = read_json(&pending.join("state.json"))?;
    if field(&state, "phase")? != "Sending" {
        return Err("host upgrade requires the exact pending Sending phase".into());
    }
    let prepare_name = field(&state, "prepare")?;
    let prepare = pending.join(prepare_name);
    let call = prepare.join("call.bin");
    sync_retained_call(&prepare, &call)?;
    let (manifest_host, manifest_config, manifest_socket) = manifest_paths(&prepare)?;
    let config_bytes = fs::read(&config).map_err(|e| e.to_string())?;
    if manifest_host != old_host
        || manifest_config != prepare.join("config.json")
        || fs::read(&manifest_config).map_err(|e| e.to_string())? != config_bytes
        || manifest_socket.as_deref() != Some(socket.as_path())
    {
        return Err("pending attempt manifest differs from existing worker pin".into());
    }
    let call_sha = file_digest(&call)?;
    if file_digest(known_outcome)? != known_sha {
        return Err("known confirmed outcome digest differs from operator assertion".into());
    }
    let config_sha = hex(&Sha256::digest(&config_bytes));
    let original_manifests = manifest_digests(&config)?;
    let mut upgrade_dir = None;
    for index in 1..=999 {
        let path = state_dir.join(format!("host-upgrade-{index:03}"));
        if !path.exists() {
            upgrade_dir = Some(path);
            break;
        }
    }
    let upgrade_dir = upgrade_dir.ok_or("exhausted host upgrade evidence names")?;
    private_dir(&upgrade_dir)?;
    create_private(&upgrade_dir.join("old-pin.json"), &old_pin_bytes)?;
    if file_digest(&upgrade_dir.join("old-pin.json"))? != old_pin_sha {
        return Err("retained old worker pin differs from pre-upgrade digest".into());
    }
    create_private(
        &upgrade_dir.join("known-outcome.bin"),
        &fs::read(known_outcome).map_err(|e| e.to_string())?,
    )?;
    sync_directory_ancestors(&upgrade_dir)?;
    direct_host(
        &new_host,
        &config,
        &[
            Path::new("inspect"),
            Path::new("outcome"),
            &upgrade_dir.join("known-outcome.bin"),
            &upgrade_dir.join("known-outcome.json"),
        ],
    )?;
    direct_host(
        &new_host,
        &config,
        &[Path::new("lookup"), &call, &upgrade_dir.join("lookup.bin")],
    )?;
    direct_host(
        &new_host,
        &config,
        &[
            Path::new("inspect"),
            Path::new("outcome"),
            &upgrade_dir.join("lookup.bin"),
            &upgrade_dir.join("lookup.json"),
        ],
    )?;
    for name in ["known-outcome.json", "lookup.bin", "lookup.json"] {
        File::open(upgrade_dir.join(name))
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
    }
    sync_directory_ancestors(&upgrade_dir)?;
    let known = confirmed_fields(&read_json(&upgrade_dir.join("known-outcome.json"))?)?;
    let fresh = confirmed_fields(&read_json(&upgrade_dir.join("lookup.json"))?)?;
    if known != fresh {
        return Err(
            "new host lookup does not match all four original confirmed receipt fields".into(),
        );
    }
    if expected_pin(&old_pin, &old_host, &config, &socket, &key)? != old_pin
        || file_digest(&old_host)? != old_sha
        || file_digest(&new_host)? != new_sha
        || file_digest(&upgrade_dir.join("known-outcome.bin"))? != known_sha
        || manifest_digests(&config)? != original_manifests
    {
        return Err("host upgrade inputs changed during read-only lookup".into());
    }
    let evidence_path = upgrade_dir.join("migration.json");
    let evidence = json!({
        "type":"minidregg-b-consumer-host-upgrade-v1", "oldHost":utf8_path(&old_host)?,
        "oldHostSha256":old_sha, "newHost":utf8_path(&new_host)?, "newHostSha256":new_sha,
        "oldPinType":old_pin_type, "oldPinSha256":old_pin_sha,
        "oldPinPath":utf8_path(&upgrade_dir.join("old-pin.json"))?,
        "configPath":utf8_path(&config)?, "configSha256":config_sha,
        "attemptConfigPath":utf8_path(&manifest_config)?,
        "attemptConfigSha256":file_digest(&manifest_config)?,
        "socket":utf8_path(&socket)?, "keyPath":utf8_path(&key)?,
        "publicKey":old_pin.get("publicKey"), "manifestSha256":original_manifests,
        "prepare":prepare_name, "callSha256":call_sha,
        "knownOutcomeSha256":known_sha, "newLookupSha256":file_digest(&upgrade_dir.join("lookup.bin"))?,
        "confirmedFields":known, "pendingPhase":"Sending",
        "scope":"operator-authorized rebind for one retained call; no submit or ACK"
    });
    write_json_new(&evidence_path, &evidence)?;
    sync_directory_ancestors(&upgrade_dir)?;
    let evidence_sha = file_digest(&evidence_path)?;
    let next_pin = v2_pin(
        &new_host,
        &config,
        &socket,
        &key,
        Some(utf8_path(&evidence_path)?),
        Some(&evidence_sha),
    )?;
    let mut next_pin_bytes = serde_json::to_vec_pretty(&next_pin)
        .map_err(|error| format!("cannot render the upgraded host pin: {error}"))?;
    next_pin_bytes.push(b'\n');
    if read_json(&pin_path)? != old_pin || file_digest(&pin_path)? != old_pin_sha {
        return Err("worker pin changed during host upgrade".into());
    }
    crate::fsio::replace_private(&pin_path, &next_pin_bytes)
        .map_err(|e| format!("cannot activate upgraded host pin: {e}"))?;
    sync_directory_ancestors(state_dir)?;
    println!("host upgrade pinned; retained Sending call unchanged; no submit or ACK performed");
    Ok(())
}

fn outcome_transaction(path: &Path) -> Result<Option<String>> {
    if !path.exists() {
        return Ok(None);
    }
    let value = read_json(path)?;
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Ok(None);
    }
    let txn = value
        .get("transactionId")
        .and_then(Value::as_str)
        .ok_or("confirmed outcome lacks transactionId")?;
    if txn.is_empty()
        || txn.len() > 80
        || !txn.bytes().all(|c| c.is_ascii_digit())
        || (txn.len() > 1 && txn.starts_with('0'))
    {
        return Err("confirmed outcome has noncanonical transactionId".to_owned());
    }
    Ok(Some(txn.to_owned()))
}

fn latest_retry_path(prepare: &Path) -> Result<PathBuf> {
    let (_, json) = next_retry(prepare)?;
    Ok(json)
}

fn retry_outcome(prepare: &Path, mode: &str, upgrade: Option<&HostUpgrade>) -> Result<Value> {
    let json = latest_retry_path(prepare)?;
    let result = retry_with_upgrade(prepare, mode, false, upgrade);
    if json.exists() {
        sync_directory_ancestors(prepare)?;
        read_json(&json)
    } else {
        Err(result
            .err()
            .unwrap_or_else(|| "retry returned no outcome evidence".to_owned()))
    }
}

fn confirmed_after_retry(
    prepare: &Path,
    mode: &str,
    upgrade: Option<&HostUpgrade>,
) -> Result<Option<(String, Value, PathBuf)>> {
    let json = latest_retry_path(prepare)?;
    let value = retry_outcome(prepare, mode, upgrade)?;
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Ok(None);
    }
    Ok(outcome_transaction(&json)?.map(|txn| (txn, value, json)))
}

fn retain_confirmed_anchor_route(
    pending: &Path,
    prepare: &Path,
    outcome_json: &Path,
    value: &Value,
    route: ConsumerRoute,
) -> Result<()> {
    let outcome_bin = outcome_json.with_extension("bin");
    let anchor = json!({
        "type":if route.reply {"minidregg-a-reply-consumer-confirmed-anchor-v1"}
            else {"minidregg-b-consumer-confirmed-anchor-v1"},
        "prepare":utf8_path(prepare)?,
        "callSha256":file_digest(&prepare.join("call.bin"))?,
        "attemptManifestSha256":file_digest(&prepare.join("attempt.json"))?,
        "outcomePath":utf8_path(outcome_json)?,
        "outcomeSha256":file_digest(&outcome_bin)?,
        "confirmedFields":confirmed_fields(value)?
    });
    let path = pending.join("confirmed-anchor.json");
    if path.exists() {
        let retained = read_json(&path)?;
        if retained.get("type") != anchor.get("type")
            || retained.get("prepare") != anchor.get("prepare")
            || retained.get("callSha256") != anchor.get("callSha256")
            || retained.get("attemptManifestSha256") != anchor.get("attemptManifestSha256")
            || retained.get("confirmedFields") != anchor.get("confirmedFields")
            || retained
                .get("outcomePath")
                .and_then(Value::as_str)
                .is_none_or(|path| {
                    file_digest(&PathBuf::from(path).with_extension("bin"))
                        .ok()
                        .as_deref()
                        != retained.get("outcomeSha256").and_then(Value::as_str)
                })
        {
            return Err("confirmed worker anchor changed between exact lookups".into());
        }
    } else {
        write_json_new(&path, &anchor)?;
        sync_directory_ancestors(pending)?;
    }
    Ok(())
}

#[cfg(test)]
fn retain_confirmed_anchor(
    pending: &Path,
    prepare: &Path,
    outcome_json: &Path,
    value: &Value,
) -> Result<()> {
    retain_confirmed_anchor_route(pending, prepare, outcome_json, value, B_CONSUMER)
}

fn classify_poll_route(value: &Value, route: ConsumerRoute) -> Result<(String, bool)> {
    if value.get("type").and_then(Value::as_str) != Some(route.poll_type) {
        return Err("unexpected poll response type for worker route".to_owned());
    }
    let status = value
        .get("status")
        .and_then(Value::as_str)
        .ok_or("B poll lacks status")?;
    match status {
        "idle"
            if value.pointer("/decision/type").and_then(Value::as_str)
                == Some("fn-empty-page-idle-v1")
                && value.get("intentHex").and_then(Value::as_str) == Some("") =>
        {
            Ok(("idle".into(), true))
        }
        "skip-decision" => {
            if value.pointer("/decision/decision").and_then(Value::as_str) != Some("proposed-fresh")
            {
                return Err("historical skip has no transaction ID in poll response; operator reconciliation required".into());
            }
            let intent_hex = value
                .get("intentHex")
                .and_then(Value::as_str)
                .ok_or("skip lacks intentHex")?;
            let intent = decode_hex(intent_hex)?;
            if hex(&intent) != intent_hex {
                return Err("skip intentHex is not canonical lowercase".into());
            }
            validate_skip_decision(value, route, &intent)?;
            let own_r = route.reply
                && value.pointer("/decision/type").and_then(Value::as_str)
                    == Some("fn-a-own-r-progress-decision-v1");
            let from = value
                .pointer("/decision/fromPosition")
                .and_then(Value::as_str)
                .ok_or("skip lacks fromPosition")?
                .parse::<u128>()
                .map_err(|_| "invalid skip fromPosition")?;
            let to = value
                .pointer("/decision/toPosition")
                .and_then(Value::as_str)
                .ok_or("skip lacks toPosition")?
                .parse::<u128>()
                .map_err(|_| "invalid skip toPosition")?;
            let distance = to.checked_sub(from).ok_or("skip position reversed")?;
            if !(1..=16).contains(&distance) || to > u32::MAX as u128 {
                return Err("skip page exceeds source poll scan bound".into());
            }
            // An own-R skip selects one article; it says nothing about later Q
            // articles already in the same GROUP snapshot. Only an empty-page
            // scan proves a short page reached the current frontier.
            Ok(("skip".into(), !own_r && distance < 16))
        }
        "accepted-decision"
            if value
                .get("intentHex")
                .and_then(Value::as_str)
                .is_some_and(|s| !s.is_empty())
                && (!route.reply
                    || (value.pointer("/decision/type").and_then(Value::as_str)
                        == Some("fn-a-reply-consumer-decision-v1")
                        && matches!(
                            value.pointer("/decision/decision").and_then(Value::as_str),
                            Some("proposed-fresh" | "proposed-conflict")
                        ))) =>
        {
            Ok(("publication".into(), true))
        }
        "refused" => Err("B poll refused; retained evidence requires operator review".into()),
        _ => Err(
            "B poll cannot be advanced safely; retained evidence requires operator review".into(),
        ),
    }
}

#[cfg(test)]
fn classify_poll(value: &Value) -> Result<(String, bool)> {
    classify_poll_route(value, B_CONSUMER)
}

fn finish(state_dir: &Path, pending: &Path, state: &Value) -> Result<()> {
    let completed = state_dir.join("completed");
    private_dir(&completed)?;
    let target = completed.join(field(state, "txn")?);
    if target.exists() {
        return Err("completed transaction archive already exists".into());
    }
    fs::rename(pending, &target)
        .map_err(|e| format!("cannot archive completed consumer operation: {e}"))?;
    sync_directory_ancestors(&completed)?;
    sync_directory_ancestors(state_dir)
}

fn ack_newly_confirmed(
    host: &Path,
    config: &Path,
    pending: &Path,
    state: &mut Value,
    route: ConsumerRoute,
) -> Result<()> {
    let ack = attempt(pending, state, "ack")?;
    match consumer_ack(host, config, field(state, "txn")?, &ack, route) {
        Ok(()) => sync_directory_ancestors(&ack),
        Err(_) => recover_acking_route(host, config, pending, state, route),
    }
}

// A retained op13 frame is sufficient evidence even if the process died before
// it wrote ack.json or archived the pending operation. Never infer an ACK from
// an absent reply, and never conflate prefix coverage with an exact ACK.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AckEvidence {
    Exact,
    Covered,
    Refused,
    Uncertain,
    TransportFault,
}

fn retained_ack_route(
    pending: &Path,
    state: &Value,
    route: ConsumerRoute,
) -> Result<Option<AckEvidence>> {
    let Some(name) = state.get("ack").and_then(Value::as_str) else {
        return Ok(None);
    };
    if name.len() != 12
        || !name.starts_with("ack-")
        || !name[4..].bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err("durable ACK attempt name is invalid".into());
    }
    let directory = pending.join(name);
    let frame_path = directory.join("reply.frame");
    let json_path = directory.join("ack.json");
    if !frame_path.exists() {
        if json_path.exists() {
            return Err("ACK JSON exists without its complete retained frame".into());
        }
        return Ok(None);
    }
    let frame = fs::read(&frame_path)
        .map_err(|error| format!("cannot read retained ACK frame: {error}"))?;
    if frame.first() != Some(&route.ack_opcode) {
        return Err("retained ACK frame is not a successful reply for this route".into());
    }
    if json_path.exists()
        && fs::read(&json_path)
            .map_err(|error| format!("cannot read retained ACK JSON: {error}"))?
            != frame[1..]
    {
        return Err("retained ACK JSON differs from the complete frame".into());
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|error| format!("retained ACK frame has invalid JSON: {error}"))?;
    match value.get("fnAck").and_then(Value::as_str) {
        Some("durable-accepted") => {
            parse_ack_result(&value, route, field(state, "txn")?)?;
            Ok(Some(AckEvidence::Exact))
        }
        Some("covered-by-durable-frontier") => {
            parse_ack_result(&value, route, field(state, "txn")?)?;
            Ok(Some(AckEvidence::Covered))
        }
        Some(status @ ("refused" | "uncertain" | "transport-fault")) => {
            if value.get("type").and_then(Value::as_str) != Some(route.ack_type)
                || value.get("miniTransactionId").and_then(Value::as_str)
                    != Some(field(state, "txn")?)
            {
                return Err("retained ACK reply identity mismatch".into());
            }
            Ok(Some(match status {
                "refused" => AckEvidence::Refused,
                "uncertain" => AckEvidence::Uncertain,
                _ => AckEvidence::TransportFault,
            }))
        }
        _ => Err("retained ACK reply lacks a supported outcome".into()),
    }
}

#[cfg(test)]
fn retained_ack(pending: &Path, state: &Value) -> Result<Option<AckEvidence>> {
    retained_ack_route(pending, state, B_CONSUMER)
}

fn recover_acking_route(
    host: &Path,
    config: &Path,
    pending: &Path,
    state: &mut Value,
    route: ConsumerRoute,
) -> Result<()> {
    match retained_ack_route(pending, state, route) {
        Ok(Some(AckEvidence::Exact)) => return Ok(()),
        Ok(Some(AckEvidence::Covered)) => return hold(
            pending,
            state,
            "retained ACK proves only durable cursor-prefix coverage, not the exact old ACK event",
        ),
        Ok(Some(AckEvidence::Refused)) => {
            return hold(
                pending,
                state,
                "fn definitively refused the retained exact ACK; operator review required",
            )
        }
        Ok(Some(AckEvidence::Uncertain | AckEvidence::TransportFault)) => {}
        Err(error) => {
            return hold(
                pending,
                state,
                &format!("retained ACK reply requires operator review: {error}"),
            )
        }
        Ok(None) => {}
    }
    // A fresh native equal-current skip repeat returned durable-accepted with
    // unchanged ACK and journal frontiers. Retry only this retained transaction,
    // and persist the retry marker before sending so a second restart cannot
    // turn a lost reply into an unbounded stream of ACK attempts.
    if state.get("ackRetryStarted").and_then(Value::as_bool) == Some(true) {
        return hold(pending, state,
            "one exact ACK retry was already started without a complete reply; operator review required");
    }
    set(state, "ackRetryStarted", json!(true));
    save_state(pending, state)?;
    let ack = attempt(pending, state, "ack")?;
    match consumer_ack(host, config, field(state, "txn")?, &ack, route) {
        Ok(()) => {
            sync_directory_ancestors(&ack)?;
            Ok(())
        }
        Err(error) => {
            let reason = match retained_ack_route(pending, state, route) {
                Ok(Some(AckEvidence::Exact)) => {
                    return hold(pending, state,
                        "exact ACK reply exists but client reported an error; operator review required")
                }
                Ok(Some(AckEvidence::Covered)) =>
                    "ACK retry proves only durable cursor-prefix coverage, not the exact old ACK event".to_owned(),
                Ok(Some(AckEvidence::Refused)) =>
                    "fn definitively refused the exact ACK retry; operator review required".to_owned(),
                Ok(Some(AckEvidence::Uncertain)) =>
                    "fn reported uncertain ACK retry; one retry exhausted".to_owned(),
                Ok(Some(AckEvidence::TransportFault)) =>
                    "fn reported ACK retry transport fault; one retry exhausted".to_owned(),
                Ok(None) => format!("ACK retry reply missing; one retry exhausted: {error}"),
                Err(inspect_error) => format!(
                    "ACK retry reply cannot be validated: {inspect_error}; client error: {error}"
                ),
            };
            hold(pending, state, &reason)
        }
    }
}

fn hold<T>(pending: &Path, state: &mut Value, reason: &str) -> Result<T> {
    set(state, "phase", json!("Held"));
    set(state, "reason", json!(reason));
    save_state(pending, state)?;
    Err(reason.to_owned())
}

fn held_ack_anchor(
    state_dir: &Path,
    pending: &Path,
    state: &Value,
    host: &Path,
    route: ConsumerRoute,
) -> Result<(Value, Option<HostUpgrade>)> {
    let prepare = pending.join(field(state, "prepare")?);
    let call = prepare.join("call.bin");
    sync_retained_call(&prepare, &call)?;
    let mut sending = state.clone();
    sending["phase"] = json!("Sending");
    let upgrade = load_upgrade(state_dir, pending, &sending, host)?;
    let anchor_path = pending.join("confirmed-anchor.json");
    let expected = if anchor_path.exists() {
        let anchor = read_json(&anchor_path)?;
        if anchor.get("type").and_then(Value::as_str)
            != Some(if route.reply {
                "minidregg-a-reply-consumer-confirmed-anchor-v1"
            } else {
                "minidregg-b-consumer-confirmed-anchor-v1"
            })
            || anchor.get("prepare").and_then(Value::as_str) != Some(utf8_path(&prepare)?)
            || anchor.get("callSha256").and_then(Value::as_str)
                != Some(file_digest(&call)?.as_str())
            || anchor.get("attemptManifestSha256").and_then(Value::as_str)
                != Some(file_digest(&prepare.join("attempt.json"))?.as_str())
        {
            return Err("retained confirmed ACK anchor differs from exact call".into());
        }
        let outcome_path = PathBuf::from(field(&anchor, "outcomePath")?);
        if !outcome_path.starts_with(&prepare)
            || file_digest(&outcome_path.with_extension("bin"))? != field(&anchor, "outcomeSha256")?
        {
            return Err("retained confirmed ACK outcome bytes changed".into());
        }
        let fields = confirmed_fields(&read_json(&outcome_path)?)?;
        if anchor.get("confirmedFields") != Some(&fields) {
            return Err("retained confirmed ACK outcome presentation changed".into());
        }
        fields
    } else if let Some(upgrade) = &upgrade {
        upgrade.expected_fields.clone()
    } else {
        return Err("held ACK lacks a durable exact-call confirmed receipt anchor".into());
    };
    if expected.get("transactionId").and_then(Value::as_str) != Some(field(state, "txn")?) {
        return Err("held ACK transaction differs from confirmed exact-call anchor".into());
    }
    if let Some(upgrade) = &upgrade {
        if expected != upgrade.expected_fields {
            return Err("confirmed ACK anchor differs from host migration receipt".into());
        }
    }
    Ok((expected, upgrade))
}

fn archive_exact_ack_route(
    state_dir: &Path,
    pending: &Path,
    state: &mut Value,
    route: ConsumerRoute,
) -> Result<()> {
    if retained_ack_route(pending, state, route)? != Some(AckEvidence::Exact) {
        return Err("held ACK recovery lacks a retained exact durable reply".into());
    }
    set(state, "phase", json!("Acking"));
    save_state(pending, state)?;
    finish(state_dir, pending, state)
}

#[cfg(test)]
fn archive_exact_ack(state_dir: &Path, pending: &Path, state: &mut Value) -> Result<()> {
    archive_exact_ack_route(state_dir, pending, state, B_CONSUMER)
}

fn require_pending_route(state: &Value, route: ConsumerRoute) -> Result<()> {
    match (route.reply, state.get("route").and_then(Value::as_str)) {
        (true, Some("a-reply")) | (false, None | Some("b")) => Ok(()),
        _ => Err("pending consumer state belongs to another route".into()),
    }
}

fn resume_held_ack_route(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    route: ConsumerRoute,
) -> Result<()> {
    private_dir(state_dir)?;
    let socket_dir = socket.parent().ok_or("socket lacks parent")?;
    private_dir(socket_dir)?;
    let _global = transport::service_lock(&socket_dir.join("consumer-worker.lock"))?;
    let _worker = transport::service_lock(&state_dir.join("worker.lock"))?;
    pin_route(state_dir, host, config, socket, key, route)?;
    if read_json(&state_dir.join("pin.json"))?
        .get("type")
        .and_then(Value::as_str)
        != Some(if route.reply {
            "minidregg-a-reply-consumer-worker-pin-v2"
        } else {
            "minidregg-b-consumer-worker-pin-v2"
        })
    {
        return Err("explicit held ACK recovery requires a v2 host image pin".into());
    }
    pin_worker_host_image(state_dir)?;
    let pending = state_dir.join("pending");
    private_dir(&pending)?;
    let mut state = read_json(&pending.join("state.json"))?;
    require_pending_route(&state, route)?;
    if field(&state, "phase")? != "Held" {
        return Err("explicit ACK recovery requires a held decision".into());
    }
    let poll = pending.join(field(&state, "poll")?);
    let (retained_kind, _) = classify_poll_route(&read_json(&poll.join("decision.json"))?, route)?;
    if !matches!(retained_kind.as_str(), "publication" | "skip")
        || field(&state, "kind")? != retained_kind
    {
        return Err("held ACK kind differs from retained source poll decision".into());
    }
    if state.get("ackRetryStarted").and_then(Value::as_bool) == Some(true) {
        return Err("existing exact ACK retry is already exhausted".into());
    }
    let (expected, upgrade) = held_ack_anchor(state_dir, &pending, &state, host, route)?;
    if state.get("ackRecoveryStarted").and_then(Value::as_bool) == Some(true) {
        if retained_ack_route(&pending, &state, route)? == Some(AckEvidence::Exact) {
            return archive_exact_ack_route(state_dir, &pending, &mut state, route);
        }
        return Err(
            "one exact held ACK recovery was already started without a complete exact reply".into(),
        );
    }
    let prior_ack = field(&state, "ack")?.to_owned();
    let prior_frame_path = pending.join(&prior_ack).join("reply.frame");
    let prior_frame = fs::read(&prior_frame_path).map_err(|e| e.to_string())?;
    if prior_frame.first() != Some(&255)
        || prior_frame.len() < 2
        || pending.join(&prior_ack).join("ack.json").exists()
    {
        return Err("held ACK lacks a complete source refusal frame".into());
    }
    let reconcile = attempt(&pending, &mut state, "reconcile")?;
    private_dir(&reconcile)?;
    create_private(&reconcile.join("prior-refusal.bin"), &prior_frame[1..])?;
    let decoded = inspect(
        host,
        config,
        "outcome",
        &reconcile.join("prior-refusal.bin"),
        &reconcile.join("prior-refusal.json"),
    )?;
    if decoded.get("type").and_then(Value::as_str) != Some("refused")
        || decoded.get("phase").and_then(Value::as_str) != Some("666e2d73657373696f6e")
    {
        return Err("prior ACK frame is not a source-owned fn-session refusal".into());
    }
    let prepare = pending.join(field(&state, "prepare")?);
    let lookup_json = latest_retry_path(&prepare)?;
    let lookup = retry_outcome(&prepare, "lookup", upgrade.as_ref())?;
    require_upgraded_receipt(&lookup, &expected)?;
    if outcome_transaction(&lookup_json)?.as_deref() != Some(field(&state, "txn")?) {
        return Err("recovery lookup transaction differs from retained ACK transaction".into());
    }
    let proof = json!({
        "type":if route.reply {"minidregg-a-reply-consumer-held-ack-recovery-v1"}
            else {"minidregg-b-consumer-held-ack-recovery-v1"},
        "priorAck":prior_ack, "priorFrameSha256":hex(&Sha256::digest(&prior_frame)),
        "priorReason":field(&state, "reason")?, "lookupPath":utf8_path(&lookup_json)?,
        "lookupSha256":file_digest(&lookup_json.with_extension("bin"))?,
        "confirmedFields":expected, "transactionId":field(&state, "txn")?,
        "scope":"one exact typed ACK retry; no Mini submit or new intent"
    });
    write_json_new(&reconcile.join("recovery.json"), &proof)?;
    sync_directory_ancestors(&reconcile)?;
    set(&mut state, "ackRecoveryStarted", json!(true));
    set(&mut state, "ackRecoveryPriorAck", json!(prior_ack));
    save_state(&pending, &state)?;
    let ack = attempt(&pending, &mut state, "ack")?;
    let sent = consumer_ack(host, config, field(&state, "txn")?, &ack, route);
    if sent.is_ok()
        || retained_ack_route(&pending, &state, route).ok() == Some(Some(AckEvidence::Exact))
    {
        sync_directory_ancestors(&ack)?;
        return archive_exact_ack_route(state_dir, &pending, &mut state, route);
    }
    hold(
        &pending,
        &mut state,
        &format!(
            "one explicit exact ACK recovery did not prove durable acceptance: {}",
            sent.unwrap_err()
        ),
    )
}

pub(super) fn resume_held_ack(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
) -> Result<()> {
    resume_held_ack_route(host, config, socket, key, state_dir, B_CONSUMER)
}

pub(super) fn resume_held_reply_ack(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
) -> Result<()> {
    resume_held_ack_route(host, config, socket, key, state_dir, A_REPLY_CONSUMER)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Stop {
    Idle,
    ShortPage,
    Publication,
    PageCap,
}

fn completed_stop(state: &Value) -> Result<Option<Stop>> {
    if field(state, "kind")? == "publication" {
        Ok(Some(Stop::Publication))
    } else if state.get("short").and_then(Value::as_bool) == Some(true) {
        Ok(Some(Stop::ShortPage))
    } else {
        Ok(None)
    }
}

pub(super) fn run(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
) -> Result<()> {
    run_route(host, config, socket, key, state_dir, max_pages, B_CONSUMER)
}

pub(super) fn run_reply(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
) -> Result<()> {
    run_route(
        host,
        config,
        socket,
        key,
        state_dir,
        max_pages,
        A_REPLY_CONSUMER,
    )
}

fn run_route(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
    route: ConsumerRoute,
) -> Result<()> {
    private_dir(state_dir)?;
    let socket_dir = socket.parent().ok_or("socket lacks parent")?;
    private_dir(socket_dir)?;
    let _global = transport::service_lock(&socket_dir.join("consumer-worker.lock"))?;
    let _lock = transport::service_lock(&state_dir.join("worker.lock"))?;
    let stop = run_locked_route(host, config, socket, key, state_dir, max_pages, route)?;
    println!("consumer wake stopped: {stop:?}");
    Ok(())
}

pub(super) fn run_locked_route(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
    route: ConsumerRoute,
) -> Result<Stop> {
    pin_route(state_dir, host, config, socket, key, route)?;
    pin_worker_host_image(state_dir)?;
    let pending = state_dir.join("pending");
    let mut pages = 0;
    loop {
        if pages >= max_pages {
            return Ok(Stop::PageCap);
        }
        if !pending.exists() {
            private_dir(&pending)?;
            let mut initial = json!({"phase":"Polling", "serial":0});
            if route.reply {
                initial["route"] = json!("a-reply");
            }
            save_state(&pending, &initial)?;
        }
        private_dir(&pending)?;
        let state_file = pending.join("state.json");
        if !state_file.exists() {
            let only_state_temps = fs::read_dir(&pending)
                .map_err(|e| format!("cannot inspect new worker slot: {e}"))?
                .all(|entry| {
                    entry
                        .ok()
                        .and_then(|e| e.file_name().into_string().ok())
                        .is_some_and(|name| name.starts_with("state-") && name.ends_with(".tmp"))
                });
            if !only_state_temps {
                return Err(
                    "pending worker slot lacks durable state; operator review required".into(),
                );
            }
            let mut initial = json!({"phase":"Polling", "serial":0});
            if route.reply {
                initial["route"] = json!("a-reply");
            }
            save_state(&pending, &initial)?;
        }
        let mut state = read_json(&state_file)?;
        require_pending_route(&state, route)?;
        match field(&state, "phase")? {
            "Polling" => {
                let path = attempt(&pending, &mut state, "poll")?;
                if let Err(error) = consumer_poll(host, config, &path, route) {
                    if path.join("reply.frame").exists() {
                        return hold(
                            &pending,
                            &mut state,
                            &format!("poll reply retained but unusable: {error}"),
                        );
                    }
                    return Err(error);
                }
                let value = read_json(&path.join("decision.json"))?;
                let (kind, short) = match classify_poll_route(&value, route) {
                    Ok(classification) => classification,
                    Err(error) => return hold(&pending, &mut state, &error),
                };
                if kind == "idle" {
                    fs::remove_dir_all(&pending)
                        .map_err(|e| format!("cannot clean idle poll: {e}"))?;
                    sync_directory_ancestors(state_dir)?;
                    return Ok(Stop::Idle);
                }
                if !path.join("intent.bin").is_file() {
                    return Err("poll did not retain canonical intent".into());
                }
                sync_directory_ancestors(&path)?;
                set(&mut state, "phase", json!("Preparing"));
                set(&mut state, "kind", json!(kind));
                set(&mut state, "short", json!(short));
                save_state(&pending, &state)?;
            }
            "Preparing" => {
                let poll = pending.join(field(&state, "poll")?);
                let path = attempt(&pending, &mut state, "prepare")?;
                submit(
                    host,
                    config,
                    &poll.join("intent.bin"),
                    OsStr::new("binary"),
                    key,
                    &path,
                    true,
                )?;
                sync_retained_call(&path, &path.join("call.bin"))?;
                set(&mut state, "phase", json!("Ready"));
                save_state(&pending, &state)?;
            }
            "Ready" => {
                let path = pending.join(field(&state, "prepare")?);
                sync_retained_call(&path, &path.join("call.bin"))?;
                set(&mut state, "phase", json!("Sending"));
                save_state(&pending, &state)?;
                let outcome_path = latest_retry_path(&path)?;
                let outcome = retry_outcome(&path, "submit", None)?;
                let txn = match outcome.get("type").and_then(Value::as_str) {
                    Some("confirmed") => outcome_transaction(&outcome_path)?
                        .ok_or("confirmed submit lacks transaction ID")?,
                    Some("refused") => {
                        return hold(
                            &pending,
                            &mut state,
                            "Mini definitively refused the exact call; operator review required",
                        )
                    }
                    _ => {
                        return Err(
                            "submit did not confirm; exact call retained, lookup required".into(),
                        )
                    }
                };
                retain_confirmed_anchor_route(&pending, &path, &outcome_path, &outcome, route)?;
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state, route)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if let Some(stop) = completed_stop(&state)? {
                    return Ok(stop);
                }
            }
            "Sending" => {
                let path = pending.join(field(&state, "prepare")?);
                sync_retained_call(&path, &path.join("call.bin"))?;
                let upgrade = load_upgrade(state_dir, &pending, &state, host)?;
                let lookup_path = latest_retry_path(&path)?;
                let lookup = match retry_outcome(&path, "lookup", upgrade.as_ref()) {
                    Ok(value) => value,
                    Err(error) => return hold(&pending, &mut state,
                        &format!("exact lookup unresolved; retained call requires operator reconciliation: {error}")),
                };
                let (txn, anchored, anchor_path) = match lookup.get("type").and_then(Value::as_str) {
                    Some("confirmed") => {
                        if let Some(upgrade) = &upgrade {
                            if require_upgraded_receipt(&lookup, &upgrade.expected_fields).is_err() {
                                return hold(&pending, &mut state,
                                    "upgraded lookup confirmed a different four-field receipt; no ACK or resubmit");
                            }
                        }
                        (outcome_transaction(&lookup_path)?
                            .ok_or("confirmed exact lookup lacks transaction ID")?, lookup, lookup_path)
                    }
                    Some("absent") if upgrade.is_some() => return hold(&pending, &mut state,
                        "upgraded lookup is absent despite prior confirmed receipt; exact call retained for operator review"),
                    Some("absent") => match confirmed_after_retry(&path, "submit", None) {
                        Ok(Some(confirmed)) => confirmed,
                        Ok(None) => return hold(&pending, &mut state,
                            "same-call resubmit did not confirm; exact call retained"),
                        Err(error) => return hold(&pending, &mut state,
                            &format!("same-call resubmit uncertain; exact call retained: {error}")),
                    },
                    _ => return hold(&pending, &mut state,
                        "exact lookup did not confirm or prove absence; retained call requires operator reconciliation"),
                };
                retain_confirmed_anchor_route(&pending, &path, &anchor_path, &anchored, route)?;
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state, route)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if let Some(stop) = completed_stop(&state)? {
                    return Ok(stop);
                }
            }
            "Acking" => {
                recover_acking_route(host, config, &pending, &mut state, route)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if let Some(stop) = completed_stop(&state)? {
                    return Ok(stop);
                }
            }
            "Held" => {
                return Err(format!(
                    "consumer worker held for operator review: {}",
                    field(&state, "reason")?
                ))
            }
            other => return Err(format!("unknown durable consumer phase {other}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_upgrade_accepts_fresh_v2_and_legacy_v1_without_rebinding_call() {
        use std::os::unix::fs::PermissionsExt;
        // The stub supplies fixed receipt bytes only to exercise physical pin
        // activation. This test does not establish native receipt semantics.
        for legacy in [false, true] {
            let root = env::temp_dir().join(format!(
                "mini-upgrade-pin-{}-{}",
                std::process::id(),
                workspace::random_nonce().unwrap()
            ));
            private_dir(&root).unwrap();
            let state_dir = root.join("state");
            let socket_dir = root.join("service");
            private_dir(&state_dir).unwrap();
            private_dir(&socket_dir).unwrap();
            let old_host = root.join("old-host");
            let new_host = root.join("new-host");
            let config = root.join("config.json");
            let key = root.join("key");
            let socket = socket_dir.join("host.sock");
            let known = root.join("known-outcome.bin");
            create_private(&old_host, b"old pinned image").unwrap();
            create_private(&new_host, br#"#!/bin/sh
if [ "$2" = lookup ]; then
  printf '%s' '{"type":"confirmed","confirmation":"replayed","acceptedCount":"3","transactionId":"123","eventId":"456","worldRoot":"789"}' > "$4"
else
  cat "$4" > "$5"
fi
"#).unwrap();
            fs::set_permissions(&new_host, fs::Permissions::from_mode(0o700)).unwrap();
            create_private(&config, b"{}\n").unwrap();
            create_private(&key, &[7; 32]).unwrap();
            create_private(&known, br#"{"type":"confirmed","confirmation":"replayed","acceptedCount":"3","transactionId":"123","eventId":"456","worldRoot":"789"}"#).unwrap();
            if legacy {
                write_json_new(
                    &state_dir.join("pin.json"),
                    &pin_identity(&old_host, &config, &socket, &key).unwrap(),
                )
                .unwrap();
            } else {
                pin(&state_dir, &old_host, &config, &socket, &key).unwrap();
                assert_eq!(
                    read_json(&state_dir.join("pin.json")).unwrap()["type"],
                    "minidregg-b-consumer-worker-pin-v2"
                );
            }
            let pending = state_dir.join("pending");
            let prepare = pending.join("prepare-00000002");
            private_dir(&pending).unwrap();
            private_dir(&prepare).unwrap();
            create_private(&prepare.join("call.bin"), b"exact retained call").unwrap();
            create_private(&prepare.join("config.json"), b"{}\n").unwrap();
            write_json_new(&prepare.join("attempt.json"), &json!({"format":"minidregg-resource-client-attempt-v1", "operation":"submit",
                "host":utf8_path(&old_host).unwrap(), "config":utf8_path(&prepare.join("config.json")).unwrap(), "socket":utf8_path(&socket).unwrap()})).unwrap();
            let state = json!({"phase":"Sending","prepare":"prepare-00000002"});
            save_state(&pending, &state).unwrap();
            upgrade_host(UpgradeRequest {
                old_host: &old_host,
                new_host: &new_host,
                config: &config,
                socket: &socket,
                key: &key,
                state_dir: &state_dir,
                known_outcome: &known,
                old_sha: &file_digest(&old_host).unwrap(),
                new_sha: &file_digest(&new_host).unwrap(),
                known_sha: &file_digest(&known).unwrap(),
            })
            .unwrap();
            assert_eq!(
                fs::read(prepare.join("call.bin")).unwrap(),
                b"exact retained call"
            );
            assert_eq!(read_json(&pending.join("state.json")).unwrap(), state);
            pin(&state_dir, &new_host, &config, &socket, &key).unwrap();
            assert!(load_upgrade(&state_dir, &pending, &state, &new_host)
                .unwrap()
                .is_some());
            let pin_value = read_json(&state_dir.join("pin.json")).unwrap();
            let evidence = read_json(Path::new(
                pin_value["upgradeEvidencePath"].as_str().unwrap(),
            ))
            .unwrap();
            fs::write(
                Path::new(evidence["oldPinPath"].as_str().unwrap()),
                b"changed original pin",
            )
            .unwrap();
            assert!(pin(&state_dir, &new_host, &config, &socket, &key).is_err());
            assert_eq!(
                fs::read(prepare.join("call.bin")).unwrap(),
                b"exact retained call"
            );
            fs::remove_dir_all(root).unwrap();
        }
    }

    #[test]
    fn upgraded_pin_binds_pending_call_but_allows_next_fresh_wake() {
        let root = env::temp_dir().join(format!(
            "mini-upgrade-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let state_dir = root.join("state");
        let socket_dir = root.join("service");
        private_dir(&state_dir).unwrap();
        private_dir(&socket_dir).unwrap();
        let old_host = root.join("old-host");
        let new_host = root.join("new-host");
        let config = root.join("config.json");
        let key = root.join("key");
        let socket = socket_dir.join("host.sock");
        create_private(&old_host, b"old image").unwrap();
        create_private(&new_host, b"new image").unwrap();
        create_private(&config, b"{}\n").unwrap();
        create_private(&key, &[7; 32]).unwrap();
        let pending = state_dir.join("pending");
        let prepare = pending.join("prepare-00000002");
        private_dir(&pending).unwrap();
        private_dir(&prepare).unwrap();
        create_private(&prepare.join("call.bin"), b"exact retained call").unwrap();
        let attempt_config = prepare.join("config.json");
        create_private(&attempt_config, b"{}\n").unwrap();
        let original_manifest = json!({"format":"minidregg-resource-client-attempt-v1",
            "operation":"submit", "host":utf8_path(&old_host).unwrap(),
            "config":utf8_path(&attempt_config).unwrap(), "socket":utf8_path(&socket).unwrap()});
        write_json_new(&prepare.join("attempt.json"), &original_manifest).unwrap();
        let mut state = json!({"phase":"Sending","prepare":"prepare-00000002"});
        save_state(&pending, &state).unwrap();
        let evidence = state_dir.join("migration.json");
        let prior_pin = state_dir.join("old-pin.json");
        write_json_new(
            &prior_pin,
            &pin_identity(&old_host, &config, &socket, &key).unwrap(),
        )
        .unwrap();
        write_json_new(&evidence, &json!({
            "type":"minidregg-b-consumer-host-upgrade-v1",
            "oldPinPath":utf8_path(&prior_pin).unwrap(), "oldPinSha256":file_digest(&prior_pin).unwrap(),
            "oldHost":utf8_path(&old_host).unwrap(), "oldHostSha256":file_digest(&old_host).unwrap(),
            "newHost":utf8_path(&new_host).unwrap(), "newHostSha256":file_digest(&new_host).unwrap(),
            "configPath":utf8_path(&config).unwrap(), "configSha256":file_digest(&config).unwrap(),
            "attemptConfigPath":utf8_path(&attempt_config).unwrap(),
            "attemptConfigSha256":file_digest(&attempt_config).unwrap(),
            "socket":utf8_path(&socket).unwrap(), "prepare":"prepare-00000002",
            "callSha256":file_digest(&prepare.join("call.bin")).unwrap(),
            "confirmedFields":{"acceptedCount":"3","transactionId":"123",
                "eventId":"456","worldRoot":"789"}
        })).unwrap();
        let pin_value = v2_pin(
            &new_host,
            &config,
            &socket,
            &key,
            Some(utf8_path(&evidence).unwrap()),
            Some(&file_digest(&evidence).unwrap()),
        )
        .unwrap();
        write_json_new(&state_dir.join("pin.json"), &pin_value).unwrap();
        pin(&state_dir, &new_host, &config, &socket, &key).unwrap();
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host)
            .unwrap()
            .is_some());
        fs::write(&attempt_config, b"{\"changed\":true}").unwrap();
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host).is_err());
        fs::write(&attempt_config, b"{}\n").unwrap();
        state["phase"] = json!("Acking");
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host)
            .unwrap()
            .is_none());
        state["phase"] = json!("Polling");
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host)
            .unwrap()
            .is_none());
        state["phase"] = json!("Sending");
        let mut fresh_manifest = original_manifest.clone();
        fresh_manifest["host"] = json!(utf8_path(&new_host).unwrap());
        fs::write(
            prepare.join("attempt.json"),
            serde_json::to_vec(&fresh_manifest).unwrap(),
        )
        .unwrap();
        fs::write(prepare.join("call.bin"), b"next fresh call").unwrap();
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host)
            .unwrap()
            .is_none());
        fresh_manifest["host"] = json!(utf8_path(&root.join("unknown-host")).unwrap());
        fs::write(
            prepare.join("attempt.json"),
            serde_json::to_vec(&fresh_manifest).unwrap(),
        )
        .unwrap();
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host).is_err());
        fs::write(
            prepare.join("attempt.json"),
            serde_json::to_vec(&original_manifest).unwrap(),
        )
        .unwrap();
        fs::write(prepare.join("call.bin"), b"different").unwrap();
        assert!(load_upgrade(&state_dir, &pending, &state, &new_host).is_err());
        fs::write(prepare.join("call.bin"), b"exact retained call").unwrap();
        fs::write(&config, b"{\"changed\":true}").unwrap();
        assert!(pin(&state_dir, &new_host, &config, &socket, &key).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn upgrade_receipt_requires_all_four_canonical_fields() {
        let original = json!({"type":"confirmed","acceptedCount":"3", "transactionId":"123",
            "eventId":"456", "worldRoot":"789", "confirmation":"replayed"});
        let mut replay = original.clone();
        replay["confirmation"] = json!("accepted");
        let expected = confirmed_fields(&original).unwrap();
        assert!(require_upgraded_receipt(&replay, &expected).is_ok());
        for field in ["acceptedCount", "transactionId", "eventId", "worldRoot"] {
            let mut changed = replay.clone();
            changed[field] = json!("001");
            assert!(confirmed_fields(&changed).is_err());
            changed[field] = json!("8");
            assert_ne!(
                confirmed_fields(&original).unwrap(),
                confirmed_fields(&changed).unwrap()
            );
            assert!(require_upgraded_receipt(&changed, &expected).is_err());
        }
        replay["type"] = json!("absent");
        assert!(confirmed_fields(&replay).is_err());
    }

    #[test]
    fn confirmed_anchor_survives_new_lookup_but_rejects_different_receipt() {
        let root = env::temp_dir().join(format!(
            "mini-anchor-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        let prepare = pending.join("prepare-00000002");
        private_dir(&pending).unwrap();
        private_dir(&prepare).unwrap();
        create_private(&prepare.join("call.bin"), b"call").unwrap();
        create_private(&prepare.join("attempt.json"), b"manifest").unwrap();
        let absent = json!({"type":"absent"});
        create_private(&prepare.join("retry-0000.bin"), b"absent lookup").unwrap();
        write_json_new(&prepare.join("retry-0000.json"), &absent).unwrap();
        assert!(retain_confirmed_anchor(
            &pending,
            &prepare,
            &prepare.join("retry-0000.json"),
            &absent
        )
        .is_err());
        let value = json!({"type":"confirmed", "acceptedCount":"3",
            "transactionId":"123", "eventId":"456", "worldRoot":"789"});
        create_private(&prepare.join("retry-0001.bin"), b"binary receipt").unwrap();
        write_json_new(&prepare.join("retry-0001.json"), &value).unwrap();
        retain_confirmed_anchor(&pending, &prepare, &prepare.join("retry-0001.json"), &value)
            .unwrap();
        create_private(&prepare.join("retry-0002.bin"), b"same receipt new lookup").unwrap();
        write_json_new(&prepare.join("retry-0002.json"), &value).unwrap();
        retain_confirmed_anchor(&pending, &prepare, &prepare.join("retry-0002.json"), &value)
            .unwrap();
        let mut fork = value;
        fork["worldRoot"] = json!("790");
        assert!(retain_confirmed_anchor(
            &pending,
            &prepare,
            &prepare.join("retry-0002.json"),
            &fork
        )
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_exact_ack_archives_after_crash_without_resending() {
        let root = env::temp_dir().join(format!(
            "mini-ack-archive-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        let ack = pending.join("ack-00000003");
        private_dir(&pending).unwrap();
        private_dir(&ack).unwrap();
        let reply = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"durable-accepted"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&reply).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        let mut state = json!({"phase":"Held", "ackRecoveryStarted":true,
            "ack":"ack-00000003", "txn":"123"});
        save_state(&pending, &state).unwrap();
        archive_exact_ack(&root, &pending, &mut state).unwrap();
        assert!(!pending.exists());
        assert_eq!(
            fs::read(root.join("completed/123/ack-00000003/reply.frame")).unwrap(),
            frame
        );
        assert_eq!(
            field(
                &read_json(&root.join("completed/123/state.json")).unwrap(),
                "phase"
            )
            .unwrap(),
            "Acking"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn live_service_lock_blocks_upgrade_before_any_host_probe() {
        let root = env::temp_dir().join(format!(
            "mini-upgrade-lock-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let socket = root.join("host.sock");
        let _running = transport::service_lock(&socket.with_extension("lock")).unwrap();
        let old_host = root.join("missing-old");
        let new_host = root.join("missing-new");
        let config = root.join("missing-config");
        let key = root.join("missing-key");
        let state_dir = root.join("state");
        let known_outcome = root.join("missing-outcome");
        let error = upgrade_host(UpgradeRequest {
            old_host: &old_host,
            new_host: &new_host,
            config: &config,
            socket: &socket,
            key: &key,
            state_dir: &state_dir,
            known_outcome: &known_outcome,
            old_sha: &"0".repeat(64),
            new_sha: &"1".repeat(64),
            known_sha: &"2".repeat(64),
        })
        .unwrap_err();
        assert!(error.contains("another service owns"));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn orphaned_upgrade_files_do_not_activate_a_v1_pin() {
        let root = env::temp_dir().join(format!(
            "mini-upgrade-orphan-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let host = root.join("old-host");
        let config = root.join("config.json");
        let key = root.join("key");
        let socket = root.join("host.sock");
        create_private(&host, b"old").unwrap();
        create_private(&config, b"{}").unwrap();
        create_private(&key, &[9; 32]).unwrap();
        write_json_new(
            &root.join("pin.json"),
            &pin_identity(&host, &config, &socket, &key).unwrap(),
        )
        .unwrap();
        private_dir(&root.join("host-upgrade-001")).unwrap();
        create_private(&root.join("pin-upgrade-001.tmp"), b"incomplete").unwrap();
        pin(&root, &host, &config, &socket, &key).unwrap();
        assert_eq!(
            read_json(&root.join("pin.json"))
                .unwrap()
                .get("type")
                .and_then(Value::as_str),
            Some("minidregg-b-consumer-worker-pin-v1")
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn source_skip_page_bound_stops_short_page_and_rejects_history_without_txn() {
        let fresh = json!({"type":"fn-consumer-poll-session-v1", "status":"skip-decision",
            "decision":{"type":"fn-empty-page-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"16", "toPosition":"21"},
            "intentHex":"00"});
        assert_eq!(classify_poll(&fresh).unwrap(), ("skip".to_owned(), true));
        let full = json!({"type":"fn-consumer-poll-session-v1", "status":"skip-decision",
            "decision":{"type":"fn-empty-page-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"0", "toPosition":"16"},
            "intentHex":"00"});
        assert_eq!(classify_poll(&full).unwrap(), ("skip".to_owned(), false));
        let mut repeated = fresh;
        repeated["decision"]["decision"] = json!("repeated");
        repeated["intentHex"] = json!("");
        assert!(classify_poll(&repeated).is_err());
        repeated["decision"]["decision"] = json!("proposed-fresh");
        repeated["decision"]["type"] = json!("fn-a-own-r-progress-decision-v1");
        repeated["decision"]["outboxTransactionId"] = json!("42");
        repeated["intentHex"] = json!("00");
        assert!(classify_poll(&repeated).is_err());
    }

    #[test]
    fn a_catalog_route_keeps_b_state_disjoint_and_classifies_own_r() {
        let root = env::temp_dir().join(format!(
            "mini-a-worker-pin-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let host = root.join("host");
        let key = root.join("key");
        let socket = root.join("host.sock");
        let config = root.join("config.json");
        create_private(&host, b"a-host-image").unwrap();
        create_private(&key, &[9; 32]).unwrap();
        let mut catalog = serde_json::Map::new();
        for field in [
            "originConfigPath",
            "rPinPath",
            "qPinPath",
            "scopePath",
            "policyPath",
        ] {
            let path = root.join(format!("{field}.json"));
            create_private(&path, field.as_bytes()).unwrap();
            catalog.insert(field.to_owned(), json!(utf8_path(&path).unwrap()));
        }
        catalog.insert(
            "controlPath".into(),
            json!(utf8_path(&root.join("fn-control.sock")).unwrap()),
        );
        write_json_new(
            &config,
            &json!({"fnReplyCatalog":catalog,
            "fnPoll":null, "fnReplyPoll":null}),
        )
        .unwrap();
        pin_route(&root, &host, &config, &socket, &key, A_REPLY_CONSUMER).unwrap();
        assert_eq!(
            read_json(&root.join("pin.json")).unwrap()["type"],
            "minidregg-a-reply-consumer-worker-pin-v2"
        );
        assert!(pin_route(&root, &host, &config, &socket, &key, B_CONSUMER).is_err());
        assert!(require_pending_route(&json!({"phase":"Polling"}), A_REPLY_CONSUMER).is_err());
        assert!(
            require_pending_route(&json!({"phase":"Polling","route":"a-reply"}), B_CONSUMER)
                .is_err()
        );
        let own_r = json!({"type":"fn-a-reply-poll-session-v1", "status":"skip-decision",
            "decision":{"type":"fn-a-own-r-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"0", "toPosition":"1",
                "outboxTransactionId":"0"}, "intentHex":"00"});
        assert_eq!(
            classify_poll_route(&own_r, A_REPLY_CONSUMER).unwrap(),
            ("skip".into(), false)
        );
        assert!(classify_poll_route(&own_r, B_CONSUMER).is_err());
        let mut historical = own_r;
        historical["decision"]["decision"] = json!("repeated");
        historical["intentHex"] = json!("");
        assert!(classify_poll_route(&historical, A_REPLY_CONSUMER).is_err());
        let q = json!({"type":"fn-a-reply-poll-session-v1", "status":"accepted-decision",
            "decision":{"type":"fn-a-reply-consumer-decision-v1",
                "decision":"proposed-fresh"}, "intentHex":"00"});
        assert_eq!(
            classify_poll_route(&q, A_REPLY_CONSUMER).unwrap(),
            ("publication".into(), true)
        );
        let mut q_repeat = q;
        q_repeat["decision"]["decision"] = json!("repeated");
        q_repeat["intentHex"] = json!("");
        assert!(classify_poll_route(&q_repeat, A_REPLY_CONSUMER).is_err());
        fs::write(root.join("scopePath.json"), b"different scope").unwrap();
        assert!(pin_route(&root, &host, &config, &socket, &key, A_REPLY_CONSUMER).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_own_r_skip_continues_to_queued_q_with_unchanged_group() {
        let own_r = json!({"type":A_REPLY_CONSUMER.poll_type, "status":"skip-decision",
            "decision":{"type":"fn-a-own-r-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"2", "toPosition":"3",
                "outboxTransactionId":"0"}, "intentHex":"00"});
        let q = json!({"type":A_REPLY_CONSUMER.poll_type, "status":"accepted-decision",
            "decision":{"type":"fn-a-reply-consumer-decision-v1",
                "decision":"proposed-fresh"}, "intentHex":"00"});
        let (first_kind, first_short) = classify_poll_route(&own_r, A_REPLY_CONSUMER).unwrap();
        let first = json!({"kind":first_kind, "short":first_short});
        assert_eq!(completed_stop(&first).unwrap(), None);
        let (next_kind, next_short) = classify_poll_route(&q, A_REPLY_CONSUMER).unwrap();
        let next = json!({"kind":next_kind, "short":next_short});
        assert_eq!(completed_stop(&next).unwrap(), Some(Stop::Publication));
        let empty = json!({"type":A_REPLY_CONSUMER.poll_type, "status":"skip-decision",
            "decision":{"type":"fn-empty-page-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"3", "toPosition":"4"},
            "intentHex":"00"});
        let (_, empty_short) = classify_poll_route(&empty, A_REPLY_CONSUMER).unwrap();
        assert_eq!(
            completed_stop(&json!({"kind":"skip", "short":empty_short})).unwrap(),
            Some(Stop::ShortPage)
        );
    }

    #[test]
    fn durable_preparing_reserves_new_path_after_an_orphan() {
        let root = env::temp_dir().join(format!(
            "mini-drain-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        private_dir(&pending).unwrap();
        let mut state = json!({"phase":"Preparing", "serial":0});
        save_state(&pending, &state).unwrap();
        let old = attempt(&pending, &mut state, "prepare").unwrap();
        private_dir(&old).unwrap();
        let recovered = read_json(&pending.join("state.json")).unwrap();
        let mut recovered = recovered;
        let next = attempt(&pending, &mut recovered, "prepare").unwrap();
        assert_ne!(old, next);
        assert!(old.is_dir());
        assert_eq!(
            field(&read_json(&pending.join("state.json")).unwrap(), "phase").unwrap(),
            "Preparing"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_ack_distinguishes_exact_coverage_and_missing_reply() {
        let root = env::temp_dir().join(format!(
            "mini-ack-recovery-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        private_dir(&pending).unwrap();
        let mut state = json!({"phase":"Acking", "serial":0, "txn":"123"});
        assert_eq!(retained_ack(&pending, &state).unwrap(), None);
        let ack = attempt(&pending, &mut state, "ack").unwrap();
        private_dir(&ack).unwrap();
        assert_eq!(retained_ack(&pending, &state).unwrap(), None);

        let exact = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"durable-accepted"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&exact).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Exact)
        );

        fs::remove_file(ack.join("reply.frame")).unwrap();
        let covered = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"covered-by-durable-frontier",
            "kind":"empty-page-skip", "fnCursorPosition":"16", "fnCommittedAck":"21"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&covered).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Covered)
        );
        create_private(&ack.join("ack.json"), b"different").unwrap();
        assert!(retained_ack(&pending, &state).is_err());
        fs::remove_file(ack.join("ack.json")).unwrap();
        fs::remove_file(ack.join("reply.frame")).unwrap();
        let uncertain = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"uncertain"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&uncertain).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Uncertain)
        );
        fs::remove_file(ack.join("reply.frame")).unwrap();
        let refused = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"refused"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&refused).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Refused)
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_reply_retained_ack_cannot_complete_a_b_pending_state() {
        let root = env::temp_dir().join(format!(
            "mini-a-ack-route-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        private_dir(&pending).unwrap();
        let mut state = json!({"phase":"Acking", "route":"a-reply", "serial":0, "txn":"123"});
        let ack = attempt(&pending, &mut state, "ack").unwrap();
        private_dir(&ack).unwrap();
        let exact = json!({"type":A_REPLY_CONSUMER.ack_type,
            "miniTransactionId":"123", "kind":"own-r-skip",
            "outboxTransactionId":"0", "fnStoreSequence":"0",
            "fnStoreTransactionId":"0", "fnCursorPosition":"1",
            "fnCommittedAck":"1", "fnAck":"durable-accepted"});
        let mut frame = vec![A_REPLY_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&exact).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack_route(&pending, &state, A_REPLY_CONSUMER).unwrap(),
            Some(AckEvidence::Exact)
        );
        assert!(retained_ack_route(&pending, &state, B_CONSUMER).is_err());
        let mut wrong_transaction = exact;
        wrong_transaction["miniTransactionId"] = json!("124");
        fs::write(
            ack.join("reply.frame"),
            [
                vec![A_REPLY_CONSUMER.ack_opcode],
                serde_json::to_vec(&wrong_transaction).unwrap(),
            ]
            .concat(),
        )
        .unwrap();
        assert!(retained_ack_route(&pending, &state, A_REPLY_CONSUMER).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
