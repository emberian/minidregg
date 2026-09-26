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
    for name in ["acceptedCount", "transactionId", "eventId", "imageBoundary"] {
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
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
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
    let mut temp = None;
    for number in 0..1000 {
        let path = pending.join(format!("state-{number:03}.tmp"));
        if !path.exists() {
            temp = Some(path);
            break;
        }
    }
    let temp = temp.ok_or("exhausted durable state temporary names")?;
    create_private(&temp, &bytes)?;
    fs::rename(&temp, pending.join("state.json"))
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
        let expected = match retained.get("type").and_then(Value::as_str) {
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
        };
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
    if pin_identity(&old_host, &config, &socket, &key)? != old_pin
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
    let temp_pin = (1..=999)
        .map(|index| state_dir.join(format!("pin-upgrade-{index:03}.tmp")))
        .find(|path| !path.exists())
        .ok_or("exhausted host upgrade temporary pin names")?;
    write_json_new(&temp_pin, &next_pin)?;
    sync_directory_ancestors(state_dir)?;
    if read_json(&pin_path)? != old_pin || file_digest(&pin_path)? != old_pin_sha {
        return Err("worker pin changed during host upgrade".into());
    }
    fs::rename(&temp_pin, &pin_path)
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
) -> Result<Option<String>> {
    let json = latest_retry_path(prepare)?;
    let value = retry_outcome(prepare, mode, upgrade)?;
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Ok(None);
    }
    outcome_transaction(&json)
}

fn classify_poll(value: &Value) -> Result<(String, bool)> {
    if value.get("type").and_then(Value::as_str) != Some(B_CONSUMER.poll_type) {
        return Err("unexpected B poll response type".to_owned());
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
        "skip-decision"
            if value.pointer("/decision/type").and_then(Value::as_str)
                == Some("fn-empty-page-progress-decision-v1") =>
        {
            if value.pointer("/decision/decision").and_then(Value::as_str) != Some("proposed-fresh")
            {
                return Err("historical skip has no transaction ID in poll response; operator reconciliation required".into());
            }
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
            if !(1..=16).contains(&distance) {
                return Err("skip page exceeds source poll scan bound".into());
            }
            Ok(("skip".into(), distance < 16))
        }
        "accepted-decision"
            if value
                .get("intentHex")
                .and_then(Value::as_str)
                .is_some_and(|s| !s.is_empty()) =>
        {
            Ok(("publication".into(), true))
        }
        "refused" => Err("B poll refused; retained evidence requires operator review".into()),
        _ => Err(
            "B poll cannot be advanced safely; retained evidence requires operator review".into(),
        ),
    }
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
) -> Result<()> {
    let ack = attempt(pending, state, "ack")?;
    match consumer_ack(host, config, field(state, "txn")?, &ack, B_CONSUMER) {
        Ok(()) => sync_directory_ancestors(&ack),
        Err(_) => recover_acking(host, config, pending, state),
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

fn retained_ack(pending: &Path, state: &Value) -> Result<Option<AckEvidence>> {
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
    if frame.first() != Some(&B_CONSUMER.ack_opcode) {
        return Err("retained ACK frame is not a successful B ACK reply".into());
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
            parse_ack_result(&value, B_CONSUMER, field(state, "txn")?)?;
            Ok(Some(AckEvidence::Exact))
        }
        Some("covered-by-durable-frontier") => {
            parse_ack_result(&value, B_CONSUMER, field(state, "txn")?)?;
            Ok(Some(AckEvidence::Covered))
        }
        Some(status @ ("refused" | "uncertain" | "transport-fault")) => {
            if value.get("type").and_then(Value::as_str) != Some(B_CONSUMER.ack_type)
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

fn recover_acking(host: &Path, config: &Path, pending: &Path, state: &mut Value) -> Result<()> {
    match retained_ack(pending, state) {
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
    match consumer_ack(host, config, field(state, "txn")?, &ack, B_CONSUMER) {
        Ok(()) => {
            sync_directory_ancestors(&ack)?;
            Ok(())
        }
        Err(error) => {
            let reason = match retained_ack(pending, state) {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Stop {
    Idle,
    ShortPage,
    Publication,
    PageCap,
}

pub(super) fn run(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
) -> Result<()> {
    private_dir(state_dir)?;
    let socket_dir = socket.parent().ok_or("socket lacks parent")?;
    private_dir(socket_dir)?;
    let _global = transport::service_lock(&socket_dir.join("consumer-worker.lock"))?;
    let _lock = transport::service_lock(&state_dir.join("worker.lock"))?;
    let stop = run_locked(host, config, socket, key, state_dir, max_pages)?;
    println!("consumer wake stopped: {stop:?}");
    Ok(())
}

pub(super) fn run_locked(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
) -> Result<Stop> {
    pin(state_dir, host, config, socket, key)?;
    let pending = state_dir.join("pending");
    let mut pages = 0;
    loop {
        if pages >= max_pages {
            return Ok(Stop::PageCap);
        }
        if !pending.exists() {
            private_dir(&pending)?;
            save_state(&pending, &json!({"phase":"Polling", "serial":0}))?;
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
            save_state(&pending, &json!({"phase":"Polling", "serial":0}))?;
        }
        let mut state = read_json(&state_file)?;
        match field(&state, "phase")? {
            "Polling" => {
                let path = attempt(&pending, &mut state, "poll")?;
                if let Err(error) = consumer_poll(host, config, &path, B_CONSUMER) {
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
                let (kind, short) = match classify_poll(&value) {
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
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" {
                    return Ok(Stop::Publication);
                }
                if state.get("short").and_then(Value::as_bool) == Some(true) {
                    return Ok(Stop::ShortPage);
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
                let txn = match lookup.get("type").and_then(Value::as_str) {
                    Some("confirmed") => {
                        if let Some(upgrade) = &upgrade {
                            if require_upgraded_receipt(&lookup, &upgrade.expected_fields).is_err() {
                                return hold(&pending, &mut state,
                                    "upgraded lookup confirmed a different four-field receipt; no ACK or resubmit");
                            }
                        }
                        outcome_transaction(&lookup_path)?
                            .ok_or("confirmed exact lookup lacks transaction ID")?
                    }
                    Some("absent") if upgrade.is_some() => return hold(&pending, &mut state,
                        "upgraded lookup is absent despite prior confirmed receipt; exact call retained for operator review"),
                    Some("absent") => match confirmed_after_retry(&path, "submit", None) {
                        Ok(Some(txn)) => txn,
                        Ok(None) => return hold(&pending, &mut state,
                            "same-call resubmit did not confirm; exact call retained"),
                        Err(error) => return hold(&pending, &mut state,
                            &format!("same-call resubmit uncertain; exact call retained: {error}")),
                    },
                    _ => return hold(&pending, &mut state,
                        "exact lookup did not confirm or prove absence; retained call requires operator reconciliation"),
                };
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" {
                    return Ok(Stop::Publication);
                }
                if state.get("short").and_then(Value::as_bool) == Some(true) {
                    return Ok(Stop::ShortPage);
                }
            }
            "Acking" => {
                recover_acking(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" {
                    return Ok(Stop::Publication);
                }
                if state.get("short").and_then(Value::as_bool) == Some(true) {
                    return Ok(Stop::ShortPage);
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
                "eventId":"456","imageBoundary":"789"}
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
            "eventId":"456", "imageBoundary":"789", "confirmation":"replayed"});
        let mut replay = original.clone();
        replay["confirmation"] = json!("accepted");
        let expected = confirmed_fields(&original).unwrap();
        assert!(require_upgraded_receipt(&replay, &expected).is_ok());
        for field in ["acceptedCount", "transactionId", "eventId", "imageBoundary"] {
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
}
