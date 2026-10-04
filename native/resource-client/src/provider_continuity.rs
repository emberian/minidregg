//! Admission-bound provider continuity. The Host owns history validation and
//! canonical envelope rewriting; Mini binds their exact outputs before signing.
use crate::*;
use std::os::unix::fs::{DirBuilderExt, MetadataExt};

const DESCRIPTOR_MAX: usize = 16_384;
pub(crate) const V2: &[u8] = b"DREGG/PROVIDER-CONTINUITY/v2\0";
pub(crate) const V3: &[u8] = b"DREGG/PROVIDER-CONTINUITY/v3\0";

/// Reject duplicate keys, including escaped aliases, before using a descriptor.
/// serde_json validates grammar; this scan only tracks object-key uniqueness.
fn strict_descriptor(bytes: &[u8]) -> Result<Value> {
    let value =
        serde_json::from_slice(bytes).map_err(|e| format!("invalid continuity descriptor: {e}"))?;
    let mut containers: Vec<(Option<std::collections::HashSet<String>>, bool)> = Vec::new();
    let mut cursor = 0;
    while cursor < bytes.len() {
        match bytes[cursor] {
            b'{' => containers.push((Some(std::collections::HashSet::new()), true)),
            b'[' => containers.push((None, false)),
            b'}' | b']' => {
                containers.pop();
            }
            b',' => {
                if let Some((keys, is_key)) = containers.last_mut() {
                    *is_key = keys.is_some();
                }
            }
            b'"' => {
                let start = cursor;
                cursor += 1;
                while cursor < bytes.len() && bytes[cursor] != b'"' {
                    if bytes[cursor] == b'\\' {
                        cursor += 1;
                    }
                    cursor += 1;
                }
                if let Some((Some(keys), is_key)) = containers.last_mut() {
                    if *is_key {
                        let key: String = serde_json::from_slice(&bytes[start..=cursor])
                            .map_err(|e| e.to_string())?;
                        if !keys.insert(key) {
                            return Err("duplicate continuity descriptor key".into());
                        }
                        *is_key = false;
                    }
                }
            }
            _ => {}
        }
        cursor += 1;
    }
    Ok(value)
}

fn object_keys(value: &Value, names: &[&str]) -> Result<()> {
    let object = value
        .as_object()
        .ok_or("continuity field must be an object")?;
    if object.len() != names.len() || names.iter().any(|name| !object.contains_key(*name)) {
        return Err("continuity object has missing or unknown fields".into());
    }
    Ok(())
}
fn natural<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    let s = value
        .get(name)
        .and_then(Value::as_str)
        .ok_or("continuity natural must be a string")?;
    if !mini_sdk::decimal::is_canonical_max(s, 80)
    {
        return Err(format!("noncanonical continuity natural: {name}"));
    }
    Ok(s)
}
fn bounded_regular(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let named = fs::symlink_metadata(path).map_err(|e| format!("inspect continuity input: {e}"))?;
    if !named.file_type().is_file() || named.len() > limit as u64 {
        return Err("continuity input must be a bounded regular file".into());
    }
    let mut file = File::open(path).map_err(|e| format!("open continuity input: {e}"))?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if (named.dev(), named.ino()) != (opened.dev(), opened.ino()) || !opened.is_file() {
        return Err("continuity input changed while opening".into());
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err("continuity input length exceeds bound".into());
    }
    Ok(bytes)
}
fn retained_input(value: &Value, limit: usize, destination: &Path) -> Result<Vec<u8>> {
    object_keys(value, &["path", "sha256"])?;
    let path = Path::new(
        value["path"]
            .as_str()
            .ok_or("continuity input path must be text")?,
    );
    if !path.is_absolute() {
        return Err("continuity input path must be absolute".into());
    }
    let expected = value["sha256"]
        .as_str()
        .ok_or("continuity input lacks SHA256")?;
    if expected.len() != 64
        || !mini_sdk::hex::is_lower(expected)
    {
        return Err("continuity SHA256 must be lowercase hex".into());
    }
    let bytes = bounded_regular(path, limit)?;
    if hex(&sha2::Sha256::digest(&bytes)) != expected {
        return Err("continuity input SHA256 mismatch".into());
    }
    create_private(destination, &bytes)?;
    Ok(bytes)
}
fn receipt(value: &Value) -> Result<()> {
    object_keys(
        value,
        &[
            "type",
            "transactionId",
            "eventId",
            "acceptedCount",
            "worldRoot",
        ],
    )?;
    if value["type"] != "verified-mini-native-prefix-v1" {
        return Err("unexpected continuity receipt type".into());
    }
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        natural(value, name)?;
    }
    Ok(())
}
fn pair(first: &[u8], second: &[u8]) -> Result<Vec<u8>> {
    let len: u32 = first
        .len()
        .try_into()
        .map_err(|_| "continuity pair too large")?;
    let mut bytes = len.to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    Ok(bytes)
}
/// Legacy callers keep API17's original exact call/outcome pair.
pub(crate) fn request_payload(
    call: &[u8],
    outcome: &[u8],
    fence: Option<(&[u8], &[u8])>,
    v2: bool,
) -> Result<Vec<u8>> {
    let reserve = pair(call, outcome)?;
    let bytes = if v2 {
        let fence = match fence {
            Some((c, o)) => pair(c, o)?,
            None => Vec::new(),
        };
        let mut result = V2.to_vec();
        result.extend(pair(&reserve, &fence)?);
        result
    } else {
        if fence.is_some() {
            return Err("legacy continuity does not accept a fence".into());
        }
        reserve
    };
    if bytes.len() + 1 > transport::HOST_MAX_FRAME {
        return Err("continuity request exceeds frame bound".into());
    }
    Ok(bytes)
}
pub(crate) fn resolution_payload(v2_payload: &[u8], previous: &Value) -> Result<Vec<u8>> {
    let body = v2_payload
        .strip_prefix(V2)
        .ok_or("resolution needs exact v2 reserve/fence input")?;
    let count = natural(previous, "checkedAcceptedCount")?;
    let root = natural(previous, "checkedWorldRoot")?;
    if count == "0" {
        return Err("original continuity prefix must be nonzero".into());
    }
    let point = pair(count.as_bytes(), root.as_bytes())?;
    let mut wire = V3.to_vec();
    wire.extend(pair(body, &point)?);
    if wire.len() + 1 > transport::HOST_MAX_FRAME {
        return Err("resolution request exceeds frame bound".into());
    }
    Ok(wire)
}
fn verify_prior_checked(fresh: &Value, previous: &Value) -> Result<()> {
    let expected = json!({"acceptedCount":natural(previous,"checkedAcceptedCount")?,"worldRoot":natural(previous,"checkedWorldRoot")?});
    if fresh.get("priorChecked") != Some(&expected) {
        return Err(
            "native continuity reply does not prove the original prepared prefix; keep Pending"
                .into(),
        );
    }
    Ok(())
}
fn proof(value: &Value, name: &str, directory: &Path) -> Result<(Vec<u8>, Vec<u8>)> {
    object_keys(value, &["call", "outcome", "receipt"])?;
    receipt(&value["receipt"])?;
    Ok((
        retained_input(
            &value["call"],
            transport::HOST_MAX_FRAME,
            &directory.join(format!("{name}-call.bin")),
        )?,
        retained_input(
            &value["outcome"],
            1024,
            &directory.join(format!("{name}-outcome.bin")),
        )?,
    ))
}

fn verify_prefix(value: &Value, descriptor: &Value) -> Result<()> {
    if !continuity_reply(value)? {
        return Err("provider continuity refused; evidence retained".into());
    }
    if value["providerResourceId"] != descriptor["providerResourceId"]
        || value["anchor"] != descriptor["reserve"]["receipt"]
    {
        return Err("continuity reply does not bind the original reserve".into());
    }
    let expected = if descriptor["fence"].is_null() {
        &Value::Null
    } else {
        &descriptor["fence"]["receipt"]
    };
    if value.get("allowedFence") != Some(expected) {
        return Err("continuity reply does not bind the exact allowed fence".into());
    }
    Ok(())
}
fn verify_reply(value: &Value, descriptor: &Value, original: &Value) -> Result<()> {
    verify_prefix(value, descriptor)?;
    if value["checkedWorldRoot"] != original["worldRoot"] {
        return Err("continuity reply does not bind the original plan world".into());
    }
    Ok(())
}
fn verify_pinned(original: &Value, pinned: &Value) -> Result<()> {
    let height = natural(original, "height")?;
    natural(original, "worldRoot")?;
    let mut expected = original.clone();
    let original_slots = original["slots"]
        .as_array()
        .ok_or("original plan lacks slots")?;
    let slots = pinned["slots"]
        .as_array()
        .ok_or("pinned plan lacks slots")?;
    if slots.is_empty() || slots.len() != original_slots.len() {
        return Err("pinned plan slot count changed or empty".into());
    }
    for (index, (before, after)) in original_slots.iter().zip(slots).enumerate() {
        let deadline = natural(&before["signing"], "validUntil")?;
        let tightened = if (deadline.len(), deadline) < (height.len(), height) {
            deadline
        } else {
            height
        };
        if before["signing"]["decoded"] != true
            || after["signing"]["decoded"] != true
            || before["header"] != before["signing"]["canonical"]
            || after["header"] != after["signing"]["canonical"]
            || after["signing"]["validUntil"].as_str() != Some(tightened)
        {
            return Err("pinned plan has invalid canonical envelope or deadline".into());
        }
        // Header bytes are produced by the pinned source Host. Everything it
        // decodes besides validUntil must remain byte-for-byte JSON identical.
        expected["slots"][index]["header"] = after["header"].clone();
        expected["slots"][index]["signing"]["canonical"] = after["signing"]["canonical"].clone();
        expected["slots"][index]["signing"]["validUntil"] = Value::String(tightened.into());
    }
    if expected != *pinned {
        return Err("pin-plan-height changed another plan binding".into());
    }
    plan_headers(pinned)?;
    Ok(())
}

fn require_before_signing(directory: &Path) -> Result<()> {
    for name in [
        "call.bin",
        "transaction-signatures.bin",
        "transaction-signatures.json",
        "outcome.bin",
        "outcome.json",
    ] {
        match fs::symlink_metadata(directory.join(name)) {
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(format!(
                    "continuity rejection cannot precede existing {name}"
                ))
            }
            Err(error) => return Err(format!("cannot establish absent {name}: {error}")),
        }
    }
    Ok(())
}
fn rejection_binding(directory: &Path, name: &str, limit: usize) -> Result<Value> {
    let bytes = bounded_regular(&directory.join(name), limit)?;
    Ok(json!({"path":name,"sha256":hex(&sha2::Sha256::digest(&bytes))}))
}
/// Called only after guard returns Err. That caller immediately returns; it
/// cannot proceed into transaction signing, assembly, or submission. This is
/// positive source-client evidence, not an inference from missing call bytes.
/// The runtime must revalidate every binding and late-artifact absence before
/// retiring Pending, while preserving the actual provider allowance.
pub(crate) fn retain_rejection(directory: &Path, intent: &Path) -> Result<()> {
    let intent_name = if intent == directory.join("intent.json") {
        "intent.json"
    } else if intent == directory.join("intent-source.bin") {
        "intent-source.bin"
    } else {
        return Err("continuity rejection intent is not the retained source".into());
    };
    require_before_signing(directory)?;
    let names = [
        ("intent", intent_name, transport::HOST_MAX_FRAME),
        ("config", "config.json", 65_536),
        ("manifest", "attempt.json", 65_536),
        (
            "descriptor",
            "provider-continuity/descriptor.json",
            DESCRIPTOR_MAX,
        ),
        (
            "originalPlan",
            "original-plan.bin",
            transport::HOST_MAX_FRAME,
        ),
        (
            "originalPlanPresentation",
            "original-plan.json",
            4 * transport::HOST_MAX_FRAME,
        ),
    ];
    let manifest: Value =
        serde_json::from_slice(&bounded_regular(&directory.join("attempt.json"), 65_536)?)
            .map_err(|e| format!("invalid continuity attempt manifest: {e}"))?;
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["config"].as_str().map(PathBuf::from)
            != Some(absolute(&directory.join("config.json"))?)
    {
        return Err("continuity rejection does not name a retained submit attempt".into());
    }
    let mut marker = json!({"type":"minidregg-provider-continuity-rejection-v1",
        "stage":"before-signing","heldAllowanceReleased":false,"reason":"continuity-gate-rejected"});
    for (field, name, limit) in names {
        marker[field] = rejection_binding(directory, name, limit)?;
    }
    // Refuse partial evidence or an input changed during custody. Later changes
    // are detected by the runtime against these exact hashes.
    for (field, name, limit) in names {
        if marker[field] != rejection_binding(directory, name, limit)? {
            return Err(format!("continuity rejection input changed: {name}"));
        }
    }
    require_before_signing(directory)?;
    let mut bytes = serde_json::to_vec_pretty(&marker).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(
        &directory.join("provider-continuity-rejection.json"),
        &bytes,
    )?;
    sync_directory_ancestors(directory)
}

fn descriptor_payload(descriptor: &Value, evidence: &Path) -> Result<Vec<u8>> {
    object_keys(
        descriptor,
        &["type", "providerResourceId", "reserve", "fence"],
    )?;
    if descriptor["type"] != "mini-provider-continuity-v1"
        || natural(descriptor, "providerResourceId")? == "0"
    {
        return Err("invalid provider continuity descriptor identity".into());
    }
    let reserve = proof(&descriptor["reserve"], "reserve", evidence)?;
    let fence = if descriptor["fence"].is_null() {
        None
    } else {
        Some(proof(&descriptor["fence"], "fence", evidence)?)
    };
    let payload = request_payload(
        &reserve.0,
        &reserve.1,
        fence.as_ref().map(|(c, o)| (c.as_slice(), o.as_slice())),
        true,
    )?;
    Ok(payload)
}

pub(crate) fn guard(
    host: &Path,
    config: &Path,
    descriptor_path: &Path,
    directory: &Path,
    original_bin: &Path,
    original: &Value,
    plan_bin: &Path,
    plan_json: &Path,
) -> Result<Value> {
    let socket = SOCKET
        .get()
        .ok_or("provider continuity requires --socket")?;
    let evidence = directory.join("provider-continuity");
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&evidence)
        .map_err(|e| e.to_string())?;
    let bytes = bounded_regular(descriptor_path, DESCRIPTOR_MAX)?;
    create_private(&evidence.join("descriptor.json"), &bytes)?;
    let descriptor = strict_descriptor(&bytes)?;
    let payload = descriptor_payload(&descriptor, &evidence)?;
    create_private(&evidence.join("request.bin"), &payload)?;
    sync_directory_ancestors(&evidence)?;
    let frame = session_invoke(host, socket, config, 17, &payload)?;
    create_private(&evidence.join("reply.frame"), &frame)?;
    if frame.first() != Some(&17) {
        return Err("Host refused continuity; exact frame retained".into());
    }
    let answer: Value = serde_json::from_slice(&frame[1..])
        .map_err(|e| format!("invalid continuity reply: {e}"))?;
    create_private(&evidence.join("continuity.json"), &frame[1..])?;
    verify_reply(&answer, &descriptor, original)?;
    // This helper is stateless and must run against the pinned native image,
    // not be interpreted as a new Store prepare by socket_process.
    let output = Command::new(host)
        .arg(config)
        .arg("pin-plan-height")
        .arg(original_bin)
        .arg(plan_bin)
        .output()
        .map_err(|e| format!("cannot run native plan pinning: {e}"))?;
    if !output.status.success() {
        return Err(format!(
            "native plan pinning failed: {}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let pinned = inspect(host, config, "plan", plan_bin, plan_json)?;
    verify_pinned(original, &pinned)?;
    sync_retained_call(directory, plan_bin)?;
    Ok(pinned)
}

// Read-only resolution keeps the retained signed call immutable. The physical
// caller still binds this report to its current Pending and held request.
fn expiration(
    profile: &Value,
    original_prefix: &Value,
    pinned: &Value,
    fresh_prefix: &Value,
) -> Result<Value> {
    if profile["providerContinuityAdmission"] != "exact-height-v1" {
        return Err("Host does not advertise exact-height continuity admission".into());
    }
    let genesis = natural(profile, "genesisHeight")?;
    let old_count = natural(original_prefix, "checkedAcceptedCount")?;
    let new_count = natural(fresh_prefix, "checkedAcceptedCount")?;
    if mini_sdk::decimal::add(genesis, old_count)? != natural(pinned, "height")?
        || mini_sdk::decimal::compare(new_count, old_count) != std::cmp::Ordering::Greater
    {
        return Err(
            "continuity resolution has no extension of the original admission prefix".into(),
        );
    }
    let current_height = mini_sdk::decimal::add(genesis, new_count)?;
    let slots = pinned["slots"]
        .as_array()
        .ok_or("retained signed plan lacks slots")?;
    if slots.is_empty() {
        return Err("retained signed plan has no deadlines".into());
    }
    let mut deadlines = Vec::new();
    for slot in slots {
        let deadline = natural(&slot["signing"], "validUntil")?;
        if slot["signing"]["decoded"] != true
            || slot["header"] != slot["signing"]["canonical"]
            || mini_sdk::decimal::compare(&current_height, deadline) != std::cmp::Ordering::Greater
        {
            return Err("at least one actual signed deadline has not expired".into());
        }
        deadlines.push(deadline);
    }
    Ok(
        json!({"genesisHeight":genesis,"originalAcceptedCount":old_count,"checkedAcceptedCount":new_count,
        "checkedHeight":current_height,"signedDeadlines":deadlines}),
    )
}
fn resolution_lookup(value: &Value) -> Result<bool> {
    match value["type"].as_str() {
        Some("confirmed") => {
            if !matches!(
                value["confirmation"].as_str(),
                Some("installed" | "replayed")
            ) {
                return Err("exact lookup has no native confirmation kind".into());
            }
            for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
                natural(value, field)?;
            }
            Ok(true)
        }
        Some("absent") if value.as_object().is_some_and(|obj| obj.len() == 1) => Ok(false),
        _ => Err("exact lookup is neither confirmed nor native absent; keep Pending".into()),
    }
}
fn require_contention(value: &Value) -> Result<()> {
    if value["type"] == "contention" && value.as_object().is_some_and(|obj| obj.len() == 1) {
        Ok(())
    } else {
        Err("retained native outcome is not exact typed contention".into())
    }
}
fn copy_resolution_input(
    attempt: &Path,
    kept: &Path,
    name: &str,
    limit: usize,
    inputs: &mut Value,
) -> Result<Vec<u8>> {
    let from = attempt.join(name);
    let to = kept.join(name);
    let bytes = bounded_regular(&from, limit)?;
    create_private(&to, &bytes)?;
    inputs[name] = json!({"path":absolute(&from)?,"retainedPath":absolute(&to)?,"sha256":hex(&sha2::Sha256::digest(&bytes))});
    Ok(bytes)
}
fn protect_native_evidence(path: &Path) -> Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let named = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !named.file_type().is_file() {
        return Err("native resolution evidence must be regular".into());
    }
    let file = File::open(path).map_err(|e| e.to_string())?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !opened.is_file() || (opened.dev(), opened.ino()) != (named.dev(), named.ino()) {
        return Err("native resolution evidence changed while opening".into());
    }
    file.set_permissions(fs::Permissions::from_mode(0o600))
        .and_then(|()| file.sync_all())
        .map_err(|e| e.to_string())
}
fn inspect_private(
    host: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
) -> Result<Value> {
    let value = inspect(host, config, kind, input, output)?;
    protect_native_evidence(output)?;
    Ok(value)
}
fn evidence_file(path: &Path) -> Result<Value> {
    protect_native_evidence(path)?;
    let bytes = bounded_regular(path, 4 * transport::HOST_MAX_FRAME)?;
    Ok(json!({"path":absolute(path)?,"sha256":hex(&sha2::Sha256::digest(&bytes))}))
}
fn recheck_resolution_inputs(inputs: &Value) -> Result<()> {
    for binding in inputs
        .as_object()
        .ok_or("resolution bindings absent")?
        .values()
    {
        let path = Path::new(binding["path"].as_str().ok_or("resolution path absent")?);
        let actual = hex(&sha2::Sha256::digest(bounded_regular(
            path,
            4 * transport::HOST_MAX_FRAME,
        )?));
        if Some(actual.as_str()) != binding["sha256"].as_str() {
            return Err("guarded attempt changed during read-only resolution".into());
        }
    }
    Ok(())
}
fn settlement_source(intent: &Value, descriptor: &Value) -> Result<Value> {
    let grain = &intent["grain"];
    if grain["operation"]["type"] != "settle"
        || grain["task"] != descriptor["providerResourceId"]
        || grain["publications"]
            .as_array()
            .is_none_or(|items| !items.is_empty())
    {
        return Err("contention retirement requires the exact provider settlement source".into());
    }
    Ok(grain.clone())
}
fn verify_settlement_command(pinned: &Value, authored: &[u8]) -> Result<()> {
    if pinned["finalizedDraft"]["type"] != "invoke"
        || pinned["finalizedDraft"]["command"].as_str() != Some(hex(authored).as_str())
    {
        return Err(
            "signed plan does not contain the exact native-authored settlement command".into(),
        );
    }
    Ok(())
}
fn verify_resolution_environment(host: &Path, config: &Path, report: &Value) -> Result<()> {
    let actual_host = host_image_sha256(host)?;
    let actual_config = hex(&sha2::Sha256::digest(bounded_regular(config, 65536)?));
    if report["hostSha256"].as_str() != Some(actual_host.as_str())
        || report["configSha256"].as_str() != Some(actual_config.as_str())
    {
        return Err("selected Host or configuration changed during resolution".into());
    }
    Ok(())
}
fn finish_resolution(directory: &Path, report: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(report).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(&directory.join("resolution.json"), &bytes)?;
    sync_directory_ancestors(directory)?;
    print_json(report)
}

/// Read-only native evidence for a guarded attempt. No key parameter exists;
/// the only assembly uses already-retained signatures and is never submitted.
pub(crate) fn resolve_attempt(
    host: &Path,
    config: &Path,
    attempt: &Path,
    directory: &Path,
) -> Result<()> {
    let socket = SOCKET
        .get()
        .ok_or("provider continuity resolution requires --socket")?;
    let selected_host_sha = host_image_sha256(host)?;
    let attempt = absolute(attempt)?;
    let metadata = fs::symlink_metadata(&attempt).map_err(|e| e.to_string())?;
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    if !metadata.file_type().is_dir()
        || metadata.uid() != unsafe { geteuid() }
        || metadata.mode() & 0o077 != 0
    {
        return Err("guarded attempt must be an owned private directory".into());
    }
    fs::DirBuilder::new()
        .mode(0o700)
        .create(directory)
        .map_err(|e| e.to_string())?;
    let kept = directory.join("retained");
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&kept)
        .map_err(|e| e.to_string())?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(kept.join("provider-continuity"))
        .map_err(|e| e.to_string())?;
    let mut inputs = json!({});
    let manifest_bytes =
        copy_resolution_input(&attempt, &kept, "attempt.json", 65_536, &mut inputs)?;
    let config_bytes = copy_resolution_input(&attempt, &kept, "config.json", 65_536, &mut inputs)?;
    copy_resolution_input(
        &attempt,
        &kept,
        "intent.json",
        transport::HOST_MAX_FRAME,
        &mut inputs,
    )?;
    let call = copy_resolution_input(
        &attempt,
        &kept,
        "call.bin",
        transport::HOST_MAX_FRAME,
        &mut inputs,
    )?;
    let manifest = strict_descriptor(&manifest_bytes)?;
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["host"].as_str().map(Path::new) != Some(absolute(host)?.as_path())
        || manifest["config"].as_str().map(Path::new) != Some(attempt.join("config.json").as_path())
        || manifest["socket"].as_str() != Some(transport::pinned_address(socket)?.as_str())
        || config_bytes != bounded_regular(config, 65_536)?
    {
        return Err("guarded attempt differs from selected Host/config/socket".into());
    }
    let copied_config = kept.join("config.json");
    // Exact lookup comes before expiry and negative evidence. It cannot submit.
    let lookup_bin = directory.join("lookup.bin");
    let lookup_json = directory.join("lookup.json");
    host_files(
        host,
        &copied_config,
        &[Path::new("lookup"), &kept.join("call.bin"), &lookup_bin],
    )?;
    let lookup = inspect_private(host, &copied_config, "outcome", &lookup_bin, &lookup_json)?;
    let mut report = json!({"type":"mini-provider-continuity-resolution-v1","attempt":attempt,
        "host":absolute(host)?,"hostSha256":selected_host_sha,"config":absolute(config)?,
        "configSha256":hex(&sha2::Sha256::digest(&config_bytes)),"socket":transport::pinned_address(socket)?,
        "heldAllowanceReleased":false,"providerRequestRepeated":false,
        "lookup":{"binary":evidence_file(&lookup_bin)?,"presentation":evidence_file(&lookup_json)?,"outcome":lookup}});
    if resolution_lookup(&lookup)? {
        recheck_resolution_inputs(&inputs)?;
        report["decision"] = json!("already-confirmed");
        report["inputs"] = inputs;
        verify_resolution_environment(host, config, &report)?;
        return finish_resolution(directory, &report);
    }
    for (name, limit) in [
        ("original-plan.bin", transport::HOST_MAX_FRAME),
        ("original-plan.json", 4 * transport::HOST_MAX_FRAME),
        ("plan.bin", transport::HOST_MAX_FRAME),
        ("plan.json", 4 * transport::HOST_MAX_FRAME),
        ("transaction-signatures.bin", transport::HOST_MAX_FRAME),
        ("transaction-signatures.json", transport::HOST_MAX_FRAME),
        ("outcome.bin", 65_536),
        ("outcome.json", 65_536),
        ("provider-continuity/descriptor.json", DESCRIPTOR_MAX),
        ("provider-continuity/request.bin", transport::HOST_MAX_FRAME),
        ("provider-continuity/reply.frame", 65_536),
        ("provider-continuity/continuity.json", 65_536),
        (
            "provider-continuity/reserve-call.bin",
            transport::HOST_MAX_FRAME,
        ),
        ("provider-continuity/reserve-outcome.bin", 1024),
    ] {
        copy_resolution_input(&attempt, &kept, name, limit, &mut inputs)?;
    }
    let read_json = |name: &str| -> Result<Value> {
        strict_descriptor(&bounded_regular(
            &kept.join(name),
            4 * transport::HOST_MAX_FRAME,
        )?)
    };
    let descriptor = read_json("provider-continuity/descriptor.json")?;
    if !descriptor["fence"].is_null() {
        for (name, limit) in [
            (
                "provider-continuity/fence-call.bin",
                transport::HOST_MAX_FRAME,
            ),
            ("provider-continuity/fence-outcome.bin", 1024),
        ] {
            copy_resolution_input(&attempt, &kept, name, limit, &mut inputs)?;
        }
    }
    let native_outcome = inspect_private(
        host,
        &copied_config,
        "outcome",
        &kept.join("outcome.bin"),
        &directory.join("retained-outcome-inspected.json"),
    )?;
    require_contention(&native_outcome)?;
    if native_outcome != read_json("outcome.json")? {
        return Err("retained contention presentation differs from native bytes".into());
    }
    let original = inspect_private(
        host,
        &copied_config,
        "plan",
        &kept.join("original-plan.bin"),
        &directory.join("original-plan-inspected.json"),
    )?;
    let pinned = inspect_private(
        host,
        &copied_config,
        "plan",
        &kept.join("plan.bin"),
        &directory.join("pinned-plan-inspected.json"),
    )?;
    if original != read_json("original-plan.json")? || pinned != read_json("plan.json")? {
        return Err("retained plan presentation differs from native plan bytes".into());
    }
    verify_pinned(&original, &pinned)?;
    let grain = settlement_source(&read_json("intent.json")?, &descriptor)?;
    let grain_json = directory.join("settlement-grain.json");
    create_private(
        &grain_json,
        &serde_json::to_vec(&grain).map_err(|e| e.to_string())?,
    )?;
    let grain_command = directory.join("settlement-command.bin");
    author(
        host,
        &copied_config,
        OsStr::new("grain"),
        &grain_json,
        &grain_command,
    )?;
    verify_settlement_command(
        &pinned,
        &bounded_regular(&grain_command, transport::HOST_MAX_FRAME)?,
    )?;
    let reassembled = directory.join("reassembled-call.bin");
    let assembled = Command::new(host)
        .arg(&copied_config)
        .arg("assemble")
        .arg(kept.join("plan.bin"))
        .arg(kept.join("transaction-signatures.bin"))
        .arg(&reassembled)
        .output()
        .map_err(|e| e.to_string())?;
    if !assembled.status.success()
        || bounded_regular(&reassembled, transport::HOST_MAX_FRAME)? != call
    {
        return Err(
            "retained signed plan and signatures do not reassemble the exact original call".into(),
        );
    }
    let old_frame = bounded_regular(&kept.join("provider-continuity/reply.frame"), 65_536)?;
    if old_frame.first() != Some(&17) {
        return Err("original continuity frame is not API17 evidence".into());
    }
    let old_prefix = strict_descriptor(&old_frame[1..])?;
    if old_prefix != read_json("provider-continuity/continuity.json")? {
        return Err("original continuity presentation differs from frame".into());
    }
    verify_reply(&old_prefix, &descriptor, &original)?;
    let fresh_dir = directory.join("fresh-continuity");
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&fresh_dir)
        .map_err(|e| e.to_string())?;
    let payload = descriptor_payload(&descriptor, &fresh_dir)?;
    // The original proof must have used these same exact reserve/fence inputs.
    if payload
        != bounded_regular(
            &kept.join("provider-continuity/request.bin"),
            transport::HOST_MAX_FRAME,
        )?
    {
        return Err(
            "original continuity request differs from exact reserve/fence descriptor".into(),
        );
    }
    for name in [
        "reserve-call.bin",
        "reserve-outcome.bin",
        "fence-call.bin",
        "fence-outcome.bin",
    ] {
        if name.starts_with("fence") && descriptor["fence"].is_null() {
            continue;
        }
        if bounded_regular(&fresh_dir.join(name), transport::HOST_MAX_FRAME)?
            != bounded_regular(
                &kept.join("provider-continuity").join(name),
                transport::HOST_MAX_FRAME,
            )?
        {
            return Err("original continuity input differs from fresh exact proof input".into());
        }
    }
    let payload = resolution_payload(&payload, &old_prefix)?;
    create_private(&fresh_dir.join("request.bin"), &payload)?;
    let frame = session_invoke(host, socket, &copied_config, 17, &payload)?;
    create_private(&fresh_dir.join("reply.frame"), &frame)?;
    if frame.first() != Some(&17) {
        return Err("fresh continuity refused; keep Pending".into());
    }
    let fresh_prefix = strict_descriptor(&frame[1..])?;
    create_private(&fresh_dir.join("continuity.json"), &frame[1..])?;
    verify_prefix(&fresh_prefix, &descriptor)?;
    let profile_output = host_words(host, &copied_config, &["profile"])?;
    create_private(&directory.join("profile.json"), &profile_output.stdout)?;
    let profile = strict_descriptor(&profile_output.stdout)?;
    let expired = expiration(&profile, &old_prefix, &pinned, &fresh_prefix)?;
    verify_prior_checked(&fresh_prefix, &old_prefix)?;
    recheck_resolution_inputs(&inputs)?;
    report["decision"] = json!("retire-expired-contention");
    report["inputs"] = inputs;
    report["originalPrefix"] = old_prefix;
    report["freshPrefix"] = fresh_prefix;
    report["expiration"] = expired;
    report["freshProof"] = json!({"request":evidence_file(&fresh_dir.join("request.bin"))?,"frame":evidence_file(&fresh_dir.join("reply.frame"))?,"presentation":evidence_file(&fresh_dir.join("continuity.json"))?});
    report["settlementCommand"] = evidence_file(&grain_command)?;
    report["reassembledCall"] = evidence_file(&reassembled)?;
    report["profile"] = evidence_file(&directory.join("profile.json"))?;
    verify_resolution_environment(host, config, &report)?;
    finish_resolution(directory, &report)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn anchor(n: &str) -> Value {
        json!({"type":"verified-mini-native-prefix-v1","transactionId":n,"eventId":"2","acceptedCount":"3","worldRoot":"4"})
    }
    fn descriptor() -> Value {
        json!({"type":"mini-provider-continuity-v1","providerResourceId":"14","reserve":{"receipt":anchor("1")},"fence":null})
    }
    fn answer() -> Value {
        json!({"type":"minidregg-provider-continuity-v1","status":"confirmed","continuous":true,"reason":"","providerResourceId":"14","anchor":anchor("1"),"allowedFence":null,"checkedWorldRoot":"42","checkedAcceptedCount":"7"})
    }
    fn plan() -> Value {
        json!({"domain":"1","semantics":"2","height":"7","worldRoot":"42","finalizedDraft":{"type":"invoke","command":"aabb"},"slots":[{"role":"1","index":"0","header":"aa","signing":{"decoded":true,"canonical":"aa","validUntil":"99","message":"bb","keyId":"8","nullifier":"9"}}]})
    }
    fn pinned() -> Value {
        let mut value = plan();
        value["slots"][0]["header"] = json!("cc");
        value["slots"][0]["signing"]["canonical"] = json!("cc");
        value["slots"][0]["signing"]["validUntil"] = json!("7");
        value
    }
    #[test]
    fn native_resolution_outputs_are_private_even_when_created_public() {
        use std::os::unix::fs::PermissionsExt;
        let dir = rejected_fixture();
        let native = dir.join("native-output.bin");
        fs::write(&native, b"native output").unwrap();
        fs::set_permissions(&native, fs::Permissions::from_mode(0o644)).unwrap();
        let retained = evidence_file(&native).unwrap();
        assert_eq!(fs::metadata(&native).unwrap().mode() & 0o777, 0o600);
        assert_eq!(
            retained["sha256"],
            hex(&sha2::Sha256::digest(b"native output"))
        );
        let link = dir.join("alias.bin");
        std::os::unix::fs::symlink(&native, &link).unwrap();
        assert!(evidence_file(&link).is_err());
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn resolution_v3_requires_exact_prior_prefix_not_just_larger_count() {
        let old = answer();
        let v2 = request_payload(b"r", b"o", None, true).unwrap();
        let wire = resolution_payload(&v2, &old).unwrap();
        let point = pair(b"7", b"42").unwrap();
        let mut expected = b"DREGG/PROVIDER-CONTINUITY/v3\0".to_vec();
        expected.extend(pair(v2.strip_prefix(V2).unwrap(), &point).unwrap());
        assert_eq!(wire, expected);
        let mut fresh = answer();
        fresh["checkedAcceptedCount"] = json!("999");
        assert!(verify_prior_checked(&fresh, &old).is_err());
        fresh["priorChecked"] = json!({"acceptedCount":"7","worldRoot":"42"});
        verify_prior_checked(&fresh, &old).unwrap();
        for point in [
            json!({"acceptedCount":"8","worldRoot":"42"}),
            json!({"acceptedCount":"7","worldRoot":"43"}),
            json!({"acceptedCount":"7","worldRoot":"42","extra":true}),
            Value::Null,
        ] {
            fresh["priorChecked"] = point;
            assert!(verify_prior_checked(&fresh, &old).is_err());
        }
        let mut zero = old.clone();
        zero["checkedAcceptedCount"] = json!("0");
        assert!(resolution_payload(&v2, &zero).is_err());
    }
    #[test]
    fn resolution_requires_exact_native_outcome_variants() {
        assert!(!resolution_lookup(&json!({"type":"absent"})).unwrap());
        let confirmed = json!({"type":"confirmed","confirmation":"replayed","transactionId":"1","eventId":"2","acceptedCount":"8","worldRoot":"9"});
        assert!(resolution_lookup(&confirmed).unwrap());
        for value in [
            json!({"type":"absent","reason":"unknown"}),
            json!({"type":"refused"}),
            json!({"type":"uncertain"}),
            json!({"type":"confirmed"}),
            json!({"type":"contention"}),
        ] {
            assert!(resolution_lookup(&value).is_err());
        }
        require_contention(&json!({"type":"contention"})).unwrap();
        for value in [
            json!({"type":"absent"}),
            json!({"type":"uncertain"}),
            json!({"type":"contention","reason":"conflict"}),
        ] {
            assert!(require_contention(&value).is_err());
        }
    }
    #[test]
    fn expiration_requires_native_height_relation_and_every_signed_deadline() {
        let profile = json!({"providerContinuityAdmission":"exact-height-v1","genesisHeight":"0"});
        let old = answer();
        let mut fresh = answer();
        fresh["checkedAcceptedCount"] = json!("8");
        assert_eq!(
            expiration(&profile, &old, &pinned(), &fresh).unwrap()["checkedHeight"],
            "8"
        );
        assert!(expiration(&profile, &old, &pinned(), &old).is_err());
        let mut bad = fresh.clone();
        bad["checkedAcceptedCount"] = json!("6");
        assert!(expiration(&profile, &old, &pinned(), &bad).is_err());
        let mut bad_profile = profile.clone();
        bad_profile["genesisHeight"] = json!("1");
        assert!(expiration(&bad_profile, &old, &pinned(), &fresh).is_err());
        for deadline in ["8", "9", "08"] {
            let mut bad_plan = pinned();
            bad_plan["slots"][0]["signing"]["validUntil"] = json!(deadline);
            assert!(expiration(&profile, &old, &bad_plan, &fresh).is_err());
        }
        let mut bad_plan = pinned();
        let mut later = bad_plan["slots"][0].clone();
        later["signing"]["validUntil"] = json!("9");
        bad_plan["slots"].as_array_mut().unwrap().push(later);
        assert!(expiration(&profile, &old, &bad_plan, &fresh).is_err());
        assert_eq!(
            mini_sdk::decimal::add("999999999999999999999999999999999999999999", "1").unwrap(),
            "1000000000000000000000000000000000000000000"
        );
    }
    #[test]
    fn retirement_only_accepts_exact_provider_settlement_native_command() {
        let intent = json!({"grain":{"task":"14","operation":{"type":"settle"},"publications":[]}});
        settlement_source(&intent, &descriptor()).unwrap();
        for (field, value) in [
            ("task", json!("15")),
            ("operation", json!({"type":"disconnect"})),
            ("publications", json!([{}])),
        ] {
            let mut bad = intent.clone();
            bad["grain"][field] = value;
            assert!(settlement_source(&bad, &descriptor()).is_err());
        }
        verify_settlement_command(&pinned(), &[0xaa, 0xbb]).unwrap();
        assert!(verify_settlement_command(&pinned(), &[0xaa, 0xbc]).is_err());
        let mut noninvoke = pinned();
        noninvoke["finalizedDraft"]["type"] = json!("delegate");
        assert!(verify_settlement_command(&noninvoke, &[0xaa, 0xbb]).is_err());
    }
    #[test]
    fn resolution_rechecks_every_original_input_and_refuses_symlinks() {
        let dir = rejected_fixture();
        let mut inputs = json!({});
        let kept = dir.join("copy");
        fs::create_dir(&kept).unwrap();
        for name in ["intent.json", "config.json", "original-plan.bin"] {
            copy_resolution_input(&dir, &kept, name, 65536, &mut inputs).unwrap();
        }
        recheck_resolution_inputs(&inputs).unwrap();
        for name in ["intent.json", "config.json", "original-plan.bin"] {
            let path = dir.join(name);
            let bytes = fs::read(&path).unwrap();
            fs::write(&path, b"changed").unwrap();
            assert!(recheck_resolution_inputs(&inputs).is_err());
            fs::write(&path, &bytes).unwrap();
        }
        fs::remove_file(dir.join("original-plan.bin")).unwrap();
        std::os::unix::fs::symlink(
            kept.join("original-plan.bin"),
            dir.join("original-plan.bin"),
        )
        .unwrap();
        assert!(recheck_resolution_inputs(&inputs).is_err());
        fs::remove_dir_all(dir).unwrap();
    }
    #[test]
    fn reply_binds_provider_original_reserve_fence_and_original_world() {
        let d = descriptor();
        let a = answer();
        let p = plan();
        verify_reply(&a, &d, &p).unwrap();
        for (field, value) in [
            ("providerResourceId", json!("15")),
            ("anchor", anchor("8")),
            ("allowedFence", anchor("9")),
            ("checkedWorldRoot", json!("43")),
            ("continuous", json!(false)),
        ] {
            let mut changed = a.clone();
            changed[field] = value;
            assert!(verify_reply(&changed, &d, &p).is_err(), "{field}");
        }
        let mut fenced = d.clone();
        fenced["fence"] = json!({"receipt":anchor("9")});
        assert!(verify_reply(&a, &fenced, &p).is_err());
        let mut aa = a;
        aa["allowedFence"] = anchor("9");
        verify_reply(&aa, &fenced, &p).unwrap();
        let mut changed_plan = p;
        changed_plan["worldRoot"] = json!("44");
        assert!(verify_reply(&aa, &fenced, &changed_plan).is_err());
    }
    #[test]
    fn only_deadline_and_its_native_canonical_encoding_can_change() {
        let p = plan();
        let tightened = pinned();
        verify_pinned(&p, &tightened).unwrap();
        for (field, value) in [
            ("domain", json!("2")),
            ("height", json!("8")),
            ("worldRoot", json!("43")),
            ("finalizedDraft", json!({"type":"invoke","command":"cc"})),
        ] {
            let mut bad = tightened.clone();
            bad[field] = value;
            assert!(verify_pinned(&p, &bad).is_err(), "{field}");
        }
        for (field, value) in [
            ("message", json!("dd")),
            ("validUntil", json!("8")),
            ("validUntil", json!("6")),
            ("canonical", json!("ee")),
            ("keyId", json!("18")),
            ("nullifier", json!("19")),
            ("decoded", json!(false)),
        ] {
            let mut bad = tightened.clone();
            bad["slots"][0]["signing"][field] = value;
            assert!(verify_pinned(&p, &bad).is_err(), "{field}");
        }
        let mut bad = tightened;
        bad["slots"][0]["role"] = json!("2");
        assert!(verify_pinned(&p, &bad).is_err());
        let mut short = plan();
        short["slots"][0]["signing"]["validUntil"] = json!("3");
        verify_pinned(&short, &short).unwrap();
        let mut extended = short.clone();
        extended["slots"][0]["signing"]["validUntil"] = json!("7");
        assert!(verify_pinned(&short, &extended).is_err());
    }
    #[test]
    fn wire_preserves_legacy_and_v2_exact_pair_boundaries() {
        assert_eq!(
            request_payload(b"call", b"out", None, false).unwrap(),
            pair(b"call", b"out").unwrap()
        );
        let v = request_payload(b"call", b"out", Some((b"fence", b"proof")), true).unwrap();
        let mut expected = V2.to_vec();
        expected.extend(
            pair(
                &pair(b"call", b"out").unwrap(),
                &pair(b"fence", b"proof").unwrap(),
            )
            .unwrap(),
        );
        assert_eq!(v, expected);
        assert!(request_payload(b"call", b"out", Some((b"f", b"p")), false).is_err());
    }
    #[test]
    fn input_is_exact_bounded_regular_and_private_retention() {
        let dir = env::temp_dir().join(format!(
            "mini-continuity-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&dir).unwrap();
        let input = dir.join("input.bin");
        fs::write(&input, b"reserve").unwrap();
        let value = json!({"path":input,"sha256":hex(&sha2::Sha256::digest(b"reserve"))});
        let kept = dir.join("retained.bin");
        retained_input(&value, 64, &kept).unwrap();
        assert_eq!(fs::metadata(&kept).unwrap().mode() & 0o777, 0o600);
        fs::write(&input, b"changed").unwrap();
        assert!(retained_input(&value, 64, &dir.join("changed.bin")).is_err());
        assert!(bounded_regular(&input, 2).is_err());
        let link = dir.join("link");
        std::os::unix::fs::symlink(&input, &link).unwrap();
        assert!(bounded_regular(&link, 64).is_err());
        let mut malformed = value.clone();
        malformed["extra"] = json!(true);
        assert!(retained_input(&malformed, 64, &dir.join("extra.bin")).is_err());
        let mut bad = anchor("1");
        bad["acceptedCount"] = json!("03");
        assert!(receipt(&bad).is_err());
        fs::remove_dir_all(&dir).unwrap();
    }
    #[test]
    fn descriptor_rejects_duplicate_and_escaped_alias_keys() {
        assert!(strict_descriptor(br#"{"reserve":{},"reserve":{}}"#).is_err());
        assert!(strict_descriptor(br#"{"reserve":{"path":"a","pa\u0074h":"b"}}"#).is_err());
        strict_descriptor(
            br#"{"reserve":{"path":"a"},"fence":{"path":"b"},"array":["x",{"key":"y"}]}"#,
        )
        .unwrap();
        assert!(strict_descriptor(b"{broken").is_err());
    }

    #[test]
    fn guarded_attempt_lookup_uses_original_call_without_rechecking_or_resigning() {
        use std::os::unix::fs::PermissionsExt;
        let directory = env::temp_dir().join(format!(
            "mini-continuity-lookup-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let host = directory.join("host.sh");
        // Any prepare, submit, or pin-plan-height invocation fails this test.
        fs::write(&host, b"#!/bin/sh\ncase \"$2\" in lookup) cp \"$3\" \"$4\" ;; inspect) printf '{\"type\":\"confirmed\"}' >\"$5\" ;; *) exit 91 ;; esac\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let config = directory.join("config.json");
        fs::write(&config, b"{}").unwrap();
        let original = b"exact signed call with original expired deadline";
        fs::write(directory.join("call.bin"), original).unwrap();
        fs::create_dir(directory.join("provider-continuity")).unwrap();
        fs::write(
            directory.join("provider-continuity/descriptor.json"),
            b"deliberately invalid; lookup must not re-enter signing",
        )
        .unwrap();
        fs::write(directory.join("original-plan.bin"), b"original plan").unwrap();
        write_json_new(&directory.join("attempt.json"), &json!({"format":"minidregg-resource-client-attempt-v1","operation":"submit","host":host,"config":config})).unwrap();
        retry(&directory, "lookup", false).unwrap();
        assert_eq!(
            fs::read(directory.join("retry-0001.bin")).unwrap(),
            original
        );
        assert_eq!(fs::read(directory.join("call.bin")).unwrap(), original);
        assert!(!directory.join("transaction-signatures.bin").exists());
        fs::remove_dir_all(directory).unwrap();
    }
    fn rejected_fixture() -> PathBuf {
        let directory = env::temp_dir().join(format!(
            "mini-continuity-rejected-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        fs::create_dir(directory.join("provider-continuity")).unwrap();
        for (name, bytes) in [
            ("intent.json", b"exact intent".as_slice()),
            ("config.json", b"exact config".as_slice()),
            (
                "provider-continuity/descriptor.json",
                b"exact descriptor".as_slice(),
            ),
            ("original-plan.bin", b"exact native plan".as_slice()),
            ("original-plan.json", b"exact inspected plan".as_slice()),
        ] {
            fs::write(directory.join(name), bytes).unwrap();
        }
        write_json_new(&directory.join("attempt.json"), &json!({"format":"minidregg-resource-client-attempt-v1","operation":"submit","config":directory.join("config.json")})).unwrap();
        directory
    }
    #[test]
    fn rejection_marker_binds_each_exact_retained_input_and_never_releases_hold() {
        let directory = rejected_fixture();
        retain_rejection(&directory, &directory.join("intent.json")).unwrap();
        let marker_path = directory.join("provider-continuity-rejection.json");
        let marker: Value = serde_json::from_slice(&fs::read(&marker_path).unwrap()).unwrap();
        assert_eq!(marker["type"], "minidregg-provider-continuity-rejection-v1");
        assert_eq!(marker["stage"], "before-signing");
        assert_eq!(marker["heldAllowanceReleased"], false);
        assert_eq!(marker["reason"], "continuity-gate-rejected");
        assert_eq!(fs::metadata(&marker_path).unwrap().mode() & 0o777, 0o600);
        for field in [
            "intent",
            "config",
            "manifest",
            "descriptor",
            "originalPlan",
            "originalPlanPresentation",
        ] {
            let name = marker[field]["path"].as_str().unwrap();
            assert_eq!(
                marker[field],
                rejection_binding(&directory, name, 65536).unwrap()
            );
            let original = fs::read(directory.join(name)).unwrap();
            fs::write(directory.join(name), b"changed after rejection").unwrap();
            assert_ne!(
                marker[field],
                rejection_binding(&directory, name, 65536).unwrap(),
                "{field}"
            );
            fs::write(directory.join(name), original).unwrap();
        }
        fs::remove_dir_all(directory).unwrap();
    }
    #[test]
    fn rejection_marker_requires_positive_absence_and_complete_retained_inputs() {
        for name in [
            "call.bin",
            "transaction-signatures.bin",
            "transaction-signatures.json",
            "outcome.bin",
            "outcome.json",
        ] {
            for dangling in [false, true] {
                let directory = rejected_fixture();
                if dangling {
                    std::os::unix::fs::symlink(directory.join("missing"), directory.join(name))
                        .unwrap();
                } else {
                    fs::write(directory.join(name), b"possible signed operation").unwrap();
                }
                assert!(
                    retain_rejection(&directory, &directory.join("intent.json")).is_err(),
                    "{name}"
                );
                assert!(!directory
                    .join("provider-continuity-rejection.json")
                    .exists());
                fs::remove_dir_all(directory).unwrap();
            }
        }
        let directory = rejected_fixture();
        fs::remove_file(directory.join("provider-continuity/descriptor.json")).unwrap();
        assert!(retain_rejection(&directory, &directory.join("intent.json")).is_err());
        assert!(!directory
            .join("provider-continuity-rejection.json")
            .exists());
        fs::remove_dir_all(directory).unwrap();
    }
}
