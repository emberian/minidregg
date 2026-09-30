//! Durable operator custody for one fn consumer namespace registration.
//! The Host owns the plan, credential envelope, ingress, and admission. This
//! client only retains exact bytes, signs the source-selected header, and
//! recovers an uncertain submit through receipt-only op41.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, PermissionsExt};

const FORMAT: &str = "minidregg-fn-namespace-custody-v1";
const APPROVAL: &str = "minidregg-fn-namespace-approval-v1";

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn bounded(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| format!("cannot open {}: {e}", path.display()))?
        .take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err(format!("{} must contain 1..={limit} bytes", path.display()));
    }
    Ok(bytes)
}

fn member<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("fn namespace custody lacks {name}"))
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 80
        && value.bytes().all(|b| b.is_ascii_digit())
        && (value.len() == 1 || !value.starts_with('0'))
}

fn private_file(path: &Path, limit: usize) -> Result<Vec<u8>> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = path.parent().ok_or("private file has no parent")?;
    let directory = fs::symlink_metadata(parent).map_err(|e| e.to_string())?;
    let named = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    let file = File::open(path).map_err(|e| e.to_string())?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !directory.is_dir()
        || directory.uid() != uid
        || directory.permissions().mode() & 0o077 != 0
        || !named.file_type().is_file()
        || named.uid() != uid
        || named.permissions().mode() & 0o077 != 0
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err("fn namespace custody requires owner-private file and parent".into());
    }
    let mut bytes = Vec::new();
    file.take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err("fn namespace private file exceeds bound".into());
    }
    Ok(bytes)
}

fn custody_key(path: &Path) -> Result<SigningKey> {
    let bytes = private_file(path, 32)?;
    let mut seed: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "fn namespace key must contain exactly 32 bytes".to_owned())?;
    let signing = SigningKey::from_bytes(&seed);
    seed.fill(0);
    Ok(signing)
}

fn operator_socket_owned(socket: &Path) -> Result<()> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = socket.parent().ok_or("operator socket has no parent")?;
    let directory = fs::symlink_metadata(parent).map_err(|e| e.to_string())?;
    let node = fs::symlink_metadata(socket).map_err(|e| e.to_string())?;
    if !directory.is_dir()
        || directory.uid() != uid
        || directory.permissions().mode() & 0o077 != 0
        || !node.file_type().is_socket()
        || node.uid() != uid
        || node.permissions().mode() & 0o077 != 0
    {
        return Err("fn namespace requires an owner-private operator socket".into());
    }
    Ok(())
}

fn retain_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("fn namespace state has no parent")?)
}

fn source_inspect(
    host: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
) -> Result<Value> {
    let result = Command::new(host)
        .arg(config)
        .args(["inspect", kind])
        .arg(input)
        .arg(output)
        .output()
        .map_err(|e| format!("cannot run pinned Host inspection: {e}"))?;
    if !result.status.success() {
        return Err(format!("pinned Host {kind} inspection refused"));
    }
    serde_json::from_slice(&bounded(output, 65_536)?)
        .map_err(|e| format!("invalid source inspection: {e}"))
}

fn expect_frame(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        [255, ..] => Err(format!(
            "fn namespace Host refused op{operation}; frame retained"
        )),
        _ => Err(format!("fn namespace op{operation} returned invalid frame")),
    }
}

struct Retained {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    host_sha: String,
    plan: Vec<u8>,
    inspection: Value,
}

fn retained(directory: &Path) -> Result<Retained> {
    drain::private_dir(directory)?;
    let pin: Value = serde_json::from_slice(&bounded(&directory.join("pin.json"), 65_536)?)
        .map_err(|e| e.to_string())?;
    if member(&pin, "format")? != FORMAT {
        return Err("unsupported fn namespace custody pin".into());
    }
    let host = PathBuf::from(member(&pin, "host")?);
    let config = PathBuf::from(member(&pin, "config")?);
    let socket = PathBuf::from(member(&pin, "operatorSocket")?);
    let host_sha = member(&pin, "hostSha256")?.to_owned();
    if !host.is_absolute()
        || !config.is_absolute()
        || !socket.is_absolute()
        || config != absolute(&directory.join("config.json"))?
        || host_image_sha256(&host)? != host_sha
        || digest(&bounded(&config, 65_536)?) != member(&pin, "configSha256")?
    {
        return Err("fn namespace retained Host or config changed".into());
    }
    let plan = bounded(&directory.join("plan.bin"), 8192)?;
    if digest(&plan) != member(&pin, "planSha256")? {
        return Err("fn namespace retained plan changed".into());
    }
    let inspection: Value = serde_json::from_slice(&bounded(&directory.join("plan.json"), 65_536)?)
        .map_err(|e| e.to_string())?;
    if member(&inspection, "type")? != "fn-consumer-namespace-plan-v1"
        || member(&inspection, "canonicalPlanHex")? != hex(&plan)
    {
        return Err("fn namespace plan inspection differs from exact plan".into());
    }
    Ok(Retained {
        host,
        config,
        socket,
        host_sha,
        plan,
        inspection,
    })
}

fn verify_inspection(directory: &Path, state: &Retained) -> Result<()> {
    let target = (0..10_000)
        .map(|index| directory.join(format!("plan.reinspect-{index:04}.json")))
        .find(|candidate| !candidate.exists())
        .ok_or("fn namespace plan reinspection names exhausted")?;
    let checked = source_inspect(
        &state.host,
        &state.config,
        "fn-consumer-namespace-plan",
        &directory.join("plan.bin"),
        &target,
    )?;
    if checked != state.inspection {
        return Err("retained fn namespace plan presentation differs from pinned Host".into());
    }
    Ok(())
}

/// Read-only, source-authored plan from one fenced local fn zero position.
pub(super) fn plan(host: &Path, config: &Path, socket: &Path, directory: &Path) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let socket = absolute(socket)?;
    let directory = absolute(directory)?;
    operator_socket_owned(&socket)?;
    let config_bytes = bounded(&config, 65_536)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|e| format!("cannot create new fn namespace state: {e}"))?;
    sync_directory_ancestors(&directory)?;
    let config_copy = directory.join("config.json");
    create_private(&config_copy, &config_bytes)?;
    let host_sha = host_image_sha256(&host)?;
    retain_json(
        &directory.join("plan-attempt.json"),
        &json!({
            "operation":42,"host":utf8_path(&host)?,"hostSha256":host_sha,
            "configSha256":digest(&config_bytes),"operatorSocket":utf8_path(&socket)?
        }),
    )?;
    let frame = transport::invoke_pinned(&socket, &config_copy, &host_sha, 42, &[])
        .map_err(|e| format!("fn namespace plan response uncertain; no Mini write: {e}"))?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let bytes = expect_frame(&frame, 42)?;
    if bytes.len() > 8192 {
        return Err("fn namespace plan exceeds source bound".into());
    }
    create_private(&directory.join("plan.bin"), bytes)?;
    let inspection = source_inspect(
        &host,
        &config_copy,
        "fn-consumer-namespace-plan",
        &directory.join("plan.bin"),
        &directory.join("plan.json"),
    )?;
    if member(&inspection, "type")? != "fn-consumer-namespace-plan-v1"
        || member(&inspection, "canonicalPlanHex")? != hex(bytes)
    {
        return Err("fn namespace Host plan inspection differs from exact bytes".into());
    }
    retain_json(
        &directory.join("pin.json"),
        &json!({
            "format":FORMAT,"host":utf8_path(&host)?,"hostSha256":host_sha,
            "config":utf8_path(&config_copy)?,"configSha256":digest(&config_bytes),
            "operatorSocket":utf8_path(&socket)?,"planSha256":digest(bytes)
        }),
    )?;
    print_json(&inspection)
}

fn check_approval(
    approval: &Value,
    inspection: &Value,
    plan: &[u8],
    signing: &SigningKey,
) -> Result<Vec<u8>> {
    if member(approval, "type")? != APPROVAL
        || member(approval, "planSha256")? != digest(plan)
        || member(approval, "planIdentity")? != member(inspection, "planIdentity")?
        || member(approval, "signerPublicKey")? != hex(&signing.verifying_key().to_bytes())
    {
        return Err("fn namespace plan or gateway key differs from private approval".into());
    }
    for name in [
        "domain",
        "semantics",
        "applicationHex",
        "historyHex",
        "incarnationHex",
        "consumerHex",
        "principalHex",
        "queryHex",
        "queryVersion",
        "viewVersion",
        "registrationEpoch",
        "controlBindingHex",
        "gatewaySubject",
        "gatewayTarget",
        "gatewayCapability",
        "expectedAuthorityRoot",
        "expectedTargetRoot",
        "signingKeyId",
        "signingKeyEpoch",
        "signingAlgorithm",
        "signingValidUntil",
    ] {
        if member(approval, name)? != member(inspection, name)? {
            return Err(format!("fn namespace {name} differs from private approval"));
        }
    }
    if member(inspection, "signingAlgorithm")? != "1" {
        return Err("fn namespace credential algorithm is not Ed25519".into());
    }
    // The plan pins the durable outer authority root and the credential
    // header's logical authority root separately. They need not be equal.
    let header_hex = member(inspection, "signingHeaderHex")?;
    let header = decode_hex(header_hex)?;
    if header.is_empty() || header.len() > 4096 || hex(&header) != header_hex {
        return Err("fn namespace signing header is not canonical hex".into());
    }
    Ok(header)
}

fn pair(plan: &[u8], signature: &[u8]) -> Result<Vec<u8>> {
    if plan.is_empty() || plan.len() > 8192 || signature.len() != 64 {
        return Err("fn namespace op43 pair exceeds strict bound".into());
    }
    let mut bytes = Vec::with_capacity(4 + plan.len() + signature.len());
    bytes.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    bytes.extend_from_slice(plan);
    bytes.extend_from_slice(signature);
    Ok(bytes)
}

fn reinspection(directory: &Path, state: &Retained, binary: &Path, stem: &str) -> Result<Value> {
    let target = (0..10_000)
        .map(|index| directory.join(format!("{stem}.reinspect-{index:04}.json")))
        .find(|candidate| !candidate.exists())
        .ok_or("fn namespace outcome reinspection names exhausted")?;
    source_inspect(&state.host, &state.config, "outcome", binary, &target)
}

fn receipt(value: &Value) -> Result<Value> {
    if member(value, "type")? != "confirmed" {
        return Err("fn namespace original Mini receipt is not confirmed".into());
    }
    let mut fields = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
        let number = member(value, name)?;
        if !canonical_decimal(number) {
            return Err(format!("fn namespace receipt {name} is not canonical"));
        }
        fields.insert(name.to_owned(), Value::String(number.to_owned()));
    }
    Ok(Value::Object(fields))
}

fn validate_submit_marker(directory: &Path, state: &Retained, ingress: &[u8]) -> Result<()> {
    let marker: Value =
        serde_json::from_slice(&bounded(&directory.join("submit-attempt.json"), 4096)?)
            .map_err(|e| e.to_string())?;
    if marker.get("operation").and_then(Value::as_u64) != Some(40)
        || member(&marker, "ingressSha256")? != digest(ingress)
        || member(&marker, "operatorSocket")? != utf8_path(&state.socket)?
    {
        return Err("fn namespace retained submit marker changed".into());
    }
    Ok(())
}

fn validate_assembly(
    directory: &Path,
    state: &Retained,
    ingress: &[u8],
    signature: &[u8],
) -> Result<()> {
    let assembly: Value =
        serde_json::from_slice(&bounded(&directory.join("assembly-attempt.json"), 4096)?)
            .map_err(|e| e.to_string())?;
    let frame = bounded(&directory.join("assembly.frame"), 8193)?;
    if assembly.get("operation").and_then(Value::as_u64) != Some(43)
        || member(&assembly, "planSha256")? != digest(&state.plan)
        || member(&assembly, "signatureSha256")? != digest(signature)
        || frame.first() != Some(&43)
        || frame[1..] != *ingress
    {
        return Err("fn namespace ingress differs from exact Host assembly".into());
    }
    Ok(())
}

fn validate_ingress_pin(directory: &Path, state: &Retained) -> Result<Vec<u8>> {
    let ingress = bounded(&directory.join("ingress.bin"), 8192)?;
    let signature = bounded(&directory.join("signature.bin"), 64)?;
    validate_assembly(directory, state, &ingress, &signature)?;
    let pin: Value = serde_json::from_slice(&bounded(&directory.join("ingress-pin.json"), 4096)?)
        .map_err(|e| e.to_string())?;
    if member(&pin, "ingressSha256")? != digest(&ingress)
        || member(&pin, "planSha256")? != digest(&state.plan)
        || member(&pin, "signatureSha256")? != digest(&signature)
    {
        return Err("fn namespace retained ingress custody changed".into());
    }
    validate_submit_marker(directory, state, &ingress)?;
    Ok(ingress)
}

fn lookup(directory: &Path, state: &Retained, ingress: &[u8]) -> Result<Option<Value>> {
    for index in 0..16 {
        let stem = format!("lookup-{index:02}");
        if directory.join(format!("{stem}.attempt.json")).exists() {
            continue;
        }
        retain_json(
            &directory.join(format!("{stem}.attempt.json")),
            &json!({
                "operation":41,"ingressSha256":digest(ingress),
                "operatorSocket":utf8_path(&state.socket)?
            }),
        )?;
        let frame =
            transport::invoke_pinned(&state.socket, &state.config, &state.host_sha, 41, ingress)
                .map_err(|e| format!("fn namespace exact lookup uncertain: {e}"))?;
        create_private(&directory.join(format!("{stem}.frame")), &frame)?;
        sync_directory_ancestors(directory)?;
        let binary = expect_frame(&frame, 41)?;
        create_private(&directory.join(format!("{stem}.outcome.bin")), binary)?;
        let value = reinspection(
            directory,
            state,
            &directory.join(format!("{stem}.outcome.bin")),
            &stem,
        )?;
        return match member(&value, "type")? {
            "confirmed" => Ok(Some(receipt(&value)?)),
            "absent" => Ok(None),
            _ => Err("fn namespace lookup did not establish exact original".into()),
        };
    }
    Err("fn namespace lookup attempts exhausted".into())
}

/// One signed event20 ingress. An existing submit marker forces read-only
/// lookup; an uncertain transport result never authorizes another submit.
pub(super) fn register(directory: &Path, key: &Path, approval_path: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _owner = transport::service_lock(&directory.join("fn-namespace.lock"))?;
    let state = retained(&directory)?;
    operator_socket_owned(&state.socket)?;
    verify_inspection(&directory, &state)?;
    let approval_bytes = private_file(approval_path, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes).map_err(|e| e.to_string())?;
    let signing = custody_key(key)?;
    let header = check_approval(&approval, &state.inspection, &state.plan, &signing)?;
    let approval_hash = digest(&approval_bytes);
    let approval_pin = directory.join("approval-pin.json");
    if approval_pin.exists() {
        let pin: Value =
            serde_json::from_slice(&bounded(&approval_pin, 4096)?).map_err(|e| e.to_string())?;
        if member(&pin, "approvalSha256")? != approval_hash
            || member(&pin, "signerPublicKey")? != hex(&signing.verifying_key().to_bytes())
        {
            return Err("fn namespace retained approval or signer changed".into());
        }
    } else {
        retain_json(
            &approval_pin,
            &json!({"approvalSha256":approval_hash,
            "signerPublicKey":hex(&signing.verifying_key().to_bytes())}),
        )?;
    }
    let signature_path = directory.join("signature.bin");
    let signature = if signature_path.exists() {
        bounded(&signature_path, 64)?
    } else {
        let raw = signing.sign(&header).to_bytes();
        create_private(&signature_path, &raw)?;
        sync_directory_ancestors(&directory)?;
        raw.to_vec()
    };
    if signature.len() != 64 || signature != signing.sign(&header).to_bytes() {
        return Err("fn namespace retained signature differs from exact plan/key".into());
    }
    let ingress_path = directory.join("ingress.bin");
    let ingress = if ingress_path.exists() {
        bounded(&ingress_path, 8192)?
    } else {
        let marker = directory.join("assembly-attempt.json");
        let frame_path = directory.join("assembly.frame");
        let frame = if frame_path.exists() {
            bounded(&frame_path, 8193)?
        } else {
            if marker.exists() {
                let old: Value =
                    serde_json::from_slice(&bounded(&marker, 4096)?).map_err(|e| e.to_string())?;
                if old.get("operation").and_then(Value::as_u64) != Some(43)
                    || member(&old, "planSha256")? != digest(&state.plan)
                    || member(&old, "signatureSha256")? != digest(&signature)
                {
                    return Err("fn namespace assembly marker changed".into());
                }
            } else {
                retain_json(
                    &marker,
                    &json!({"operation":43,
                    "planSha256":digest(&state.plan),"signatureSha256":digest(&signature)}),
                )?;
            }
            let pair = pair(&state.plan, &signature)?;
            let frame =
                transport::invoke_pinned(&state.socket, &state.config, &state.host_sha, 43, &pair)
                    .map_err(|e| format!("fn namespace assembly response uncertain: {e}"))?;
            create_private(&frame_path, &frame)?;
            sync_directory_ancestors(&directory)?;
            frame
        };
        let bytes = expect_frame(&frame, 43)?;
        if bytes.len() > 8192 {
            return Err("fn namespace ingress exceeds strict bound".into());
        }
        create_private(&ingress_path, bytes)?;
        bytes.to_vec()
    };
    let ingress_pin = directory.join("ingress-pin.json");
    if ingress_pin.exists() {
        let pin: Value =
            serde_json::from_slice(&bounded(&ingress_pin, 4096)?).map_err(|e| e.to_string())?;
        if member(&pin, "ingressSha256")? != digest(&ingress) {
            return Err("fn namespace retained ingress changed".into());
        }
    } else {
        retain_json(
            &ingress_pin,
            &json!({"ingressSha256":digest(&ingress),
            "planSha256":digest(&state.plan),"signatureSha256":digest(&signature)}),
        )?;
    }
    validate_assembly(&directory, &state, &ingress, &signature)?;
    let submit_marker = directory.join("submit-attempt.json");
    if submit_marker.exists() {
        validate_submit_marker(&directory, &state, &ingress)?;
    } else {
        retain_json(
            &submit_marker,
            &json!({"operation":40,
            "ingressSha256":digest(&ingress),"operatorSocket":utf8_path(&state.socket)?}),
        )?;
        match transport::invoke_pinned(&state.socket, &state.config, &state.host_sha, 40, &ingress)
        {
            Ok(frame) => {
                create_private(&directory.join("submit.frame"), &frame)?;
                sync_directory_ancestors(&directory)?;
                if let Ok(bytes) = expect_frame(&frame, 40) {
                    create_private(&directory.join("submit.outcome.bin"), bytes)?;
                }
            }
            Err(error) => {
                retain_json(
                    &directory.join("submit-transport-uncertain.json"),
                    &json!({"type":"transport-uncertain","detail":error}),
                )?;
            }
        }
    }
    if directory.join("submit.outcome.bin").exists() {
        let frame = bounded(&directory.join("submit.frame"), transport::HOST_MAX_FRAME)?;
        let body = bounded(
            &directory.join("submit.outcome.bin"),
            transport::HOST_MAX_FRAME - 1,
        )?;
        if frame.first() != Some(&40) || frame[1..] != body {
            return Err("fn namespace submit outcome differs from exact Host frame".into());
        }
        if let Ok(value) = reinspection(
            &directory,
            &state,
            &directory.join("submit.outcome.bin"),
            "submit",
        ) {
            if let Ok(original) = receipt(&value) {
                let confirmed = directory.join("confirmed.json");
                if confirmed.exists() {
                    let prior: Value = serde_json::from_slice(&bounded(&confirmed, 4096)?)
                        .map_err(|e| e.to_string())?;
                    if prior != original {
                        return Err("fn namespace original receipt changed".into());
                    }
                } else {
                    retain_json(&confirmed, &original)?;
                }
                return print_json(&original);
            }
        }
    }
    match lookup(&directory, &state, &ingress)? {
        Some(original) => {
            if directory.join("confirmed.json").exists() {
                let prior: Value =
                    serde_json::from_slice(&bounded(&directory.join("confirmed.json"), 4096)?)
                        .map_err(|e| e.to_string())?;
                if prior != original {
                    return Err("fn namespace original receipt changed".into());
                }
            } else {
                retain_json(&directory.join("confirmed.json"), &original)?;
            }
            print_json(&original)
        }
        None => Err("fn namespace exact lookup absent; no automatic resubmit".into()),
    }
}

/// Read-only recovery from the exact retained op40 attempt. Gateway key
/// custody is unnecessary once the ingress and durable attempt are retained.
pub(super) fn lookup_original(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _owner = transport::service_lock(&directory.join("fn-namespace.lock"))?;
    let state = retained(&directory)?;
    operator_socket_owned(&state.socket)?;
    verify_inspection(&directory, &state)?;
    let ingress = validate_ingress_pin(&directory, &state)?;
    match lookup(&directory, &state, &ingress)? {
        Some(original) => {
            let confirmed = directory.join("confirmed.json");
            if confirmed.exists() {
                let prior: Value = serde_json::from_slice(&bounded(&confirmed, 4096)?)
                    .map_err(|e| e.to_string())?;
                if prior != original {
                    return Err("fn namespace original receipt changed".into());
                }
            } else {
                retain_json(&confirmed, &original)?;
            }
            print_json(&original)
        }
        None => Err("fn namespace exact lookup absent; no automatic resubmit".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::net::UnixListener;
    use std::thread;

    #[test]
    fn op43_pair_has_exact_raw_signature() {
        let plan = [1, 2, 3];
        let signature = [7; 64];
        let bytes = pair(&plan, &signature).unwrap();
        assert_eq!(&bytes[..4], &3u32.to_le_bytes());
        assert_eq!(&bytes[4..7], &plan);
        assert_eq!(&bytes[7..], &signature);
        assert!(pair(&plan, &[7; 63]).is_err());
    }

    #[test]
    fn gateway_custody_requires_exact_plan_and_signer() {
        let signing = SigningKey::from_bytes(&[9; 32]);
        let plan = [1, 2, 3];
        let inspection = json!({"type":"fn-consumer-namespace-plan-v1",
            "planIdentity":"123","domain":"10","semantics":"11",
            "applicationHex":"61","historyHex":"12","incarnationHex":"13",
            "consumerHex":"62","principalHex":"63","queryHex":"64",
            "queryVersion":"1","viewVersion":"0","registrationEpoch":"1",
            "controlBindingHex":"14","gatewaySubject":"8","gatewayTarget":"601",
            "gatewayCapability":"63","expectedAuthorityRoot":"15",
            "expectedTargetRoot":"16","signingKeyId":"77","signingKeyEpoch":"1",
            "signingAlgorithm":"1","signingValidUntil":"17",
            "signingHeaderHex":"010203"});
        let mut approval = inspection.clone();
        approval["type"] = json!(APPROVAL);
        approval["planSha256"] = json!(digest(&plan));
        approval["signerPublicKey"] = json!(hex(&signing.verifying_key().to_bytes()));
        assert_eq!(
            check_approval(&approval, &inspection, &plan, &signing).unwrap(),
            [1, 2, 3]
        );
        let mut changed = approval.clone();
        changed["gatewayTarget"] = json!("602");
        assert!(check_approval(&changed, &inspection, &plan, &signing).is_err());
        changed = approval.clone();
        changed["planSha256"] = json!(digest(&[1, 2, 4]));
        assert!(check_approval(&changed, &inspection, &plan, &signing).is_err());
        changed = approval.clone();
        changed["signingValidUntil"] = json!("15");
        assert!(check_approval(&changed, &inspection, &plan, &signing).is_err());
    }

    #[test]
    fn receipt_requires_four_canonical_fields() {
        let accepted = json!({"type":"confirmed","transactionId":"1","eventId":"2",
            "acceptedCount":"3","imageBoundary":"4"});
        assert_eq!(receipt(&accepted).unwrap()["eventId"], "2");
        let mut malformed = accepted.clone();
        malformed["eventId"] = json!("02");
        assert!(receipt(&malformed).is_err());
        malformed = accepted;
        malformed["type"] = json!("uncertain");
        assert!(receipt(&malformed).is_err());
    }

    #[test]
    fn lost_submit_reply_recovers_by_lookup_without_resubmit() {
        let root = std::env::temp_dir().join(format!(
            "mfn-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
                % 1_000_000_000
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let state = root.join("state");
        fs::DirBuilder::new().mode(0o700).create(&state).unwrap();
        let config = state.join("config.json");
        create_private(&config, b"{}").unwrap();
        let plan = [1u8, 2, 3];
        create_private(&state.join("plan.bin"), &plan).unwrap();
        let inspection = json!({"type":"fn-consumer-namespace-plan-v1",
            "canonicalPlanHex":hex(&plan),"planIdentity":"123",
            "domain":"10","semantics":"11","applicationHex":"61",
            "historyHex":"12","incarnationHex":"13","consumerHex":"62",
            "principalHex":"63","queryHex":"64","queryVersion":"1",
            "viewVersion":"0","registrationEpoch":"1","controlBindingHex":"14",
            "gatewaySubject":"8","gatewayTarget":"601","gatewayCapability":"63",
            "expectedAuthorityRoot":"15","expectedTargetRoot":"16",
            "signingKeyId":"77","signingKeyEpoch":"1","signingAlgorithm":"1",
            "signingValidUntil":"17","signingHeaderHex":"010203"});
        retain_json(&state.join("plan.json"), &inspection).unwrap();
        let host = root.join("host.sh");
        let script = format!("#!/bin/sh\nif [ \"$2\" != inspect ]; then exit 1; fi\nif [ \"$3\" = fn-consumer-namespace-plan ]; then cp '{}' \"$5\"; else printf '%s\\n' '{{\"type\":\"confirmed\",\"transactionId\":\"1\",\"eventId\":\"2\",\"acceptedCount\":\"3\",\"imageBoundary\":\"4\"}}' > \"$5\"; fi\n", state.join("plan.json").display());
        fs::write(&host, script).unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let socket = root.join("operator.sock");
        let listener = UnixListener::bind(&socket).unwrap();
        fs::set_permissions(&socket, fs::Permissions::from_mode(0o600)).unwrap();
        let host_sha = host_image_sha256(&host).unwrap();
        retain_json(
            &state.join("pin.json"),
            &json!({"format":FORMAT,
            "host":utf8_path(&host).unwrap(),"hostSha256":host_sha,
            "config":utf8_path(&config).unwrap(),"configSha256":digest(b"{}"),
            "operatorSocket":utf8_path(&socket).unwrap(),"planSha256":digest(&plan)}),
        )
        .unwrap();
        let signing = SigningKey::from_bytes(&[9; 32]);
        let key = root.join("gateway.key");
        create_private(&key, &[9; 32]).unwrap();
        let mut approval = inspection.clone();
        approval["type"] = json!(APPROVAL);
        approval["planSha256"] = json!(digest(&plan));
        approval["signerPublicKey"] = json!(hex(&signing.verifying_key().to_bytes()));
        let approval_path = root.join("approval.json");
        retain_json(&approval_path, &approval).unwrap();
        let server = thread::spawn(move || {
            let mut operations = Vec::new();
            for _ in 0..4 {
                let (mut stream, _) = listener.accept().unwrap();
                let mut width = [0u8; 4];
                stream.read_exact(&mut width).unwrap();
                let mut request = vec![0; u32::from_le_bytes(width) as usize];
                stream.read_exact(&mut request).unwrap();
                let config_length = u32::from_le_bytes(request[1..5].try_into().unwrap()) as usize;
                let operation = request[5 + config_length + 32];
                operations.push(operation);
                if operation == 40 {
                    // The simulated Store installs this exact ingress, then
                    // the reply is lost. The following op41 is its readback.
                    continue;
                }
                let reply = if operation == 43 {
                    let mut bytes = vec![43];
                    bytes.extend_from_slice(b"exact-ingress");
                    bytes
                } else {
                    assert_eq!(operation, 41);
                    let mut bytes = vec![41];
                    bytes.extend_from_slice(b"confirmed-outcome");
                    bytes
                };
                stream
                    .write_all(&(reply.len() as u32).to_le_bytes())
                    .unwrap();
                stream.write_all(&reply).unwrap();
            }
            operations
        });
        register(&state, &key, &approval_path).unwrap();
        register(&state, &key, &approval_path).unwrap();
        assert_eq!(server.join().unwrap(), [43, 40, 41, 41]);
        assert!(state.join("submit-transport-uncertain.json").exists());
        assert!(state.join("confirmed.json").exists());
        fs::remove_dir_all(root).unwrap();
    }
}
