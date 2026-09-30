//! Operator custody for one event17 selected observation or event19 empty page.
//! The source-owned Host polls the pinned fn service, authors the complete plan,
//! assembles the credential envelope, and admits the special Mini event. This
//! client signs only its exact header and never invents a cursor or ingress.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, PermissionsExt};

const FORMAT: &str = "minidregg-fn-frontier-custody-v1";
const APPROVAL: &str = "minidregg-fn-frontier-approval-v1";
const MAX_PLAN: usize = 12_102_760;
const MAX_INSPECTION: usize = 2 * MAX_PLAN + 65_536;

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

fn bounded_allow_empty(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| format!("cannot open {}: {e}", path.display()))?
        .take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    if bytes.len() > limit {
        return Err(format!("{} exceeds {limit} bytes", path.display()));
    }
    Ok(bytes)
}

fn member<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("fn frontier custody lacks {name}"))
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
        return Err("fn frontier custody requires owner-private file and parent".into());
    }
    let mut bytes = Vec::new();
    file.take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err("fn frontier private file exceeds bound".into());
    }
    Ok(bytes)
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
        return Err("fn frontier requires an owner-private operator socket".into());
    }
    Ok(())
}

fn retain_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("fn frontier state has no parent")?)
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
    agent_reserve::retain_generated(output)?;
    serde_json::from_slice(&bounded(output, MAX_INSPECTION)?)
        .map_err(|e| format!("invalid source inspection: {e}"))
}

fn expect_frame(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        [255, ..] => Err(format!(
            "fn frontier Host refused op{operation}; frame retained"
        )),
        _ => Err(format!("fn frontier op{operation} returned invalid frame")),
    }
}

fn operations(inspection: &Value) -> Result<(u8, u8)> {
    match member(inspection, "kind")? {
        "selected" => Ok((60, 61)),
        "empty" => Ok((62, 63)),
        _ => Err("fn frontier plan kind is not selected or empty".into()),
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
        return Err("unsupported fn frontier custody pin".into());
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
        return Err("fn frontier retained Host or config changed".into());
    }
    let plan = bounded(&directory.join("plan.bin"), MAX_PLAN)?;
    if digest(&plan) != member(&pin, "planSha256")? {
        return Err("fn frontier retained plan changed".into());
    }
    if digest(&bounded(&directory.join("request.bin"), 128)?) != member(&pin, "requestSha256")? {
        return Err("fn frontier retained request changed".into());
    }
    let inspection: Value =
        serde_json::from_slice(&bounded(&directory.join("plan.json"), MAX_INSPECTION)?)
            .map_err(|e| e.to_string())?;
    if member(&inspection, "type")? != "fn-consumer-frontier-plan-v2"
        || member(&inspection, "canonicalPlanHex")? != hex(&plan)
    {
        return Err("fn frontier plan inspection differs from exact plan".into());
    }
    for (name, limit) in [
        ("cursor.fncu", 346usize),
        ("report.fn-e", 3_150_546),
        ("source.eml", 1_500_000),
    ] {
        let path = directory.join(name);
        let bytes = bounded_allow_empty(&path, limit)?;
        if (name == "cursor.fncu" && bytes.is_empty())
            || (member(&inspection, "kind")? == "empty"
                && name != "cursor.fncu"
                && !bytes.is_empty())
            || (member(&inspection, "kind")? == "selected"
                && name != "cursor.fncu"
                && bytes.is_empty())
            || digest(&bytes) != member(&pin, &format!("{name}Sha256"))?
        {
            return Err(format!("retained fn frontier {name} changed"));
        }
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

fn pin_still(directory: &Path, earlier: &Retained) -> Result<()> {
    let current = retained(directory)?;
    if current.host != earlier.host
        || current.config != earlier.config
        || current.socket != earlier.socket
        || current.host_sha != earlier.host_sha
        || current.plan != earlier.plan
        || current.inspection != earlier.inspection
    {
        return Err("fn frontier custody pin changed during operation".into());
    }
    Ok(())
}

fn receipt(value: &Value) -> Result<Value> {
    if member(value, "type")? != "confirmed" {
        return Err("fn frontier original Mini receipt is not confirmed".into());
    }
    let mut fields = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
        let number = member(value, name)?;
        if number.is_empty()
            || number.len() > 80
            || (number.len() > 1 && number.starts_with('0'))
            || !number.bytes().all(|b| b.is_ascii_digit())
        {
            return Err(format!("fn frontier receipt {name} is not canonical"));
        }
        fields.insert(name.to_owned(), Value::String(number.to_owned()));
    }
    Ok(Value::Object(fields))
}

fn outcome_inspect(directory: &Path, state: &Retained, binary: &Path, stem: &str) -> Result<Value> {
    let target = (0..10_000)
        .map(|index| directory.join(format!("{stem}.reinspect-{index:04}.json")))
        .find(|candidate| !candidate.exists())
        .ok_or("fn frontier outcome reinspection names exhausted")?;
    let value = source_inspect(&state.host, &state.config, "outcome", binary, &target)?;
    pin_still(directory, state)?;
    Ok(value)
}

fn record_confirmed(directory: &Path, original: &Value) -> Result<()> {
    let target = directory.join("confirmed.json");
    if target.exists() {
        let prior: Value =
            serde_json::from_slice(&bounded(&target, 4096)?).map_err(|e| e.to_string())?;
        if prior != *original {
            return Err("fn frontier original receipt changed".into());
        }
    } else {
        retain_json(&target, original)?;
    }
    Ok(())
}

fn host_cli(host: &Path, config: &Path, args: &[&str], paths: &[&Path]) -> Result<()> {
    let mut child = Command::new(host);
    child.arg(config).args(args);
    for path in paths {
        child.arg(path);
    }
    let result = child
        .output()
        .map_err(|e| format!("cannot run pinned Host CLI: {e}"))?;
    if !result.status.success() {
        return Err(format!("pinned Host {} refused", args.join(" ")));
    }
    Ok(())
}

/// Read-only source-authored poll plan. The new directory retains every exact
/// response and native poll artifact; it does not sign or submit to Mini/fn.
pub(super) fn plan(
    host: &Path,
    config: &Path,
    socket: &Path,
    kind: &str,
    transaction: &str,
    directory: &Path,
) -> Result<()> {
    if !matches!((kind, transaction), ("empty", "-") | ("selected", _)) {
        return Err("fn frontier plan requires selected TX or empty -".into());
    }
    let host = absolute(host)?;
    let config = absolute(config)?;
    let socket = absolute(socket)?;
    let directory = absolute(directory)?;
    operator_socket_owned(&socket)?;
    let config_bytes = bounded(&config, 65_536)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|e| format!("cannot create new fn frontier state: {e}"))?;
    sync_directory_ancestors(&directory)?;
    let config_copy = directory.join("config.json");
    create_private(&config_copy, &config_bytes)?;
    let host_sha = host_image_sha256(&host)?;
    retain_json(
        &directory.join("plan-attempt.json"),
        &json!({"operation":64,"host":utf8_path(&host)?,"hostSha256":host_sha,
            "configSha256":digest(&config_bytes),"operatorSocket":utf8_path(&socket)?,
            "kind":kind,"transaction":transaction}),
    )?;
    let request = directory.join("request.bin");
    host_cli(
        &host,
        &config_copy,
        &["fn-frontier-request", kind, transaction],
        &[&request],
    )?;
    agent_reserve::retain_generated(&request)?;
    let request_bytes = bounded(&request, 128)?;
    let frame = transport::invoke_pinned(&socket, &config_copy, &host_sha, 64, &request_bytes)
        .map_err(|e| format!("fn frontier plan response uncertain; no Mini write: {e}"))?;
    create_private(&directory.join("plan.frame"), &frame)?;
    let plan_bytes = expect_frame(&frame, 64)?;
    if plan_bytes.len() > MAX_PLAN {
        return Err("fn frontier plan exceeds source bound".into());
    }
    let plan_path = directory.join("plan.bin");
    create_private(&plan_path, plan_bytes)?;
    let inspection = source_inspect(
        &host,
        &config_copy,
        "fn-consumer-frontier-plan",
        &plan_path,
        &directory.join("plan.json"),
    )?;
    if member(&inspection, "type")? != "fn-consumer-frontier-plan-v2"
        || member(&inspection, "canonicalPlanHex")? != hex(plan_bytes)
        || member(&inspection, "kind")? != kind
    {
        return Err("fn frontier Host inspection differs from exact plan".into());
    }
    host_cli(
        &host,
        &config_copy,
        &["fn-frontier-export"],
        &[
            &plan_path,
            &directory.join("cursor.fncu"),
            &directory.join("report.fn-e"),
            &directory.join("source.eml"),
        ],
    )?;
    for name in ["cursor.fncu", "report.fn-e", "source.eml"] {
        agent_reserve::retain_generated(&directory.join(name))?;
    }
    let cursor = bounded(&directory.join("cursor.fncu"), 346)?;
    let report = bounded_allow_empty(&directory.join("report.fn-e"), 3_150_546)?;
    let source = bounded_allow_empty(&directory.join("source.eml"), 1_500_000)?;
    if report.len() > 3_150_546
        || source.len() > 1_500_000
        || (kind == "selected" && (report.is_empty() || source.is_empty()))
        || (kind == "empty" && (!report.is_empty() || !source.is_empty()))
    {
        return Err("fn frontier retained poll artifacts exceed source bounds".into());
    }
    if host_image_sha256(&host)? != host_sha
        || digest(&bounded(&config_copy, 65_536)?) != digest(&config_bytes)
    {
        return Err("fn frontier Host or config changed while preparing plan".into());
    }
    retain_json(
        &directory.join("pin.json"),
        &json!({"format":FORMAT,"host":utf8_path(&host)?,"hostSha256":host_sha,
            "config":utf8_path(&config_copy)?,"configSha256":digest(&config_bytes),
            "operatorSocket":utf8_path(&socket)?,"planSha256":digest(plan_bytes),
            "requestSha256":digest(&request_bytes),
            "cursor.fncuSha256":digest(&cursor),"report.fn-eSha256":digest(&report),
            "source.emlSha256":digest(&source)}),
    )?;
    let _ = retained(&directory)?;
    print_json(&inspection)
}

fn verify_inspection(directory: &Path, state: &Retained) -> Result<()> {
    let target = (0..10_000)
        .map(|index| directory.join(format!("plan.reinspect-{index:04}.json")))
        .find(|candidate| !candidate.exists())
        .ok_or("fn frontier plan reinspection names exhausted")?;
    let checked = source_inspect(
        &state.host,
        &state.config,
        "fn-consumer-frontier-plan",
        &directory.join("plan.bin"),
        &target,
    )?;
    if checked != state.inspection {
        return Err("retained fn frontier plan differs from pinned Host".into());
    }
    Ok(())
}

fn approval_header(approval: &Value, state: &Retained, signing: &SigningKey) -> Result<Vec<u8>> {
    if member(approval, "type")? != APPROVAL
        || member(approval, "planSha256")? != digest(&state.plan)
        || member(approval, "signerPublicKey")? != hex(&signing.verifying_key().to_bytes())
    {
        return Err("fn frontier plan or gateway key differs from private approval".into());
    }
    for name in [
        "kind",
        "canonicalSpecHex",
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
        "fromPosition",
        "toPosition",
        "cursorHex",
        "reportBytes",
        "sourceBytes",
        "reportDigest",
        "sourceDigest",
        "expectedAuthorityRoot",
        "expectedTargetRoot",
        "signingKeyId",
        "signingKeyEpoch",
        "signingAlgorithm",
        "signingValidUntil",
    ] {
        if member(approval, name)? != member(&state.inspection, name)? {
            return Err(format!("fn frontier {name} differs from private approval"));
        }
    }
    for name in [
        "predecessor",
        "registrationReceipt",
        "selectedSequence",
        "releaseReceipt",
        "releaseKey",
    ] {
        if approval.get(name) != state.inspection.get(name) {
            return Err(format!("fn frontier {name} differs from private approval"));
        }
    }
    if member(&state.inspection, "signingAlgorithm")? != "1" {
        return Err("fn frontier credential algorithm is not Ed25519".into());
    }
    let header_hex = member(&state.inspection, "signingHeaderHex")?;
    let header = decode_hex(header_hex)?;
    if header.is_empty() || header.len() > 4096 || hex(&header) != header_hex {
        return Err("fn frontier signing header is not canonical hex".into());
    }
    Ok(header)
}

fn custody_key(path: &Path) -> Result<SigningKey> {
    let bytes = private_file(path, 32)?;
    let mut seed: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "fn frontier key must contain exactly 32 bytes".to_owned())?;
    let signing = SigningKey::from_bytes(&seed);
    seed.fill(0);
    Ok(signing)
}

fn pair(plan: &[u8], signature: &[u8]) -> Result<Vec<u8>> {
    if plan.is_empty() || plan.len() + 4 + 64 > MAX_PLAN || signature.len() != 64 {
        return Err("fn frontier op65 pair exceeds strict bound".into());
    }
    let mut bytes = Vec::with_capacity(4 + plan.len() + signature.len());
    bytes.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    bytes.extend_from_slice(plan);
    bytes.extend_from_slice(signature);
    Ok(bytes)
}

#[derive(PartialEq, Eq, Debug)]
enum SubmitMode {
    Fresh,
    LookupOnly,
}

fn submit_mode(
    directory: &Path,
    operation: u8,
    ingress: &[u8],
    socket: &Path,
) -> Result<SubmitMode> {
    let marker = directory.join("submit-attempt.json");
    if marker.exists() {
        let old: Value =
            serde_json::from_slice(&bounded(&marker, 4096)?).map_err(|e| e.to_string())?;
        if old.get("operation").and_then(Value::as_u64) != Some(operation as u64)
            || member(&old, "ingressSha256")? != digest(ingress)
            || member(&old, "operatorSocket")? != utf8_path(socket)?
        {
            return Err("fn frontier retained submit marker changed".into());
        }
        Ok(SubmitMode::LookupOnly)
    } else {
        retain_json(
            &marker,
            &json!({"operation":operation,"ingressSha256":digest(ingress),
                "operatorSocket":utf8_path(socket)?}),
        )?;
        Ok(SubmitMode::Fresh)
    }
}

fn lookup(directory: &Path, state: &Retained, ingress: &[u8]) -> Result<Option<Value>> {
    let (_, lookup_op) = operations(&state.inspection)?;
    for index in 0..16 {
        let stem = format!("lookup-{index:02}");
        if directory.join(format!("{stem}.attempt.json")).exists() {
            continue;
        }
        retain_json(
            &directory.join(format!("{stem}.attempt.json")),
            &json!({"operation":lookup_op,"ingressSha256":digest(ingress),
                "operatorSocket":utf8_path(&state.socket)?}),
        )?;
        let frame = transport::invoke_pinned(
            &state.socket,
            &state.config,
            &state.host_sha,
            lookup_op,
            ingress,
        )
        .map_err(|e| format!("fn frontier exact lookup uncertain: {e}"))?;
        pin_still(directory, state)?;
        create_private(&directory.join(format!("{stem}.frame")), &frame)?;
        sync_directory_ancestors(directory)?;
        let binary = expect_frame(&frame, lookup_op)?;
        create_private(&directory.join(format!("{stem}.outcome.bin")), binary)?;
        let value = outcome_inspect(
            directory,
            state,
            &directory.join(format!("{stem}.outcome.bin")),
            &stem,
        )?;
        return match member(&value, "type")? {
            "confirmed" => Ok(Some(receipt(&value)?)),
            "absent" => Ok(None),
            _ => Err("fn frontier lookup did not establish exact original".into()),
        };
    }
    Err("fn frontier lookup attempts exhausted".into())
}

/// One signed special event17 or event19. The submit marker is durable before
/// op60/62. Every reentry after a marker performs receipt-only lookup.
pub(super) fn advance(directory: &Path, key: &Path, approval_path: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _owner = transport::service_lock(&directory.join("fn-frontier.lock"))?;
    let state = retained(&directory)?;
    operator_socket_owned(&state.socket)?;
    verify_inspection(&directory, &state)?;
    pin_still(&directory, &state)?;
    let approval_bytes = private_file(approval_path, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes).map_err(|e| e.to_string())?;
    let signing = custody_key(key)?;
    let header = approval_header(&approval, &state, &signing)?;
    let approval_pin = directory.join("approval-pin.json");
    let approval_hash = digest(&approval_bytes);
    if approval_pin.exists() {
        let pinned: Value =
            serde_json::from_slice(&bounded(&approval_pin, 4096)?).map_err(|e| e.to_string())?;
        if member(&pinned, "approvalSha256")? != approval_hash
            || member(&pinned, "signerPublicKey")? != hex(&signing.verifying_key().to_bytes())
        {
            return Err("fn frontier retained approval or signer changed".into());
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
        return Err("fn frontier retained signature differs from exact plan/key".into());
    }
    let ingress_path = directory.join("ingress.bin");
    let ingress = if ingress_path.exists() {
        bounded(&ingress_path, 16_384)?
    } else {
        let marker = directory.join("assembly-attempt.json");
        let frame_path = directory.join("assembly.frame");
        let frame = if frame_path.exists() {
            bounded(&frame_path, 16_385)?
        } else {
            if marker.exists() {
                let old: Value =
                    serde_json::from_slice(&bounded(&marker, 4096)?).map_err(|e| e.to_string())?;
                if old.get("operation").and_then(Value::as_u64) != Some(65)
                    || member(&old, "planSha256")? != digest(&state.plan)
                    || member(&old, "signatureSha256")? != digest(&signature)
                {
                    return Err("fn frontier assembly marker changed".into());
                }
            } else {
                retain_json(
                    &marker,
                    &json!({"operation":65,"planSha256":digest(&state.plan),
                        "signatureSha256":digest(&signature)}),
                )?;
            }
            // Op65 only rechecks/assembles; it has no native or fn write.
            let frame = transport::invoke_pinned(
                &state.socket,
                &state.config,
                &state.host_sha,
                65,
                &pair(&state.plan, &signature)?,
            )
            .map_err(|e| format!("fn frontier assembly response uncertain: {e}"))?;
            pin_still(&directory, &state)?;
            create_private(&frame_path, &frame)?;
            sync_directory_ancestors(&directory)?;
            frame
        };
        let bytes = expect_frame(&frame, 65)?;
        if bytes.len() > 16_384 {
            return Err("fn frontier ingress exceeds strict bound".into());
        }
        create_private(&ingress_path, bytes)?;
        bytes.to_vec()
    };
    let assembly_frame = bounded(&directory.join("assembly.frame"), 16_385)?;
    if assembly_frame.first() != Some(&65) || assembly_frame[1..] != ingress {
        return Err("fn frontier ingress differs from retained assembly".into());
    }
    let (submit_op, _) = operations(&state.inspection)?;
    pin_still(&directory, &state)?;
    if submit_mode(&directory, submit_op, &ingress, &state.socket)? == SubmitMode::Fresh {
        match transport::invoke_pinned(
            &state.socket,
            &state.config,
            &state.host_sha,
            submit_op,
            &ingress,
        ) {
            Ok(frame) => {
                pin_still(&directory, &state)?;
                create_private(&directory.join("submit.frame"), &frame)?;
                sync_directory_ancestors(&directory)?;
                if let Ok(bytes) = expect_frame(&frame, submit_op) {
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
        pin_still(&directory, &state)?;
        let frame = bounded(&directory.join("submit.frame"), 16_385)?;
        let body = bounded(&directory.join("submit.outcome.bin"), 16_384)?;
        if frame.first() != Some(&submit_op) || frame[1..] != body {
            return Err("fn frontier submit outcome differs from exact Host frame".into());
        }
        if let Ok(value) = outcome_inspect(
            &directory,
            &state,
            &directory.join("submit.outcome.bin"),
            "submit",
        ) {
            if let Ok(original) = receipt(&value) {
                record_confirmed(&directory, &original)?;
                return print_json(&original);
            }
        }
    }
    match lookup(&directory, &state, &ingress)? {
        Some(original) => {
            record_confirmed(&directory, &original)?;
            print_json(&original)
        }
        None => Err("fn frontier exact lookup absent; no automatic resubmit".into()),
    }
}

/// Read-only recovery from the exact retained op60/62 attempt.
pub(super) fn lookup_original(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let _owner = transport::service_lock(&directory.join("fn-frontier.lock"))?;
    let state = retained(&directory)?;
    operator_socket_owned(&state.socket)?;
    pin_still(&directory, &state)?;
    let ingress = bounded(&directory.join("ingress.bin"), 16_384)?;
    let marker: Value =
        serde_json::from_slice(&bounded(&directory.join("submit-attempt.json"), 4096)?)
            .map_err(|e| e.to_string())?;
    let (submit_op, _) = operations(&state.inspection)?;
    if marker.get("operation").and_then(Value::as_u64) != Some(submit_op as u64)
        || member(&marker, "ingressSha256")? != digest(&ingress)
        || member(&marker, "operatorSocket")? != utf8_path(&state.socket)?
    {
        return Err("fn frontier exact submit marker changed".into());
    }
    match lookup(&directory, &state, &ingress)? {
        Some(original) => {
            record_confirmed(&directory, &original)?;
            print_json(&original)
        }
        None => Err("fn frontier exact lookup absent; no automatic resubmit".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn private_test_directory(label: &str) -> PathBuf {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "minidregg-fn-frontier-{label}-{}-{nonce}",
            std::process::id()
        ));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn selected_and_empty_routes_are_distinct() {
        assert_eq!(operations(&json!({"kind":"selected"})).unwrap(), (60, 61));
        assert_eq!(operations(&json!({"kind":"empty"})).unwrap(), (62, 63));
        assert!(operations(&json!({"kind":"legacy"})).is_err());
    }

    #[test]
    fn detached_signature_frame_requires_exact_raw_signature() {
        let frame = pair(b"source-plan", &[7u8; 64]).unwrap();
        assert_eq!(&frame[..4], &11u32.to_le_bytes());
        assert_eq!(&frame[4..15], b"source-plan");
        assert_eq!(&frame[15..], &[7u8; 64]);
        assert!(pair(b"source-plan", &[7u8; 63]).is_err());
        assert!(pair(b"", &[7u8; 64]).is_err());
        assert!(pair(&vec![0; MAX_PLAN - 67], &[7u8; 64]).is_err());
    }

    #[test]
    fn changed_host_or_config_refuses_retained_pin() {
        let directory = private_test_directory("pin");
        let host = directory.join("host.bin");
        let config = directory.join("config.json");
        let socket = directory.join("operator.sock");
        create_private(&host, b"original-host").unwrap();
        create_private(&config, b"original-config").unwrap();
        let plan = b"source-plan";
        create_private(&directory.join("request.bin"), b"request").unwrap();
        create_private(&directory.join("plan.bin"), plan).unwrap();
        retain_json(
            &directory.join("plan.json"),
            &json!({"type":"fn-consumer-frontier-plan-v2","kind":"selected",
                "canonicalPlanHex":hex(plan)}),
        )
        .unwrap();
        for (name, bytes) in [
            ("cursor.fncu", b"cursor".as_slice()),
            ("report.fn-e", b"report".as_slice()),
            ("source.eml", b"source".as_slice()),
        ] {
            create_private(&directory.join(name), bytes).unwrap();
        }
        retain_json(
            &directory.join("pin.json"),
            &json!({"format":FORMAT,"host":host.to_str().unwrap(),
                "hostSha256":digest(b"original-host"),
                "config":config.to_str().unwrap(),
                "configSha256":digest(b"original-config"),
                "operatorSocket":socket.to_str().unwrap(),
                "planSha256":digest(plan),"requestSha256":digest(b"request"),
                "cursor.fncuSha256":digest(b"cursor"),
                "report.fn-eSha256":digest(b"report"),
                "source.emlSha256":digest(b"source")}),
        )
        .unwrap();
        let state = retained(&directory).unwrap();
        fs::write(&host, b"changed-host").unwrap();
        assert!(pin_still(&directory, &state).is_err());
        fs::write(&host, b"original-host").unwrap();
        fs::write(&config, b"changed-config").unwrap();
        assert!(pin_still(&directory, &state).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn durable_submit_marker_allows_only_exact_lookup_reentry() {
        let directory = private_test_directory("submit");
        let socket = directory.join("operator.sock");
        assert_eq!(
            submit_mode(&directory, 60, b"original-ingress", &socket).unwrap(),
            SubmitMode::Fresh
        );
        assert_eq!(
            submit_mode(&directory, 60, b"original-ingress", &socket).unwrap(),
            SubmitMode::LookupOnly
        );
        assert!(submit_mode(&directory, 60, b"changed-ingress", &socket).is_err());
        assert!(submit_mode(&directory, 62, b"original-ingress", &socket).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn receipt_refuses_noncanonical_decimal_fields() {
        let original = json!({"type":"confirmed","transactionId":"01",
            "eventId":"2","acceptedCount":"3","imageBoundary":"4"});
        assert!(receipt(&original).is_err());
        let corrected = json!({"type":"confirmed","transactionId":"1",
            "eventId":"2","acceptedCount":"3","imageBoundary":"4"});
        assert!(receipt(&corrected).is_ok());
    }
}
