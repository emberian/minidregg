//! Operator custody for one source-authored application share issue. The Host
//! owns the Request, Plan, signature-list and Ingress codecs; this client pins
//! their exact bytes, checks the operator's approval, and never silently
//! resubmits an uncertain native operation.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, PermissionsExt};

const REQUEST_LIMIT: usize = 256 * 1024;
const FORMAT: &str = "minidregg-application-share-issue-custody-v1";

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

fn private_bytes(path: &Path, limit: usize) -> Result<Vec<u8>> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = path
        .parent()
        .ok_or("approval file has no parent directory")?;
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
        return Err("share issue approval must be an operator-private file and directory".into());
    }
    let mut bytes = Vec::new();
    file.take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err("share issue approval exceeds bound".into());
    }
    Ok(bytes)
}

fn strict_hex(value: &str, bytes: usize) -> bool {
    value.len() == 2 * bytes
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

fn member<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("share issue approval or inspection lacks {name}"))
}

fn approved_header(slot: &Value, signer: &Value, signing: &SigningKey) -> Result<Vec<u8>> {
    let header = member(slot, "header")?;
    let details = slot
        .get("signing")
        .ok_or("share issue signing slot lacks source inspection")?;
    if details.get("decoded").and_then(Value::as_bool) != Some(true)
        || member(details, "canonical")? != header
        || member(details, "keyId")? != member(signer, "keyId")?
        || member(details, "keyEpoch")? != member(signer, "keyEpoch")?
        || member(details, "algorithm")? != "1"
        || member(slot, "role")? != member(signer, "role")?
        || member(slot, "index")? != member(signer, "index")?
    {
        return Err("share issue signing header differs from approved custody slot".into());
    }
    let public = member(signer, "publicKey")?;
    if !strict_hex(public, 32) || public != hex(&signing.verifying_key().to_bytes()) {
        return Err("share issue signer public key differs from approved enrollment pin".into());
    }
    if header.is_empty() || header.len() % 2 != 0 || !strict_hex(header, header.len() / 2) {
        return Err("share issue signing header is not canonical hex".into());
    }
    let bytes: Vec<u8> = (0..header.len())
        .step_by(2)
        .map(|offset| {
            u8::from_str_radix(&header[offset..offset + 2], 16)
                .map_err(|_| "invalid Host signing header".to_owned())
        })
        .collect::<Result<_>>()?;
    if member(signer, "headerSha256")? != digest(&bytes) {
        return Err("share issue signing header differs from exact operator approval".into());
    }
    Ok(bytes)
}

fn custody_key(path: &Path) -> Result<SigningKey> {
    let parent = path
        .parent()
        .ok_or("share issue key has no parent directory")?;
    let directory = fs::symlink_metadata(parent).map_err(|e| e.to_string())?;
    let named = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot inspect share issue key {}: {e}", path.display()))?;
    let mut file = File::open(path)
        .map_err(|e| format!("cannot open share issue key {}: {e}", path.display()))?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    if !directory.is_dir()
        || directory.uid() != unsafe { geteuid() }
        || directory.permissions().mode() & 0o077 != 0
        || !named.file_type().is_file()
        || named.uid() != unsafe { geteuid() }
        || named.mode() & 0o077 != 0
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err("share issue signing key must be an owner-private regular file".into());
    }
    let mut seed = [0u8; 32];
    file.read_exact(&mut seed)
        .map_err(|e| format!("share issue key must contain 32 bytes: {e}"))?;
    let mut excess = [0u8; 1];
    if file.read(&mut excess).map_err(|e| e.to_string())? != 0 {
        return Err("share issue key must contain exactly 32 bytes".into());
    }
    let signing = SigningKey::from_bytes(&seed);
    seed.fill(0);
    Ok(signing)
}

fn check_approval(approval: &Value, request: &[u8], inspection: &Value) -> Result<()> {
    if member(approval, "type")? != "minidregg-application-share-issue-approval-v1"
        || !strict_hex(member(approval, "requestSha256")?, 32)
        || member(approval, "requestSha256")? != digest(request)
        || member(inspection, "canonicalRequest")? != hex(request)
        || member(approval, "canonicalSpec")? != member(inspection, "canonicalSpec")?
    {
        return Err("share issue approval differs from exact source-authored Request".into());
    }
    Ok(())
}

fn check_intended_selectors(approval: &Value, plan: &Value) -> Result<()> {
    let spec = plan
        .get("spec")
        .ok_or("share issue plan lacks Spec presentation")?;
    let ticket = spec
        .get("ticket")
        .ok_or("share issue plan lacks ticket presentation")?;
    let participant = ticket
        .get("participant")
        .ok_or("share issue plan lacks participant presentation")?;
    if member(approval, "issuer")? != member(spec, "issuer")?
        || member(approval, "appDelegateCapability")? != member(spec, "appDelegateCapability")?
        || member(approval, "participantSubject")? != member(participant, "subject")?
        || member(approval, "ticketResource")? != member(ticket, "resource")?
    {
        return Err("share issue plan differs from approved issuer, subject or capability".into());
    }
    Ok(())
}

fn operator_socket_owned(socket: &Path) -> Result<()> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = socket.parent().ok_or("operator socket has no parent")?;
    let directory = fs::symlink_metadata(parent)
        .map_err(|e| format!("cannot inspect operator directory: {e}"))?;
    let node =
        fs::symlink_metadata(socket).map_err(|e| format!("cannot inspect operator socket: {e}"))?;
    if !directory.is_dir()
        || directory.uid() != uid
        || directory.permissions().mode() & 0o077 != 0
        || !node.file_type().is_socket()
        || node.uid() != uid
        || node.permissions().mode() & 0o077 != 0
    {
        return Err(
            "operator socket must be owner-private under an owner-private directory".into(),
        );
    }
    Ok(())
}

fn expect_reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [255, ..] => Err(format!(
            "share issue Host refused op{operation}; frame retained"
        )),
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!(
            "share issue op{operation} returned an invalid frame"
        )),
    }
}

fn retain_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("share issue evidence has no parent")?)
}

struct Retained {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    ingress: Vec<u8>,
}

fn retained(directory: &Path, socket_override: Option<&Path>) -> Result<Retained> {
    drain::private_dir(directory)?;
    let pin_bytes = bounded(&directory.join("pin.json"), 65_536)?;
    let pin: Value = serde_json::from_slice(&pin_bytes).map_err(|e| e.to_string())?;
    if member(&pin, "format")? != FORMAT {
        return Err("unsupported share issue custody pin".into());
    }
    let host = PathBuf::from(member(&pin, "host")?);
    let config = PathBuf::from(member(&pin, "config")?);
    let socket = match socket_override {
        Some(path) => absolute(path)?,
        None => PathBuf::from(member(&pin, "operatorSocket")?),
    };
    let ingress = bounded(
        &directory.join("ingress.bin"),
        transport::HOST_MAX_FRAME - 1,
    )?;
    let host_sha = host_image_sha256(&host)?;
    if host_sha != member(&pin, "hostSha256")?
        || digest(&bounded(&config, 65_536)?) != member(&pin, "configSha256")?
        || digest(&bounded(&directory.join("request.bin"), REQUEST_LIMIT)?)
            != member(&pin, "requestSha256")?
        || digest(&bounded(
            &directory.join("plan.bin"),
            transport::HOST_MAX_FRAME - 1,
        )?) != member(&pin, "planSha256")?
        || digest(&private_bytes(&directory.join("approval.json"), 65_536)?)
            != member(&pin, "approvalSha256")?
        || digest(&ingress) != member(&pin, "ingressSha256")?
    {
        return Err("retained share issue Host, config or exact ingress changed".into());
    }
    Ok(Retained {
        host,
        config,
        socket,
        ingress,
    })
}

fn outcome_at(
    directory: &Path,
    name: &str,
    frame: &[u8],
    operation: u8,
    state: &Retained,
) -> Result<Value> {
    let body = expect_reply(frame, operation)?;
    let binary = directory.join(format!("{name}.outcome.bin"));
    let presentation = directory.join(format!("{name}.outcome.json"));
    create_private(&binary, body)?;
    sync_directory_ancestors(directory)?;
    inspect(
        &state.host,
        &state.config,
        "outcome",
        &binary,
        &presentation,
    )
}

fn receipt_field<'a>(value: &'a Value, field: &str) -> Result<&'a str> {
    let text = member(value, field)?;
    if text.is_empty()
        || text.len() > 80
        || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(format!("share issue receipt has noncanonical {field}"));
    }
    Ok(text)
}

fn confirmed(value: &Value) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Err("share issue outcome did not confirm".into());
    }
    for field in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
        receipt_field(value, field)?;
    }
    Ok(())
}

fn same_receipt(original: &Value, recovered: &Value) -> Result<()> {
    confirmed(original)?;
    confirmed(recovered)?;
    for field in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
        if receipt_field(original, field)? != receipt_field(recovered, field)? {
            return Err(format!("share issue historical lookup changed {field}"));
        }
    }
    Ok(())
}

fn receipt_projection(value: &Value) -> Result<Value> {
    confirmed(value)?;
    Ok(
        json!({"transactionId":receipt_field(value,"transactionId")?,
        "eventId":receipt_field(value,"eventId")?,
        "acceptedCount":receipt_field(value,"acceptedCount")?,
        "imageBoundary":receipt_field(value,"imageBoundary")?}),
    )
}

fn reconcile_receipt(first: Option<&Value>, observed: &Value) -> Result<Option<Value>> {
    if confirmed(observed).is_err() {
        return Ok(first.cloned());
    }
    if let Some(original) = first {
        same_receipt(original, observed)?;
        Ok(Some(original.clone()))
    } else {
        Ok(Some(observed.clone()))
    }
}

fn retained_outcome_bytes(directory: &Path, stem: &str) -> Result<Option<PathBuf>> {
    let binary = directory.join(format!("{stem}.outcome.bin"));
    let frame_path = directory.join(format!("{stem}.frame"));
    if !frame_path.exists() {
        if binary.exists() {
            return Err("retained share issue outcome lacks exact Host reply frame".into());
        }
        return Ok(None);
    }
    let frame = bounded(&frame_path, transport::HOST_MAX_FRAME)?;
    let operation = if stem == "submit" { 28 } else { 29 };
    if frame.first() == Some(&255) && !binary.exists() {
        return Ok(None);
    }
    if frame.first() != Some(&operation) || frame.len() < 2 {
        return Err("retained share issue outcome differs from exact Host reply frame".into());
    }
    if binary.exists() {
        let outcome_bytes = bounded(&binary, transport::HOST_MAX_FRAME - 1)?;
        if frame[1..] != outcome_bytes {
            return Err("retained share issue outcome differs from exact Host reply frame".into());
        }
    } else {
        // The frame is synced before extraction. Reconstruct the sole possible
        // canonical outcome after a crash in that narrow interval.
        create_private(&binary, &frame[1..])?;
        sync_directory_ancestors(directory)?;
    }
    Ok(Some(binary))
}

fn reinspect(directory: &Path, state: &Retained, stem: &str) -> Result<Option<Value>> {
    let Some(binary) = retained_outcome_bytes(directory, stem)? else {
        return Ok(None);
    };
    let path = (0..10_000)
        .map(|index| directory.join(format!("{stem}.reinspect-{index:04}.json")))
        .find(|path| !path.exists())
        .ok_or("share issue reinspection names exhausted")?;
    let observed = inspect(&state.host, &state.config, "outcome", &binary, &path)?;
    let cached = directory.join(format!("{stem}.outcome.json"));
    if cached.exists() {
        let saved: Value = serde_json::from_slice(&bounded(&cached, 65_536)?)
            .map_err(|e| format!("invalid retained share issue outcome: {e}"))?;
        if saved != observed {
            return Err("retained share issue outcome presentation changed".into());
        }
    }
    Ok(Some(observed))
}

/// The first confirmed source-owned outcome is a durable anchor. This scans
/// retained binary outcomes as well as the anchor file, so a crash between
/// writing the first outcome and writing the anchor cannot erase the check.
fn historical_anchor(directory: &Path, state: &Retained, lookups: usize) -> Result<Option<Value>> {
    let mut first: Option<(String, String, Value)> = None;
    for stem in std::iter::once("submit".to_owned())
        .chain((0..lookups).map(|index| format!("lookup-{index:04}")))
    {
        let Some(observed) = reinspect(directory, state, &stem)? else {
            continue;
        };
        if confirmed(&observed).is_err() {
            continue;
        }
        let binary_hash = digest(&bounded(
            &directory.join(format!("{stem}.outcome.bin")),
            transport::HOST_MAX_FRAME - 1,
        )?);
        if let Some((_, _, original)) = &first {
            let _ = reconcile_receipt(Some(original), &observed)?;
        } else {
            first = Some((stem, binary_hash, observed));
        }
    }
    let Some((stem, binary_hash, original)) = first else {
        if directory.join("receipt-anchor.json").exists() {
            return Err("share issue receipt anchor lacks exact retained outcome".into());
        }
        return Ok(None);
    };
    let expected = json!({"type":"minidregg-share-issue-receipt-anchor-v1",
        "source":stem,"outcomeSha256":binary_hash,
        "receipt":receipt_projection(&original)?});
    let anchor_path = directory.join("receipt-anchor.json");
    if anchor_path.exists() {
        let saved: Value = serde_json::from_slice(&bounded(&anchor_path, 4096)?)
            .map_err(|e| format!("invalid share issue receipt anchor: {e}"))?;
        if saved != expected {
            return Err("share issue receipt anchor differs from original exact outcome".into());
        }
    } else {
        retain_json(&anchor_path, &expected)?;
    }
    Ok(Some(original))
}

/// First submit is one durable attempt. If the response is lost, the marker
/// forbids another submit; the operator must use the exact read-only lookup.
pub(super) fn submit(directory: &Path, socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let state = retained(&directory, socket)?;
    let marker = directory.join("submit-marker.json");
    if marker.exists() {
        return Err("share issue submit already attempted; use exact lookup".into());
    }
    retain_json(
        &marker,
        &json!({"type":"minidregg-share-issue-submit-attempt-v1",
            "ingressSha256":digest(&state.ingress),"socket":utf8_path(&state.socket)?}),
    )?;
    let frame = session_invoke(
        &state.host,
        &state.socket,
        &state.config,
        28,
        &state.ingress,
    )
    .map_err(|e| format!("share issue submit uncertain; exact ingress retained: {e}"))?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let outcome = outcome_at(&directory, "submit", &frame, 28, &state)?;
    confirmed(&outcome)?;
    historical_anchor(&directory, &state, 0)?;
    print_json(&outcome)
}

/// Lookup selects exact historical identity and never creates a second issue.
pub(super) fn lookup(directory: &Path, socket: Option<&Path>) -> Result<()> {
    let directory = absolute(directory)?;
    let state = retained(&directory, socket)?;
    if !directory.join("submit-marker.json").exists() {
        return Err("share issue lookup requires a retained submit attempt".into());
    }
    let submit_marker: Value =
        serde_json::from_slice(&bounded(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|e| format!("invalid share issue submit marker: {e}"))?;
    if member(&submit_marker, "type")? != "minidregg-share-issue-submit-attempt-v1"
        || member(&submit_marker, "ingressSha256")? != digest(&state.ingress)
    {
        return Err("share issue submit marker differs from retained exact ingress".into());
    }
    let mut index = 0;
    while directory
        .join(format!("lookup-{index:04}.marker.json"))
        .exists()
    {
        index += 1;
        if index >= 10_000 {
            return Err("share issue lookup evidence names exhausted".into());
        }
    }
    historical_anchor(&directory, &state, index)?;
    let stem = format!("lookup-{index:04}");
    retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({"type":"minidregg-share-issue-lookup-v1",
            "ingressSha256":digest(&state.ingress),"socket":utf8_path(&state.socket)?}),
    )?;
    let frame = session_invoke(
        &state.host,
        &state.socket,
        &state.config,
        29,
        &state.ingress,
    )?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    let outcome = outcome_at(&directory, &stem, &frame, 29, &state)?;
    confirmed(&outcome)?;
    historical_anchor(&directory, &state, index + 1)?;
    print_json(&outcome)
}

/// The approval belongs to the operator, not the producer. Its request hash
/// pins all payer/funding/capability selectors; its ordered signers pin who may
/// sign each exact Host-selected header. Live native admission still decides.
pub(super) fn prepare(
    host: &Path,
    config: &Path,
    operator_socket: &Path,
    request_json: &Path,
    approval_json: &Path,
    directory: &Path,
) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let operator_socket = absolute(operator_socket)?;
    operator_socket_owned(&operator_socket)?;
    let directory = absolute(directory)?;
    let source = bounded(request_json, REQUEST_LIMIT)?;
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let initial_host_sha = host_image_sha256(&host)?;
    let initial_config = bounded(&config, 65_536)?;
    let check_inputs = || -> Result<()> {
        if host_image_sha256(&host)? != initial_host_sha
            || bounded(&config, 65_536)? != initial_config
            || private_bytes(approval_json, 65_536)? != approval_bytes
        {
            return Err("share issue Host or config changed during custody".into());
        }
        Ok(())
    };
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|e| format!("invalid share issue approval: {e}"))?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|e| format!("cannot create share issue custody directory: {e}"))?;
    sync_directory_ancestors(&directory)?;
    create_private(&directory.join("request.json"), &source)?;
    create_private(&directory.join("approval.json"), &approval_bytes)?;
    create_private(&directory.join("config.json"), &initial_config)?;
    let request_bin = directory.join("request.bin");
    process(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new("application-share-issue-request"),
            directory.join("request.json").as_os_str(),
            request_bin.as_os_str(),
        ],
    )?;
    sync_retained_call(&directory, &request_bin)?;
    let request = bounded(&request_bin, REQUEST_LIMIT)?;
    let inspected_request = inspect(
        &host,
        &config,
        "application-share-issue-request",
        &request_bin,
        &directory.join("request-inspected.json"),
    )?;
    if member(&inspected_request, "type")? != "application-share-issue-request-v1" {
        return Err("Host inspected the wrong share issue Request profile".into());
    }
    check_inputs()?;
    check_approval(&approval, &request, &inspected_request)?;

    let frame = session_invoke(&host, &operator_socket, &config, 32, &request)?;
    check_inputs()?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let plan = expect_reply(&frame, 32)?;
    let plan_path = directory.join("plan.bin");
    create_private(&plan_path, plan)?;
    let inspected_plan = inspect(
        &host,
        &config,
        "application-share-issue-plan",
        &plan_path,
        &directory.join("plan-inspected.json"),
    )?;
    if member(&inspected_plan, "type")? != "application-share-issue-plan-v2" {
        return Err("Host inspected the wrong share issue Plan profile".into());
    }
    check_inputs()?;
    check_approval(&approval, &request, &inspected_plan)?;
    if member(&inspected_request, "canonicalSpec")? != member(&inspected_plan, "canonicalSpec")? {
        return Err("share issue plan changed the approved canonical ticket Spec".into());
    }
    check_intended_selectors(&approval, &inspected_plan)?;
    let slots = inspected_plan
        .get("slots")
        .and_then(Value::as_array)
        .ok_or("share issue plan lacks ordered signing slots")?;
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("share issue approval lacks ordered signers")?;
    if slots.is_empty() || slots.len() != signers.len() {
        return Err("share issue signing slot count differs from approval".into());
    }
    check_inputs()?;
    let mut signatures = Vec::with_capacity(slots.len());
    for (slot, signer) in slots.iter().zip(signers) {
        let key_path = Path::new(member(signer, "keyPath")?);
        if !key_path.is_absolute() {
            return Err("share issue custody key path must be absolute".into());
        }
        let key = custody_key(key_path)?;
        let header = approved_header(slot, signer, &key)?;
        signatures.push(Value::String(hex(&key.sign(&header).to_bytes())));
    }
    let signatures_json = directory.join("signatures.json");
    retain_json(&signatures_json, &Value::Array(signatures))?;
    let signatures_path = directory.join("signatures.bin");
    process(
        &host,
        &config,
        &[
            OsStr::new("signatures"),
            signatures_json.as_os_str(),
            signatures_path.as_os_str(),
        ],
    )?;
    let signatures_bytes = bounded(&signatures_path, REQUEST_LIMIT)?;
    check_inputs()?;
    let mut assembly = Vec::with_capacity(4 + plan.len() + signatures_bytes.len());
    assembly.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    assembly.extend_from_slice(plan);
    assembly.extend_from_slice(&signatures_bytes);
    let assembled_frame = session_invoke(&host, &operator_socket, &config, 33, &assembly)?;
    check_inputs()?;
    create_private(&directory.join("assembly.frame"), &assembled_frame)?;
    let ingress = expect_reply(&assembled_frame, 33)?;
    create_private(&directory.join("ingress.bin"), ingress)?;
    let pin = json!({"format":FORMAT,"host":utf8_path(&host)?,
        "hostSha256":initial_host_sha,"config":utf8_path(&config)?,
        "configSha256":digest(&initial_config),
        "operatorSocket":utf8_path(&operator_socket)?,
        "approvalSha256":digest(&approval_bytes),
        "requestSha256":digest(&request),"planSha256":digest(plan),
        "ingressSha256":digest(ingress)});
    retain_json(&directory.join("pin.json"), &pin)?;
    println!("{}", directory.join("ingress.bin").display());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn approval_binds_complete_canonical_request() {
        let request = [1u8, 2, 3];
        let approval = json!({"type":"minidregg-application-share-issue-approval-v1",
            "requestSha256":digest(&request),"canonicalSpec":"abcd"});
        let inspection = json!({"canonicalRequest":hex(&request),"canonicalSpec":"abcd"});
        assert!(check_approval(&approval, &request, &inspection).is_ok());
        assert!(check_approval(&approval, &[1, 2, 4], &inspection).is_err());
        assert!(check_approval(&approval, &request, &json!({"canonicalRequest":"01"})).is_err());
    }

    #[test]
    fn custody_rejects_reordered_or_substituted_signing_slot() {
        let signing = SigningKey::from_bytes(&[7u8; 32]);
        let public = hex(&signing.verifying_key().to_bytes());
        let signer = json!({"keyId":"12","keyEpoch":"2","role":"5","index":"0",
            "publicKey":public,"headerSha256":digest(&[0xaa,0xbb])});
        let slot = json!({"role":"5","index":"0","header":"aabb",
            "signing":{"decoded":true,"canonical":"aabb","keyId":"12",
                "keyEpoch":"2","algorithm":"1"}});
        assert_eq!(
            approved_header(&slot, &signer, &signing).unwrap(),
            [0xaa, 0xbb]
        );
        let mut reordered = slot.clone();
        reordered["index"] = Value::String("1".into());
        assert!(approved_header(&reordered, &signer, &signing).is_err());
        let mut substituted = slot;
        substituted["signing"]["canonical"] = Value::String("aacc".into());
        assert!(approved_header(&substituted, &signer, &signing).is_err());
    }

    #[test]
    fn lost_submit_recovery_anchors_first_lookup_and_rejects_later_drift() {
        let absent = json!({"type":"absent"});
        let first = json!({"type":"confirmed","confirmation":"replayed",
            "transactionId":"10","eventId":"11","acceptedCount":"12",
            "imageBoundary":"13"});
        let mut changed = first.clone();
        changed["eventId"] = Value::String("99".into());
        // A lost submit reply leaves no original receipt. The first retained
        // lookup becomes the anchor; rescanning its bytes after a crash gives
        // the same anchor before a second lookup is considered.
        assert!(reconcile_receipt(None, &absent).unwrap().is_none());
        let anchor = reconcile_receipt(None, &first).unwrap().unwrap();
        let after_crash = reconcile_receipt(None, &first).unwrap().unwrap();
        assert_eq!(anchor, after_crash);
        assert!(reconcile_receipt(Some(&after_crash), &changed).is_err());
    }

    #[test]
    fn frame_only_crash_recovers_exact_outcome_before_next_lookup() {
        let directory = std::env::temp_dir().join(format!(
            "mini-share-frame-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        create_private(&directory.join("lookup-0000.frame"), &[29, 7, 8]).unwrap();
        let recovered = retained_outcome_bytes(&directory, "lookup-0000")
            .unwrap()
            .unwrap();
        assert_eq!(fs::read(&recovered).unwrap(), [7, 8]);
        assert_eq!(
            retained_outcome_bytes(&directory, "lookup-0000")
                .unwrap()
                .unwrap(),
            recovered
        );
        fs::write(&recovered, [7, 9]).unwrap();
        assert!(retained_outcome_bytes(&directory, "lookup-0000").is_err());
        fs::remove_dir_all(directory).unwrap();
    }
}
