//! Operator custody for one source-authored event21 purse reserve. The Host
//! owns request, plan, signature-list, call and outcome codecs. No public HTTP
//! caller can select a payer, key or capability through this module.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{DirBuilderExt, FileTypeExt, MetadataExt, PermissionsExt};

const FORMAT: &str = "minidregg-agent-reserve-custody-v1";
const APPROVAL: &str = "minidregg-agent-reserve-approval-v1";
const REQUEST_LIMIT: usize = transport::HOST_MAX_FRAME - 1;
// Host.Main.maxDispatchInspectionJsonBytes = 8 * maxFrame. The projection
// contains hex copies of the plan, request, context, and complete HTTP body.
const JSON_LIMIT: usize = 8 * transport::HOST_MAX_FRAME;

mod lifetime_v3;
pub(super) use lifetime_v3::{
    lifetime_lookup, lifetime_paid_lookup, lifetime_paid_plan, lifetime_paid_seal,
    lifetime_paid_submit, lifetime_plan, lifetime_seal, lifetime_submit,
};

pub(super) fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

pub(super) fn bounded(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let named = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !named.file_type().is_file() || named.len() == 0 || named.len() > limit as u64 {
        return Err(format!("{} is not a bounded regular file", path.display()));
    }
    let mut file = File::open(path).map_err(|error| error.to_string())?;
    let opened = file.metadata().map_err(|error| error.to_string())?;
    if (named.dev(), named.ino()) != (opened.dev(), opened.ino()) {
        return Err(format!("{} changed before read", path.display()));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() != named.len() as usize || bytes.len() > limit {
        return Err(format!("{} changed during read", path.display()));
    }
    Ok(bytes)
}

pub(super) fn private_bytes(path: &Path, limit: usize) -> Result<Vec<u8>> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = path.parent().ok_or("custody path has no parent")?;
    let directory = fs::symlink_metadata(parent).map_err(|error| error.to_string())?;
    let named = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !directory.is_dir()
        || directory.uid() != uid
        || directory.permissions().mode() & 0o077 != 0
        || !named.file_type().is_file()
        || named.uid() != uid
        || named.permissions().mode() & 0o077 != 0
    {
        return Err("agent reserve custody input must be owner-private".into());
    }
    bounded(path, limit)
}

pub(super) fn private_socket(path: &Path) -> Result<()> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = path.parent().ok_or("operator socket has no parent")?;
    let directory = fs::symlink_metadata(parent).map_err(|error| error.to_string())?;
    let named = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    if !directory.is_dir()
        || directory.uid() != uid
        || directory.permissions().mode() & 0o077 != 0
        || !named.file_type().is_socket()
        || named.uid() != uid
        || named.permissions().mode() & 0o077 != 0
    {
        return Err("agent reserve operator socket must be owner-private".into());
    }
    Ok(())
}

pub(super) fn retain_generated(path: &Path) -> Result<()> {
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let uid = unsafe { geteuid() };
    let parent = path.parent().ok_or("generated evidence has no parent")?;
    let directory = fs::symlink_metadata(parent).map_err(|error| error.to_string())?;
    let named = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    let file = File::open(path).map_err(|error| error.to_string())?;
    let opened = file.metadata().map_err(|error| error.to_string())?;
    if !directory.is_dir()
        || directory.uid() != uid
        || directory.permissions().mode() & 0o077 != 0
        || !named.file_type().is_file()
        || named.uid() != uid
        || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
    {
        return Err("source-generated reserve evidence is not an owner file".into());
    }
    file.set_permissions(fs::Permissions::from_mode(0o600))
        .and_then(|()| file.sync_all())
        .map_err(|error| format!("cannot durably restrict {}: {error}", path.display()))?;
    sync_directory_ancestors(parent)
}

pub(super) fn source(host: &Path, config: &Path, arguments: &[&OsStr]) -> Result<()> {
    let output = Command::new(host)
        .arg(config)
        .args(arguments)
        .output()
        .map_err(|error| format!("cannot invoke selected Host: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "selected Host refused source operation: {}",
            output.status
        ));
    }
    Ok(())
}

pub(super) fn source_inspect(
    host: &Path,
    config: &Path,
    kind: &str,
    input: &Path,
    output: &Path,
) -> Result<Value> {
    source(
        host,
        config,
        &[
            OsStr::new("inspect"),
            OsStr::new(kind),
            input.as_os_str(),
            output.as_os_str(),
        ],
    )?;
    retain_generated(output)?;
    serde_json::from_slice(&bounded(output, JSON_LIMIT)?)
        .map_err(|error| format!("invalid Host inspection: {error}"))
}

pub(super) fn retain_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("reserve evidence has no parent")?)
}

pub(super) fn field<'a>(value: &'a Value, name: &str) -> Result<&'a str> {
    value
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("agent reserve custody lacks {name}"))
}

fn strict_hex(value: &str) -> bool {
    !value.is_empty()
        && value.len().is_multiple_of(2)
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

pub(super) fn decode_hex(value: &str) -> Result<Vec<u8>> {
    if !strict_hex(value) {
        return Err("noncanonical reserve hex".into());
    }
    (0..value.len())
        .step_by(2)
        .map(|index| {
            u8::from_str_radix(&value[index..index + 2], 16)
                .map_err(|error| format!("invalid reserve hex: {error}"))
        })
        .collect()
}

fn expect_reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [255, ..] => Err(format!(
            "agent reserve Host refused op{operation}; frame retained"
        )),
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!(
            "agent reserve op{operation} returned an invalid frame"
        )),
    }
}

fn exact_receipt(value: &Value) -> Result<Value> {
    if field(value, "type")? != "confirmed" {
        return Err("agent reserve outcome did not confirm".into());
    }
    if !matches!(field(value, "confirmation")?, "installed" | "replayed") {
        return Err("agent reserve confirmation is not accepted history".into());
    }
    let mut receipt = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "imageBoundary"] {
        let value = field(value, name)?;
        if value.is_empty()
            || value.len() > 80
            || (value.len() > 1 && value.starts_with('0'))
            || !value.bytes().all(|byte| byte.is_ascii_digit())
        {
            return Err(format!("agent reserve receipt has noncanonical {name}"));
        }
        receipt.insert(name.to_owned(), Value::String(value.to_owned()));
    }
    if receipt["acceptedCount"] == "0" {
        return Err("agent reserve has no accepted transition".into());
    }
    let accepted = receipt["acceptedCount"]
        .as_str()
        .ok_or("agent reserve accepted count is not text")?;
    receipt.insert(
        "reserveIndex".to_owned(),
        Value::String(previous_decimal(accepted)?),
    );
    Ok(Value::Object(receipt))
}

fn previous_decimal(value: &str) -> Result<String> {
    if value.is_empty()
        || value == "0"
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err("agent reserve accepted count cannot select an index".into());
    }
    let mut digits = value.as_bytes().to_vec();
    for digit in digits.iter_mut().rev() {
        if *digit == b'0' {
            *digit = b'9';
        } else {
            *digit -= 1;
            break;
        }
    }
    let first = digits.iter().position(|digit| *digit != b'0');
    match first {
        Some(index) => String::from_utf8(digits[index..].to_vec()).map_err(|e| e.to_string()),
        None => Ok("0".to_owned()),
    }
}

struct Pin {
    host: PathBuf,
    config: PathBuf,
    operator_socket: PathBuf,
    public_socket: PathBuf,
    request: Vec<u8>,
    plan: Vec<u8>,
}

fn pinned(directory: &Path) -> Result<Pin> {
    drain::private_dir(directory)?;
    let pin: Value = serde_json::from_slice(&private_bytes(&directory.join("pin.json"), 4096)?)
        .map_err(|error| format!("invalid agent reserve pin: {error}"))?;
    if field(&pin, "format")? != FORMAT {
        return Err("unsupported agent reserve pin".into());
    }
    let host = PathBuf::from(field(&pin, "host")?);
    let config = PathBuf::from(field(&pin, "config")?);
    let operator_socket = PathBuf::from(field(&pin, "operatorSocket")?);
    let public_socket = PathBuf::from(field(&pin, "publicSocket")?);
    if [
        host.as_path(),
        config.as_path(),
        operator_socket.as_path(),
        public_socket.as_path(),
    ]
    .iter()
    .any(|path| !path.is_absolute())
        || operator_socket == public_socket
        || host_image_sha256(&host)? != field(&pin, "hostSha256")?
        || digest(&bounded(&config, 65_536)?) != field(&pin, "configSha256")?
    {
        return Err("agent reserve Host, config or socket identity changed".into());
    }
    let request = private_bytes(&directory.join("request.bin"), REQUEST_LIMIT)?;
    let plan = private_bytes(&directory.join("plan.bin"), REQUEST_LIMIT)?;
    if digest(&request) != field(&pin, "requestSha256")?
        || digest(&plan) != field(&pin, "planSha256")?
        || bounded(&directory.join("plan.frame"), transport::HOST_MAX_FRAME)?
            != [vec![58], plan.clone()].concat()
    {
        return Err("agent reserve exact request or plan changed".into());
    }
    Ok(Pin {
        host,
        config,
        operator_socket,
        public_socket,
        request,
        plan,
    })
}

fn same_pin(directory: &Path, earlier: &Pin) -> Result<()> {
    let current = pinned(directory)?;
    if current.host != earlier.host
        || current.config != earlier.config
        || current.operator_socket != earlier.operator_socket
        || current.public_socket != earlier.public_socket
        || current.request != earlier.request
        || current.plan != earlier.plan
    {
        return Err("agent reserve custody identity changed during operation".into());
    }
    Ok(())
}

/// Phase one has no native mutation. The private Host verifies the complete
/// request against its startup selectors before exposing source signing slots.
pub(super) fn plan(
    host: &Path,
    config: &Path,
    operator_socket: &Path,
    public_socket: &Path,
    request_json: &Path,
    directory: &Path,
) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let operator_socket = absolute(operator_socket)?;
    let public_socket = absolute(public_socket)?;
    let directory = absolute(directory)?;
    if operator_socket == public_socket {
        return Err("agent reserve operator and public sockets must differ".into());
    }
    private_socket(&operator_socket)?;
    let source_bytes = bounded(request_json, REQUEST_LIMIT)?;
    let config_bytes = bounded(&config, 65_536)?;
    let host_sha = host_image_sha256(&host)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|error| format!("cannot create agent reserve directory: {error}"))?;
    sync_directory_ancestors(&directory)?;
    create_private(&directory.join("source.json"), &source_bytes)?;
    create_private(&directory.join("config.json"), &config_bytes)?;
    let request_path = directory.join("request.bin");
    source(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new("application-agent-reserve-request"),
            directory.join("source.json").as_os_str(),
            request_path.as_os_str(),
        ],
    )?;
    retain_generated(&request_path)?;
    let request = bounded(&request_path, REQUEST_LIMIT)?;
    let request_view = source_inspect(
        &host,
        &config,
        "application-agent-reserve-request",
        &request_path,
        &directory.join("request-inspected.json"),
    )?;
    if field(&request_view, "type")? != "application-agent-reserve-request-v2"
        || field(&request_view, "canonicalRequestHex")? != hex(&request)
    {
        return Err("Host inspected a different canonical agent reserve request".into());
    }
    let frame = session_invoke(&host, &operator_socket, &config, 58, &request)?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let plan_bytes = expect_reply(&frame, 58)?;
    let plan_path = directory.join("plan.bin");
    create_private(&plan_path, plan_bytes)?;
    let inspection = source_inspect(
        &host,
        &config,
        "application-agent-reserve-plan",
        &plan_path,
        &directory.join("plan-inspected.json"),
    )?;
    if field(&inspection, "type")? != "application-agent-reserve-plan-v2"
        || field(&inspection, "canonicalPlanHex")? != hex(plan_bytes)
        || field(&inspection, "canonicalRequestHex")? != hex(&request)
        || host_image_sha256(&host)? != host_sha
        || bounded(&config, 65_536)? != config_bytes
    {
        return Err("agent reserve Host plan changed exact request or selected image".into());
    }
    retain_json(
        &directory.join("pin.json"),
        &json!({"format":FORMAT,"host":utf8_path(&host)?,"hostSha256":host_sha,
            "config":utf8_path(&directory.join("config.json"))?,
            "configSha256":digest(&config_bytes),
            "operatorSocket":utf8_path(&operator_socket)?,
            "publicSocket":utf8_path(&public_socket)?,
            "requestSha256":digest(&request),"planSha256":digest(plan_bytes)}),
    )?;
    print_json(&inspection)
}

fn signing_key(path: &Path) -> Result<SigningKey> {
    let bytes = private_bytes(path, 32)?;
    let seed: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "agent reserve key must be 32 raw bytes")?;
    Ok(SigningKey::from_bytes(&seed))
}

pub(super) fn approve_slot(slot: &Value, signer: &Value) -> Result<String> {
    if field(slot, "role")? != field(signer, "role")?
        || field(slot, "index")? != field(signer, "index")?
    {
        return Err("agent reserve signing role/index differs from approval".into());
    }
    let signing = slot
        .get("signing")
        .ok_or("reserve slot has no signing header")?;
    if signing.get("decoded").and_then(Value::as_bool) != Some(true)
        || field(signing, "keyId")? != field(signer, "keyId")?
        || field(signing, "keyEpoch")? != field(signer, "keyEpoch")?
        || field(signing, "algorithm")? != "1"
    {
        return Err("agent reserve signing header differs from approved key".into());
    }
    let header = decode_hex(field(slot, "headerHex")?)?;
    if digest(&header) != field(signer, "headerSha256")? {
        return Err("agent reserve exact signing header differs from approval".into());
    }
    let key_path = Path::new(field(signer, "keyPath")?);
    if !key_path.is_absolute() {
        return Err("agent reserve signer path must be absolute".into());
    }
    let key = signing_key(key_path)?;
    if hex(&key.verifying_key().to_bytes()) != field(signer, "publicKey")? {
        return Err("agent reserve signer differs from approved public key".into());
    }
    Ok(hex(&key.sign(&header).to_bytes()))
}

/// A read-only witness for the payer signer. Re-inspect the exact original
/// source plan and at least one retained native confirmation before exposing
/// its context to the later, separately approved paid dispatch.
pub(super) struct PayerAnchor {
    pub host: PathBuf,
    pub config: PathBuf,
    pub operator_socket: PathBuf,
    pub request: Vec<u8>,
    plan_sha256: String,
    pub plan_inspection: Value,
    pub receipt: Value,
}

pub(super) fn payer_pin_still(directory: &Path, anchor: &PayerAnchor) -> Result<()> {
    let directory = absolute(directory)?;
    let current = pinned(&directory)?;
    if current.host != anchor.host
        || current.config != anchor.config
        || current.operator_socket != anchor.operator_socket
        || current.request != anchor.request
        || digest(&current.plan) != anchor.plan_sha256
        || serde_json::from_slice::<Value>(&private_bytes(
            &directory.join("plan-inspected.json"),
            JSON_LIMIT,
        )?)
        .map_err(|error| format!("invalid retained reserve inspection: {error}"))?
            != anchor.plan_inspection
        || serde_json::from_slice::<Value>(&private_bytes(&directory.join("receipt.json"), 4096)?)
            .map_err(|error| format!("invalid retained reserve receipt: {error}"))?
            != anchor.receipt
    {
        return Err("original reserve pin or confirmation changed during payer signing".into());
    }
    Ok(())
}

pub(super) fn payer_anchor(directory: &Path, evidence_dir: &Path) -> Result<PayerAnchor> {
    let directory = absolute(directory)?;
    let (pin, call) = sealed(&directory)?;
    let marker: Value =
        serde_json::from_slice(&private_bytes(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|error| format!("invalid agent reserve submit marker: {error}"))?;
    if field(&marker, "type")? != "minidregg-agent-reserve-submit-attempt-v1"
        || field(&marker, "callSha256")? != digest(&call)
        || field(&marker, "publicSocket")? != utf8_path(&pin.public_socket)?
    {
        return Err("agent reserve submit marker differs from exact call".into());
    }
    let retained: Value = serde_json::from_slice(&private_bytes(
        &directory.join("plan-inspected.json"),
        JSON_LIMIT,
    )?)
    .map_err(|error| format!("invalid retained reserve plan inspection: {error}"))?;
    let fresh = source_inspect(
        &pin.host,
        &pin.config,
        "application-agent-reserve-plan",
        &directory.join("plan.bin"),
        &evidence_dir.join("reserve-plan-inspected.json"),
    )?;
    if retained != fresh
        || field(&fresh, "type")? != "application-agent-reserve-plan-v2"
        || field(&fresh, "canonicalPlanHex")? != hex(&pin.plan)
        || field(&fresh, "canonicalRequestHex")? != hex(&pin.request)
    {
        return Err("original reserve plan or source inspection changed".into());
    }
    let receipt: Value =
        serde_json::from_slice(&private_bytes(&directory.join("receipt.json"), 4096)?)
            .map_err(|error| format!("invalid retained agent reserve receipt: {error}"))?;
    let mut selected: Option<String> = None;
    let mut inspected = 0usize;
    for entry in fs::read_dir(&directory).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        let stem = name.strip_suffix(".outcome.json");
        let Some(stem) = stem else { continue };
        if stem != "submit"
            && !(stem.starts_with("lookup-")
                && stem.len() == 11
                && stem[7..].bytes().all(|byte| byte.is_ascii_digit()))
        {
            continue;
        }
        inspected += 1;
        if inspected > 10_001 {
            return Err("agent reserve outcome evidence count exceeded".into());
        }
        let result: Value = serde_json::from_slice(&private_bytes(&entry.path(), 65_536)?)
            .map_err(|error| format!("invalid retained reserve outcome: {error}"))?;
        if let Ok(confirmed) = exact_receipt(&result) {
            if confirmed != receipt {
                return Err("retained agent reserve confirmations disagree".into());
            }
            selected.get_or_insert_with(|| stem.to_owned());
        }
    }
    let stem = selected.ok_or("no retained native confirmation matches reserve receipt")?;
    let binary_path = directory.join(format!("{stem}.outcome.bin"));
    let binary = private_bytes(&binary_path, transport::HOST_MAX_FRAME)?;
    let operation = if stem == "submit" { 2 } else { 3 };
    let frame = private_bytes(
        &directory.join(format!("{stem}.frame")),
        transport::HOST_MAX_FRAME,
    )?;
    if frame != [vec![operation], binary].concat() {
        return Err("agent reserve outcome differs from retained native frame".into());
    }
    let fresh_outcome = source_inspect(
        &pin.host,
        &pin.config,
        "outcome",
        &binary_path,
        &evidence_dir.join("reserve-confirmation-inspected.json"),
    )?;
    same_pin(&directory, &pin)?;
    if exact_receipt(&fresh_outcome)? != receipt {
        return Err("source-inspected native reserve confirmation changed".into());
    }
    Ok(PayerAnchor {
        host: pin.host,
        config: pin.config,
        operator_socket: pin.operator_socket,
        request: pin.request,
        plan_sha256: digest(&pin.plan),
        plan_inspection: fresh,
        receipt,
    })
}

/// Phase two signs only the exact retained Host plan and never sends op2.
pub(super) fn seal(directory: &Path, approval_json: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let pin = pinned(&directory)?;
    private_socket(&pin.operator_socket)?;
    if directory.join("seal.json").exists() || directory.join("call.bin").exists() {
        return Err("agent reserve plan was already sealed".into());
    }
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid agent reserve approval: {error}"))?;
    let inspected: Value = serde_json::from_slice(&bounded(
        &directory.join("plan-inspected.json"),
        JSON_LIMIT,
    )?)
    .map_err(|error| format!("invalid retained agent reserve plan inspection: {error}"))?;
    let fresh = source_inspect(
        &pin.host,
        &pin.config,
        "application-agent-reserve-plan",
        &directory.join("plan.bin"),
        &directory.join("seal-plan-inspected.json"),
    )?;
    same_pin(&directory, &pin)?;
    if field(&approval, "type")? != APPROVAL
        || field(&approval, "requestSha256")? != digest(&pin.request)
        || field(&approval, "planSha256")? != digest(&pin.plan)
        || approval.get("fixedSelectors") != inspected.get("fixedSelectors")
        || field(&inspected, "canonicalPlanHex")? != hex(&pin.plan)
        || field(&inspected, "canonicalRequestHex")? != hex(&pin.request)
        || fresh != inspected
    {
        return Err("agent reserve approval differs from exact source request or plan".into());
    }
    let slots = inspected
        .get("slots")
        .and_then(Value::as_array)
        .ok_or("agent reserve plan lacks ordered slots")?;
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("agent reserve approval lacks ordered signers")?;
    if slots.is_empty() || slots.len() != signers.len() || slots.len() > 16 {
        return Err("agent reserve signing slot count differs from approval".into());
    }
    let signatures = slots
        .iter()
        .zip(signers)
        .map(|(slot, signer)| approve_slot(slot, signer).map(Value::String))
        .collect::<Result<Vec<_>>>()?;
    create_private(&directory.join("approval.json"), &approval_bytes)?;
    retain_json(
        &directory.join("signatures.json"),
        &Value::Array(signatures),
    )?;
    let signatures_path = directory.join("signatures.bin");
    source(
        &pin.host,
        &pin.config,
        &[
            OsStr::new("signatures"),
            directory.join("signatures.json").as_os_str(),
            signatures_path.as_os_str(),
        ],
    )?;
    retain_generated(&signatures_path)?;
    let signatures_bytes = bounded(&signatures_path, 4096)?;
    let plan_length: u32 = pin
        .plan
        .len()
        .try_into()
        .map_err(|_| "reserve plan too long")?;
    let mut pair = plan_length.to_le_bytes().to_vec();
    pair.extend_from_slice(&pin.plan);
    pair.extend_from_slice(&signatures_bytes);
    let frame = session_invoke(&pin.host, &pin.operator_socket, &pin.config, 59, &pair)?;
    create_private(&directory.join("assembly.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pin)?;
    let call = expect_reply(&frame, 59)?;
    create_private(&directory.join("call.bin"), call)?;
    sync_retained_call(&directory, &directory.join("call.bin"))?;
    retain_json(
        &directory.join("seal.json"),
        &json!({"format":FORMAT,"requestSha256":digest(&pin.request),
            "planSha256":digest(&pin.plan),"approvalSha256":digest(&approval_bytes),
            "callSha256":digest(call)}),
    )?;
    println!("{}", directory.join("call.bin").display());
    Ok(())
}

fn sealed(directory: &Path) -> Result<(Pin, Vec<u8>)> {
    let pin = pinned(directory)?;
    let seal: Value = serde_json::from_slice(&private_bytes(&directory.join("seal.json"), 4096)?)
        .map_err(|error| format!("invalid agent reserve seal: {error}"))?;
    let call = private_bytes(&directory.join("call.bin"), REQUEST_LIMIT)?;
    if field(&seal, "format")? != FORMAT
        || field(&seal, "requestSha256")? != digest(&pin.request)
        || field(&seal, "planSha256")? != digest(&pin.plan)
        || field(&seal, "approvalSha256")?
            != digest(&private_bytes(&directory.join("approval.json"), 65_536)?)
        || field(&seal, "callSha256")? != digest(&call)
        || bounded(&directory.join("assembly.frame"), transport::HOST_MAX_FRAME)?
            != [vec![59], call.clone()].concat()
    {
        return Err("agent reserve exact sealed call differs from retained assembly".into());
    }
    Ok((pin, call))
}

fn outcome(directory: &Path, stem: &str, frame: &[u8], operation: u8, pin: &Pin) -> Result<Value> {
    let bytes = expect_reply(frame, operation)?;
    let binary = directory.join(format!("{stem}.outcome.bin"));
    create_private(&binary, bytes)?;
    sync_directory_ancestors(directory)?;
    source_inspect(
        &pin.host,
        &pin.config,
        "outcome",
        &binary,
        &directory.join(format!("{stem}.outcome.json")),
    )
}

/// Exactly one op2 is possible per sealed directory. Lost replies require op3.
pub(super) fn submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pin, call) = sealed(&directory)?;
    if directory.join("submit-marker.json").exists() {
        return Err("agent reserve submit already attempted; use exact lookup".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({"type":"minidregg-agent-reserve-submit-attempt-v1",
            "callSha256":digest(&call),"publicSocket":utf8_path(&pin.public_socket)?}),
    )?;
    let frame = session_invoke(&pin.host, &pin.public_socket, &pin.config, 2, &call)
        .map_err(|error| format!("agent reserve op2 uncertain; use exact lookup: {error}"))?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pin)?;
    let result = outcome(&directory, "submit", &frame, 2, &pin)?;
    same_pin(&directory, &pin)?;
    let receipt = exact_receipt(&result)?;
    retain_json(&directory.join("receipt.json"), &receipt)?;
    print_json(&result)
}

/// Read-only historical op3 on the exact call. It never resubmits a reserve.
pub(super) fn lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pin, call) = sealed(&directory)?;
    let marker: Value =
        serde_json::from_slice(&private_bytes(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|error| format!("invalid agent reserve submit marker: {error}"))?;
    if field(&marker, "type")? != "minidregg-agent-reserve-submit-attempt-v1"
        || field(&marker, "callSha256")? != digest(&call)
        || field(&marker, "publicSocket")? != utf8_path(&pin.public_socket)?
    {
        return Err("agent reserve submit marker differs from exact call".into());
    }
    let mut index = 0;
    while directory
        .join(format!("lookup-{index:04}.marker.json"))
        .exists()
    {
        index += 1;
        if index >= 10_000 {
            return Err("agent reserve lookup names exhausted".into());
        }
    }
    let stem = format!("lookup-{index:04}");
    retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({"type":"minidregg-agent-reserve-lookup-v1",
            "callSha256":digest(&call),"publicSocket":utf8_path(&pin.public_socket)?}),
    )?;
    let frame = session_invoke(&pin.host, &pin.public_socket, &pin.config, 3, &call)?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pin)?;
    let result = outcome(&directory, &stem, &frame, 3, &pin)?;
    same_pin(&directory, &pin)?;
    let receipt = exact_receipt(&result)?;
    if result.get("confirmation").and_then(Value::as_str) != Some("replayed") {
        return Err("agent reserve lookup did not find historical acceptance".into());
    }
    let anchor_path = directory.join("receipt.json");
    if anchor_path.exists() {
        let prior: Value = serde_json::from_slice(&private_bytes(&anchor_path, 4096)?)
            .map_err(|error| format!("invalid agent reserve receipt: {error}"))?;
        if prior != receipt {
            return Err("agent reserve historical receipt changed".into());
        }
    } else {
        retain_json(&anchor_path, &receipt)?;
    }
    print_json(&result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch() -> PathBuf {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "mini-agent-reserve-{}-{unique}",
            std::process::id()
        ));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn host_written_files_become_durable_owner_private_evidence() {
        let directory = scratch();
        let output = directory.join("source.bin");
        fs::write(&output, b"source-owned").unwrap();
        fs::set_permissions(&output, fs::Permissions::from_mode(0o644)).unwrap();
        retain_generated(&output).unwrap();
        assert_eq!(
            fs::metadata(&output).unwrap().permissions().mode() & 0o777,
            0o600
        );
        assert_eq!(private_bytes(&output, 32).unwrap(), b"source-owned");
        let alias = directory.join("alias.bin");
        std::os::unix::fs::symlink(&output, &alias).unwrap();
        assert!(retain_generated(&alias).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn approval_requires_exact_plan_and_ordered_headers() {
        let source = json!({"type":APPROVAL,"requestSha256":digest(b"request"),
            "planSha256":digest(b"plan"),"fixedSelectors":{"purseTask":"9"}});
        let checked = json!({"fixedSelectors":{"purseTask":"9"},
            "canonicalPlanHex":hex(b"plan"),"canonicalRequestHex":hex(b"request")});
        assert!(source.get("fixedSelectors") == checked.get("fixedSelectors"));
        assert_ne!(source["planSha256"], digest(b"other"));
        let slot = json!({"role":"0","index":"1","headerHex":hex(b"header"),
            "signing":{"decoded":true,"keyId":"2","keyEpoch":"3","algorithm":"1"}});
        let wrong = json!({"role":"0","index":"0","keyId":"2","keyEpoch":"3"});
        assert!(approve_slot(&slot, &wrong).is_err());
    }

    #[test]
    fn confirmed_receipt_requires_all_four_canonical_fields() {
        let good = json!({"type":"confirmed","transactionId":"10","eventId":"20",
            "confirmation":"installed","acceptedCount":"1","imageBoundary":"30"});
        assert_eq!(exact_receipt(&good).unwrap()["reserveIndex"], "0");
        assert_eq!(
            previous_decimal("100000000000000000000000").unwrap(),
            "99999999999999999999999"
        );
        let mut bad = good.clone();
        bad["acceptedCount"] = json!("0");
        assert!(exact_receipt(&bad).is_err());
        bad["acceptedCount"] = json!("01");
        assert!(exact_receipt(&bad).is_err());
    }

    #[test]
    fn lost_op2_reply_keeps_one_shot_marker_and_exact_call() {
        let directory = scratch();
        let config = directory.join("config.json");
        let host = std::env::current_exe().unwrap();
        let operator = directory.join("operator.sock");
        let public = directory.join("absent-public.sock");
        let request = b"request";
        let plan = b"plan";
        let call = b"exact-call";
        let approval = b"approval";
        for (name, value) in [
            ("config.json", b"{}".as_slice()),
            ("request.bin", request.as_slice()),
            ("plan.bin", plan.as_slice()),
            ("approval.json", approval.as_slice()),
            ("call.bin", call.as_slice()),
        ] {
            create_private(&directory.join(name), value).unwrap();
        }
        create_private(
            &directory.join("plan.frame"),
            &[&[58][..], &plan[..]].concat(),
        )
        .unwrap();
        create_private(
            &directory.join("assembly.frame"),
            &[&[59][..], &call[..]].concat(),
        )
        .unwrap();
        retain_json(
            &directory.join("pin.json"),
            &json!({"format":FORMAT,"host":utf8_path(&host).unwrap(),
                "hostSha256":host_image_sha256(&host).unwrap(),
                "config":utf8_path(&config).unwrap(),"configSha256":digest(b"{}"),
                "operatorSocket":utf8_path(&operator).unwrap(),
                "publicSocket":utf8_path(&public).unwrap(),
                "requestSha256":digest(request),"planSha256":digest(plan)}),
        )
        .unwrap();
        retain_json(
            &directory.join("seal.json"),
            &json!({"format":FORMAT,"requestSha256":digest(request),
                "planSha256":digest(plan),"approvalSha256":digest(approval),
                "callSha256":digest(call)}),
        )
        .unwrap();
        assert!(submit(&directory).unwrap_err().contains("uncertain"));
        assert!(submit(&directory)
            .unwrap_err()
            .contains("already attempted"));
        assert_eq!(fs::read(directory.join("call.bin")).unwrap(), call);
        assert!(!directory.join("submit.frame").exists());
        let inspected = json!({"context":{"canonicalHex":"aa"}});
        let receipt = json!({"transactionId":"1","eventId":"2",
            "acceptedCount":"3","imageBoundary":"4","reserveIndex":"2"});
        retain_json(&directory.join("plan-inspected.json"), &inspected).unwrap();
        retain_json(&directory.join("receipt.json"), &receipt).unwrap();
        let anchor = PayerAnchor {
            host,
            config: config.clone(),
            operator_socket: operator,
            request: request.to_vec(),
            plan_sha256: digest(plan),
            plan_inspection: inspected,
            receipt,
        };
        payer_pin_still(&directory, &anchor).unwrap();
        fs::write(&config, b"{\"changed\":true}").unwrap();
        assert!(payer_pin_still(&directory, &anchor).is_err());
        fs::write(&config, b"{}").unwrap();
        fs::write(directory.join("receipt.json"), b"{}\n").unwrap();
        assert!(payer_pin_still(&directory, &anchor).is_err());
        fs::remove_dir_all(directory).unwrap();
    }
}
