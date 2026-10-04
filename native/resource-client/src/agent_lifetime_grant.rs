//! Owner custody for one event27 grant over the private operator broker.
//! An original event22 ticket must already be certified by Mini; this client
//! never supplies one from caller JSON alone.
use super::agent_reserve::{
    approve_slot, bounded, digest, field, private_bytes, private_socket, retain_generated,
    retain_json, source, source_inspect,
};
use super::*;
use std::os::unix::fs::DirBuilderExt;

const REQUEST_LIMIT: usize = transport::HOST_MAX_FRAME - 1;
const JSON_LIMIT: usize = 8 * transport::HOST_MAX_FRAME;

const FORMAT: &str = "minidregg-agent-lifetime-grant-custody-v1";
const APPROVAL: &str = "minidregg-agent-lifetime-grant-approval-v1";
const SUBMIT_MARKER: &str = "minidregg-agent-lifetime-grant-submit-attempt-v1";
const LOOKUP_MARKER: &str = "minidregg-agent-lifetime-grant-lookup-v1";
const REQUEST_TYPE: &str = "application-agent-lifetime-grant-request-v1";
const PLAN_TYPE: &str = "application-agent-lifetime-grant-plan-v1";
const PLAN_OPERATION: u8 = 74;
const ASSEMBLE_OPERATION: u8 = 75;
const SUBMIT_OPERATION: u8 = 72;
const LOOKUP_OPERATION: u8 = 73;

// These names are the source-owned Host author/inspection routes. The exact
// native image and these strings are pinned together by `plan`.
const REQUEST_ROUTE: &str = "application-agent-lifetime-grant-request";
const PLAN_ROUTE: &str = "application-agent-lifetime-grant-plan";

fn expect_reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [255, ..] => Err(format!("grant Host refused op{operation}; frame retained")),
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!("grant op{operation} returned an invalid frame")),
    }
}


fn preceding(value: &str) -> Result<String> {
    if !mini_sdk::decimal::is_canonical_max(value, 80) || value == "0" {
        return Err("grant accepted count cannot select an index".into());
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
    let first = digits
        .iter()
        .position(|digit| *digit != b'0')
        .unwrap_or(digits.len() - 1);
    String::from_utf8(digits[first..].to_vec()).map_err(|error| error.to_string())
}

fn exact_receipt(value: &Value) -> Result<Value> {
    if field(value, "type")? != "confirmed"
        || !matches!(field(value, "confirmation")?, "installed" | "replayed")
    {
        return Err("grant outcome did not confirm accepted history".into());
    }
    let mut receipt = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        let text = field(value, name)?;
        if !mini_sdk::decimal::is_canonical_max(text, 80) {
            return Err(format!("grant receipt has noncanonical {name}"));
        }
        receipt.insert(name.to_owned(), Value::String(text.to_owned()));
    }
    receipt.insert(
        "grantIndex".to_owned(),
        Value::String(preceding(field(value, "acceptedCount")?)?),
    );
    Ok(Value::Object(receipt))
}

struct Pin {
    host: PathBuf,
    config: PathBuf,
    operator_socket: PathBuf,
    request: Vec<u8>,
    plan: Vec<u8>,
}

fn pin(directory: &Path) -> Result<Pin> {
    crate::fsio::ensure_private_dir_durable(directory)?;
    let value: Value = serde_json::from_slice(&private_bytes(&directory.join("pin.json"), 4096)?)
        .map_err(|error| format!("invalid agent lifetime grant pin: {error}"))?;
    if field(&value, "format")? != FORMAT {
        return Err("unsupported agent lifetime grant custody format".into());
    }
    let host = PathBuf::from(field(&value, "host")?);
    let config = PathBuf::from(field(&value, "config")?);
    let operator_socket = PathBuf::from(field(&value, "operatorSocket")?);
    if [host.as_path(), config.as_path(), operator_socket.as_path()]
        .iter()
        .any(|path| !path.is_absolute())
        || host_image_sha256(&host)? != field(&value, "hostSha256")?
        || digest(&bounded(&config, 65_536)?) != field(&value, "configSha256")?
    {
        return Err("agent lifetime grant Host, config or socket identity changed".into());
    }
    let request = private_bytes(&directory.join("request.bin"), REQUEST_LIMIT)?;
    let plan = private_bytes(&directory.join("plan.bin"), REQUEST_LIMIT)?;
    if digest(&request) != field(&value, "requestSha256")?
        || digest(&plan) != field(&value, "planSha256")?
        || bounded(&directory.join("plan.frame"), transport::HOST_MAX_FRAME)?
            != [vec![PLAN_OPERATION], plan.clone()].concat()
    {
        return Err("agent lifetime grant exact request or plan changed".into());
    }
    Ok(Pin {
        host,
        config,
        operator_socket,
        request,
        plan,
    })
}

fn same_pin(directory: &Path, earlier: &Pin) -> Result<()> {
    let current = pin(directory)?;
    if current.host != earlier.host
        || current.config != earlier.config
        || current.operator_socket != earlier.operator_socket
        || current.request != earlier.request
        || current.plan != earlier.plan
    {
        return Err("agent lifetime grant custody identity changed".into());
    }
    Ok(())
}

pub(crate) fn grant_plan(
    host: &Path,
    config: &Path,
    operator_socket: &Path,
    request_json: &Path,
    directory: &Path,
) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let operator_socket = absolute(operator_socket)?;
    let directory = absolute(directory)?;
    private_socket(&operator_socket)?;
    let source_bytes = private_bytes(request_json, REQUEST_LIMIT)?;
    let config_bytes = bounded(&config, 65_536)?;
    let host_sha = host_image_sha256(&host)?;
    crate::fsio::create_private_dir(&directory)?;
    sync_directory_ancestors(&directory)?;
    create_private(&directory.join("source.json"), &source_bytes)?;
    create_private(&directory.join("config.json"), &config_bytes)?;
    let request_path = directory.join("request.bin");
    source(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new(REQUEST_ROUTE),
            directory.join("source.json").as_os_str(),
            request_path.as_os_str(),
        ],
    )?;
    retain_generated(&request_path)?;
    let request = bounded(&request_path, REQUEST_LIMIT)?;
    let request_view = source_inspect(
        &host,
        &config,
        REQUEST_ROUTE,
        &request_path,
        &directory.join("request-inspected.json"),
    )?;
    if field(&request_view, "type")? != REQUEST_TYPE
        || field(&request_view, "canonicalRequestHex")? != hex(&request)
    {
        return Err("Host inspected a different agent lifetime grant request".into());
    }
    let frame = session_invoke(&host, &operator_socket, &config, PLAN_OPERATION, &request)?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let plan_bytes = expect_reply(&frame, PLAN_OPERATION)?;
    let plan_path = directory.join("plan.bin");
    create_private(&plan_path, plan_bytes)?;
    let inspection = source_inspect(
        &host,
        &config,
        PLAN_ROUTE,
        &plan_path,
        &directory.join("plan-inspected.json"),
    )?;
    if field(&inspection, "type")? != PLAN_TYPE
        || field(&inspection, "canonicalPlanHex")? != hex(plan_bytes)
        || inspection.get("request") != Some(&request_view)
        || host_image_sha256(&host)? != host_sha
        || bounded(&config, 65_536)? != config_bytes
    {
        return Err("agent lifetime grant plan changed exact source or selected image".into());
    }
    retain_json(
        &directory.join("pin.json"),
        &json!({
            "format":FORMAT, "host":utf8_path(&host)?, "hostSha256":host_sha,
            "config":utf8_path(&directory.join("config.json"))?,
            "configSha256":digest(&config_bytes),
            "operatorSocket":utf8_path(&operator_socket)?,
            "requestSha256":digest(&request), "planSha256":digest(plan_bytes),
        }),
    )?;
    print_json(&inspection)
}

pub(crate) fn grant_seal(directory: &Path, approval_json: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let pinned = pin(&directory)?;
    private_socket(&pinned.operator_socket)?;
    if directory.join("seal.json").exists() || directory.join("call.bin").exists() {
        return Err("agent lifetime grant plan was already sealed".into());
    }
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid agent lifetime grant approval: {error}"))?;
    let retained: Value = serde_json::from_slice(&private_bytes(
        &directory.join("plan-inspected.json"),
        JSON_LIMIT,
    )?)
    .map_err(|error| format!("invalid retained agent lifetime grant plan: {error}"))?;
    let fresh = source_inspect(
        &pinned.host,
        &pinned.config,
        PLAN_ROUTE,
        &directory.join("plan.bin"),
        &directory.join("seal-plan-inspected.json"),
    )?;
    same_pin(&directory, &pinned)?;
    if field(&approval, "type")? != APPROVAL
        || field(&approval, "requestSha256")? != digest(&pinned.request)
        || field(&approval, "planSha256")? != digest(&pinned.plan)
        || approval.get("request") != retained.get("request")
        || approval.get("birthBoundary") != retained.get("birthBoundary")
        || approval.get("finalizedDraftHex") != retained.get("finalizedDraftHex")
        || field(&retained, "canonicalPlanHex")? != hex(&pinned.plan)
        || retained.get("request")
            != Some(
                &serde_json::from_slice::<Value>(&private_bytes(
                    &directory.join("request-inspected.json"),
                    JSON_LIMIT,
                )?)
                .map_err(|error| format!("invalid retained grant request: {error}"))?,
            )
        || fresh != retained
    {
        return Err("agent lifetime grant approval differs from exact source plan".into());
    }
    let birth_slots = retained
        .get("birthSlots")
        .and_then(Value::as_array)
        .ok_or("agent lifetime grant plan lacks ordered birth slots")?;
    let app_slot = retained
        .get("appSlot")
        .ok_or("agent lifetime grant plan lacks app signer")?;
    crate::client_consent::operator_plan(&pinned.host, &pinned.config, PLAN_OPERATION,
        &pinned.request, &pinned.plan)?;
    let slots = birth_slots
        .iter()
        .chain(std::iter::once(app_slot))
        .collect::<Vec<_>>();
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("agent lifetime grant approval lacks ordered signers")?;
    if birth_slots.is_empty() || slots.len() != signers.len() || slots.len() > 16 {
        return Err("agent lifetime grant signing slot count differs from approval".into());
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
        &pinned.host,
        &pinned.config,
        &[
            OsStr::new("signatures"),
            directory.join("signatures.json").as_os_str(),
            signatures_path.as_os_str(),
        ],
    )?;
    retain_generated(&signatures_path)?;
    let signatures_bytes = bounded(&signatures_path, 4096)?;
    let plan_length: u32 = pinned
        .plan
        .len()
        .try_into()
        .map_err(|_| "agent lifetime grant plan too long")?;
    let mut pair = plan_length.to_le_bytes().to_vec();
    pair.extend_from_slice(&pinned.plan);
    pair.extend_from_slice(&signatures_bytes);
    let frame = session_invoke(
        &pinned.host,
        &pinned.operator_socket,
        &pinned.config,
        ASSEMBLE_OPERATION,
        &pair,
    )?;
    create_private(&directory.join("assembly.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pinned)?;
    let call = expect_reply(&frame, ASSEMBLE_OPERATION)?;
    create_private(&directory.join("call.bin"), call)?;
    sync_retained_call(&directory, &directory.join("call.bin"))?;
    retain_json(
        &directory.join("seal.json"),
        &json!({
            "format":FORMAT, "requestSha256":digest(&pinned.request),
            "planSha256":digest(&pinned.plan), "approvalSha256":digest(&approval_bytes),
            "callSha256":digest(call),
        }),
    )?;
    println!("{}", directory.join("call.bin").display());
    Ok(())
}

fn sealed(directory: &Path) -> Result<(Pin, Vec<u8>)> {
    let pinned = pin(directory)?;
    let seal: Value = serde_json::from_slice(&private_bytes(&directory.join("seal.json"), 4096)?)
        .map_err(|error| format!("invalid agent lifetime grant seal: {error}"))?;
    let call = private_bytes(&directory.join("call.bin"), REQUEST_LIMIT)?;
    if field(&seal, "format")? != FORMAT
        || field(&seal, "requestSha256")? != digest(&pinned.request)
        || field(&seal, "planSha256")? != digest(&pinned.plan)
        || field(&seal, "approvalSha256")?
            != digest(&private_bytes(&directory.join("approval.json"), 65_536)?)
        || field(&seal, "callSha256")? != digest(&call)
        || bounded(&directory.join("assembly.frame"), transport::HOST_MAX_FRAME)?
            != [vec![ASSEMBLE_OPERATION], call.clone()].concat()
    {
        return Err("agent lifetime grant exact sealed call differs from assembly".into());
    }
    Ok((pinned, call))
}

fn outcome(
    directory: &Path,
    stem: &str,
    frame: &[u8],
    operation: u8,
    pinned: &Pin,
) -> Result<Value> {
    let bytes = expect_reply(frame, operation)?;
    let binary = directory.join(format!("{stem}.outcome.bin"));
    create_private(&binary, bytes)?;
    sync_directory_ancestors(directory)?;
    source_inspect(
        &pinned.host,
        &pinned.config,
        "outcome",
        &binary,
        &directory.join(format!("{stem}.outcome.json")),
    )
}

fn send_once<F>(directory: &Path, call: &[u8], operator_socket: &Path, send: F) -> Result<Vec<u8>>
where
    F: FnOnce() -> Result<Vec<u8>>,
{
    if directory.join("submit-marker.json").exists() {
        return Err("agent lifetime grant submit already attempted; use exact lookup".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({
            "type":SUBMIT_MARKER, "callSha256":digest(call),
            "operatorSocket":utf8_path(operator_socket)?,
        }),
    )?;
    send()
}

pub(crate) fn grant_submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, call) = sealed(&directory)?;
    private_socket(&pinned.operator_socket)?;
    let frame = send_once(&directory, &call, &pinned.operator_socket, || {
        session_invoke(
            &pinned.host,
            &pinned.operator_socket,
            &pinned.config,
            SUBMIT_OPERATION,
            &call,
        )
        .map_err(|error| format!("agent lifetime grant op72 uncertain; use exact lookup: {error}"))
    })?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pinned)?;
    let result = outcome(&directory, "submit", &frame, SUBMIT_OPERATION, &pinned)?;
    same_pin(&directory, &pinned)?;
    let receipt = exact_receipt(&result)?;
    retain_json(&directory.join("receipt.json"), &receipt)?;
    print_json(&result)
}

fn lookup_once<F>(
    directory: &Path,
    call: &[u8],
    operator_socket: &Path,
    lookup: F,
) -> Result<(String, Vec<u8>)>
where
    F: FnOnce() -> Result<Vec<u8>>,
{
    let marker: Value =
        serde_json::from_slice(&private_bytes(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|error| format!("invalid agent lifetime grant submit marker: {error}"))?;
    if field(&marker, "type")? != SUBMIT_MARKER
        || field(&marker, "callSha256")? != digest(call)
        || field(&marker, "operatorSocket")? != utf8_path(operator_socket)?
    {
        return Err("agent lifetime grant submit marker differs from exact call".into());
    }
    let mut index = 0;
    while directory
        .join(format!("lookup-{index:04}.marker.json"))
        .exists()
    {
        index += 1;
        if index >= 10_000 {
            return Err("agent lifetime grant lookup names exhausted".into());
        }
    }
    let stem = format!("lookup-{index:04}");
    retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({
            "type":LOOKUP_MARKER, "callSha256":digest(call),
            "operatorSocket":utf8_path(operator_socket)?,
        }),
    )?;
    Ok((stem, lookup()?))
}

pub(crate) fn grant_lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, call) = sealed(&directory)?;
    private_socket(&pinned.operator_socket)?;
    let (stem, frame) = lookup_once(&directory, &call, &pinned.operator_socket, || {
        session_invoke(
            &pinned.host,
            &pinned.operator_socket,
            &pinned.config,
            LOOKUP_OPERATION,
            &call,
        )
    })?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pinned)?;
    let result = outcome(&directory, &stem, &frame, LOOKUP_OPERATION, &pinned)?;
    same_pin(&directory, &pinned)?;
    let receipt = exact_receipt(&result)?;
    if result.get("confirmation").and_then(Value::as_str) != Some("replayed") {
        return Err("agent lifetime grant lookup did not confirm historical acceptance".into());
    }
    let anchor = directory.join("receipt.json");
    if anchor.exists() {
        let previous: Value = serde_json::from_slice(&private_bytes(&anchor, 4096)?)
            .map_err(|error| format!("invalid agent lifetime grant receipt: {error}"))?;
        if previous != receipt {
            return Err("agent lifetime grant historical receipt changed".into());
        }
    } else {
        retain_json(&anchor, &receipt)?;
    }
    print_json(&result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn lost_submit_reply_reenters_only_exact_read_only_lookup() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-lifetime-grant-{}-{unique}",
            std::process::id()
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let call = b"exact-canonical-call";
        let socket = Path::new("/private/recipient.sock");
        let submits = Cell::new(0);
        let first = send_once(&directory, call, socket, || {
            submits.set(submits.get() + 1);
            Err("lost submit reply".into())
        });
        assert!(first.is_err());
        assert_eq!(submits.get(), 1);
        let second = send_once(&directory, call, socket, || {
            submits.set(submits.get() + 1);
            Ok(vec![SUBMIT_OPERATION, 1])
        });
        assert!(second.is_err());
        assert_eq!(submits.get(), 1);
        let marker: Value = serde_json::from_slice(
            &private_bytes(&directory.join("submit-marker.json"), 4096).unwrap(),
        )
        .unwrap();
        assert_eq!(field(&marker, "callSha256").unwrap(), digest(call));
        let lookups = Cell::new(0);
        let first_lookup = lookup_once(&directory, call, socket, || {
            lookups.set(lookups.get() + 1);
            Err("lost lookup reply".into())
        });
        assert!(first_lookup.is_err());
        assert_eq!(lookups.get(), 1);
        let (name, frame) = lookup_once(&directory, call, socket, || {
            lookups.set(lookups.get() + 1);
            Ok(vec![LOOKUP_OPERATION, 1])
        })
        .unwrap();
        assert_eq!(name, "lookup-0001");
        assert_eq!(frame, vec![LOOKUP_OPERATION, 1]);
        assert_eq!(lookups.get(), 2);
        assert_eq!(submits.get(), 1);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn grant_slot_uses_exact_header_without_canonical_alias() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "mini-agent-lifetime-slot-{}-{unique}",
            std::process::id()
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let key_path = directory.join("key.bin");
        let seed = [7_u8; 32];
        create_private(&key_path, &seed).unwrap();
        let key = SigningKey::from_bytes(&seed);
        let header = b"exact source signing header";
        let slot = json!({"role":"2","index":"0","headerHex":hex(header),
            "signing":{"decoded":true,"keyId":"9","keyEpoch":"1",
                "algorithm":"1","authorityRoot":"12", "domainHex":"ab",
                "messageHex":"cd", "nullifier":"13"}});
        let signer = json!({"role":"2","index":"0","keyId":"9","keyEpoch":"1",
            "headerSha256":digest(header),"keyPath":utf8_path(&key_path).unwrap(),
            "publicKey":hex(&key.verifying_key().to_bytes())});
        assert_eq!(
            approve_slot(&slot, &signer).unwrap(),
            hex(&key.sign(header).to_bytes())
        );
        assert!(slot["signing"].get("canonical").is_none());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn grant_receipt_requires_four_canonical_fields() {
        let good = json!({"type":"confirmed","confirmation":"installed",
            "transactionId":"10","eventId":"20","acceptedCount":"31",
            "worldRoot":"40"});
        assert_eq!(exact_receipt(&good).unwrap()["grantIndex"], "30");
        let mut wrong = good.clone();
        wrong["acceptedCount"] = json!("031");
        assert!(exact_receipt(&wrong).is_err());
        wrong = good;
        wrong["eventId"] = Value::Null;
        assert!(exact_receipt(&wrong).is_err());
    }
}
