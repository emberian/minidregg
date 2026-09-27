//! Distinct custody for the event27-backed lifetime reserve. The v2 attempt
//! format and its op58/59 call remain historical and cannot be reinterpreted.
use super::*;

const FORMAT: &str = "minidregg-agent-lifetime-reserve-custody-v1";
const APPROVAL: &str = "minidregg-agent-lifetime-reserve-approval-v1";
const SUBMIT_MARKER: &str = "minidregg-agent-lifetime-reserve-submit-attempt-v1";
const LOOKUP_MARKER: &str = "minidregg-agent-lifetime-reserve-lookup-v1";
const REQUEST_TYPE: &str = "application-agent-lifetime-author-request-v3";
const PLAN_TYPE: &str = "application-agent-lifetime-reserve-plan-v3";
const PLAN_OPERATION: u8 = 80;
const ASSEMBLE_OPERATION: u8 = 81;

// These names are the source-owned Host author/inspection routes. The exact
// native image and these strings are pinned together by `plan`.
const REQUEST_ROUTE: &str = "application-agent-lifetime-reserve-request";
const PLAN_ROUTE: &str = "application-agent-lifetime-reserve-plan";

struct Pin {
    host: PathBuf,
    config: PathBuf,
    operator_socket: PathBuf,
    public_socket: PathBuf,
    request: Vec<u8>,
    plan: Vec<u8>,
}

fn pin(directory: &Path) -> Result<Pin> {
    drain::private_dir(directory)?;
    let value: Value = serde_json::from_slice(&private_bytes(&directory.join("pin.json"), 4096)?)
        .map_err(|error| format!("invalid lifetime reserve pin: {error}"))?;
    if field(&value, "format")? != FORMAT {
        return Err("unsupported lifetime reserve custody format".into());
    }
    let host = PathBuf::from(field(&value, "host")?);
    let config = PathBuf::from(field(&value, "config")?);
    let operator_socket = PathBuf::from(field(&value, "operatorSocket")?);
    let public_socket = PathBuf::from(field(&value, "publicSocket")?);
    if [
        host.as_path(),
        config.as_path(),
        operator_socket.as_path(),
        public_socket.as_path(),
    ]
    .iter()
    .any(|path| !path.is_absolute())
        || operator_socket == public_socket
        || host_image_sha256(&host)? != field(&value, "hostSha256")?
        || digest(&bounded(&config, 65_536)?) != field(&value, "configSha256")?
    {
        return Err("lifetime reserve Host, config or socket identity changed".into());
    }
    let request = private_bytes(&directory.join("request.bin"), REQUEST_LIMIT)?;
    let plan = private_bytes(&directory.join("plan.bin"), REQUEST_LIMIT)?;
    if digest(&request) != field(&value, "requestSha256")?
        || digest(&plan) != field(&value, "planSha256")?
        || bounded(&directory.join("plan.frame"), transport::HOST_MAX_FRAME)?
            != [vec![PLAN_OPERATION], plan.clone()].concat()
    {
        return Err("lifetime reserve exact request or plan changed".into());
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
    let current = pin(directory)?;
    if current.host != earlier.host
        || current.config != earlier.config
        || current.operator_socket != earlier.operator_socket
        || current.public_socket != earlier.public_socket
        || current.request != earlier.request
        || current.plan != earlier.plan
    {
        return Err("lifetime reserve custody identity changed".into());
    }
    Ok(())
}

pub(crate) fn lifetime_plan(
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
        return Err("lifetime reserve operator and public sockets must differ".into());
    }
    private_socket(&operator_socket)?;
    let source_bytes = private_bytes(request_json, REQUEST_LIMIT)?;
    let config_bytes = bounded(&config, 65_536)?;
    let host_sha = host_image_sha256(&host)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|error| format!("cannot create lifetime reserve directory: {error}"))?;
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
        return Err("Host inspected a different lifetime reserve request".into());
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
        || field(&inspection, "canonicalRequestHex")? != hex(&request)
        || inspection.get("fixedSelectors") != request_view.get("fixedSelectors")
        || inspection.get("canonicalHttpHex") != request_view.get("canonicalHttpHex")
        || host_image_sha256(&host)? != host_sha
        || bounded(&config, 65_536)? != config_bytes
    {
        return Err("lifetime reserve plan changed exact source or selected image".into());
    }
    retain_json(
        &directory.join("pin.json"),
        &json!({
            "format":FORMAT, "host":utf8_path(&host)?, "hostSha256":host_sha,
            "config":utf8_path(&directory.join("config.json"))?,
            "configSha256":digest(&config_bytes),
            "operatorSocket":utf8_path(&operator_socket)?,
            "publicSocket":utf8_path(&public_socket)?,
            "requestSha256":digest(&request), "planSha256":digest(plan_bytes),
        }),
    )?;
    print_json(&inspection)
}

pub(crate) fn lifetime_seal(directory: &Path, approval_json: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let pinned = pin(&directory)?;
    private_socket(&pinned.operator_socket)?;
    if directory.join("seal.json").exists() || directory.join("call.bin").exists() {
        return Err("lifetime reserve plan was already sealed".into());
    }
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid lifetime reserve approval: {error}"))?;
    let retained: Value = serde_json::from_slice(&private_bytes(
        &directory.join("plan-inspected.json"),
        JSON_LIMIT,
    )?)
    .map_err(|error| format!("invalid retained lifetime reserve plan: {error}"))?;
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
        || approval.get("fixedSelectors") != retained.get("fixedSelectors")
        || approval.get("context") != retained.get("context")
        || approval.get("bindings") != retained.get("bindings")
        || approval.get("canonicalHttpHex") != retained.get("canonicalHttpHex")
        || field(&retained, "canonicalPlanHex")? != hex(&pinned.plan)
        || field(&retained, "canonicalRequestHex")? != hex(&pinned.request)
        || fresh != retained
    {
        return Err("lifetime reserve approval differs from exact source plan".into());
    }
    let slots = retained
        .get("slots")
        .and_then(Value::as_array)
        .ok_or("lifetime reserve plan lacks ordered slots")?;
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("lifetime reserve approval lacks ordered signers")?;
    if slots.is_empty() || slots.len() != signers.len() || slots.len() > 16 {
        return Err("lifetime reserve signing slot count differs from approval".into());
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
        .map_err(|_| "lifetime reserve plan too long")?;
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
        .map_err(|error| format!("invalid lifetime reserve seal: {error}"))?;
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
        return Err("lifetime reserve exact sealed call differs from assembly".into());
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

fn send_once<F>(directory: &Path, call: &[u8], public_socket: &Path, send: F) -> Result<Vec<u8>>
where
    F: FnOnce() -> Result<Vec<u8>>,
{
    if directory.join("submit-marker.json").exists() {
        return Err("lifetime reserve submit already attempted; use exact lookup".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({
            "type":SUBMIT_MARKER, "callSha256":digest(call),
            "publicSocket":utf8_path(public_socket)?,
        }),
    )?;
    send()
}

pub(crate) fn lifetime_submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, call) = sealed(&directory)?;
    let frame = send_once(&directory, &call, &pinned.public_socket, || {
        session_invoke(
            &pinned.host,
            &pinned.public_socket,
            &pinned.config,
            2,
            &call,
        )
        .map_err(|error| format!("lifetime reserve op2 uncertain; use exact lookup: {error}"))
    })?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pinned)?;
    let result = outcome(&directory, "submit", &frame, 2, &pinned)?;
    same_pin(&directory, &pinned)?;
    let receipt = exact_receipt(&result)?;
    retain_json(&directory.join("receipt.json"), &receipt)?;
    print_json(&result)
}

fn lookup_once<F>(
    directory: &Path,
    call: &[u8],
    public_socket: &Path,
    lookup: F,
) -> Result<(String, Vec<u8>)>
where
    F: FnOnce() -> Result<Vec<u8>>,
{
    let marker: Value =
        serde_json::from_slice(&private_bytes(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|error| format!("invalid lifetime reserve submit marker: {error}"))?;
    if field(&marker, "type")? != SUBMIT_MARKER
        || field(&marker, "callSha256")? != digest(call)
        || field(&marker, "publicSocket")? != utf8_path(public_socket)?
    {
        return Err("lifetime reserve submit marker differs from exact call".into());
    }
    let mut index = 0;
    while directory
        .join(format!("lookup-{index:04}.marker.json"))
        .exists()
    {
        index += 1;
        if index >= 10_000 {
            return Err("lifetime reserve lookup names exhausted".into());
        }
    }
    let stem = format!("lookup-{index:04}");
    retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({
            "type":LOOKUP_MARKER, "callSha256":digest(call),
            "publicSocket":utf8_path(public_socket)?,
        }),
    )?;
    Ok((stem, lookup()?))
}

pub(crate) fn lifetime_lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, call) = sealed(&directory)?;
    let (stem, frame) = lookup_once(&directory, &call, &pinned.public_socket, || {
        session_invoke(
            &pinned.host,
            &pinned.public_socket,
            &pinned.config,
            3,
            &call,
        )
    })?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pinned)?;
    let result = outcome(&directory, &stem, &frame, 3, &pinned)?;
    same_pin(&directory, &pinned)?;
    let receipt = exact_receipt(&result)?;
    if result.get("confirmation").and_then(Value::as_str) != Some("replayed") {
        return Err("lifetime reserve lookup did not confirm historical acceptance".into());
    }
    let anchor = directory.join("receipt.json");
    if anchor.exists() {
        let previous: Value = serde_json::from_slice(&private_bytes(&anchor, 4096)?)
            .map_err(|error| format!("invalid lifetime reserve receipt: {error}"))?;
        if previous != receipt {
            return Err("lifetime reserve historical receipt changed".into());
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
            "mini-agent-lifetime-reserve-{}-{unique}",
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
            Ok(vec![2, 1])
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
            Ok(vec![3, 1])
        })
        .unwrap();
        assert_eq!(name, "lookup-0001");
        assert_eq!(frame, vec![3, 1]);
        assert_eq!(lookups.get(), 2);
        assert_eq!(submits.get(), 1);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn lifetime_slot_uses_exact_header_without_canonical_alias() {
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
}
