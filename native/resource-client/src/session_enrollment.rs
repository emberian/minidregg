//! Private custody for a source-authored event28 session enrollment.
//! Mini owns the Request, Plan, signature, and Ingress codecs. This client
//! retains exact bytes and never repeats an uncertain native submit.
use super::agent_reserve::{
    approve_slot, bounded, digest, field, private_bytes, private_socket, retain_generated,
    retain_json, source, source_inspect,
};
use super::*;
use std::os::unix::fs::DirBuilderExt;

const LIMIT: usize = transport::HOST_MAX_FRAME - 1;
const JSON_LIMIT: usize = 8 * transport::HOST_MAX_FRAME;
const FORMAT: &str = "minidregg-session-enrollment-custody-v1";
const APPROVAL: &str = "minidregg-session-enrollment-approval-v1";
const REQUEST_TYPE: &str = "application-session-enrollment-request-v1";
const PLAN_TYPE: &str = "application-session-enrollment-plan-v1";
const INGRESS_TYPE: &str = "application-session-enrollment-ingress-v1";
const REQUEST_ROUTE: &str = "application-session-enrollment-request";
const PLAN_ROUTE: &str = "application-session-enrollment-plan";
const INGRESS_ROUTE: &str = "application-session-enrollment-ingress";
const PLAN_OP: u8 = 82;
const ASSEMBLE_OP: u8 = 83;
const SUBMIT_OP: u8 = 84;
const LOOKUP_OP: u8 = 85;

fn reply(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [255, ..] => Err(format!(
            "enrollment Host refused op{operation}; frame retained"
        )),
        [actual, body @ ..] if *actual == operation && !body.is_empty() => Ok(body),
        _ => Err(format!(
            "enrollment op{operation} returned an invalid frame"
        )),
    }
}

fn inspected(directory: &Path, name: &str) -> Result<Value> {
    serde_json::from_slice(&private_bytes(&directory.join(name), JSON_LIMIT)?)
        .map_err(|error| format!("invalid retained enrollment inspection: {error}"))
}

fn exact_plan(view: &Value, request_view: &Value, request: &[u8], plan: &[u8]) -> Result<()> {
    if field(view, "type")? != PLAN_TYPE
        || field(view, "canonicalPlanHex")? != hex(plan)
        || field(view, "canonicalRequestHex")? != hex(request)
        || view.get("request") != Some(request_view)
        || view.get("issueReceipt").is_none()
        || view
            .get("slots")
            .and_then(Value::as_array)
            .is_none_or(|slots| slots.len() < 4 || slots.len() > 16)
    {
        return Err("enrollment Plan differs from exact source Request or selected issue".into());
    }
    Ok(())
}

struct Pin {
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    request: Vec<u8>,
    plan: Vec<u8>,
}

fn pin(directory: &Path) -> Result<Pin> {
    drain::private_dir(directory)?;
    let value = inspected(directory, "pin.json")?;
    if field(&value, "format")? != FORMAT {
        return Err("unsupported enrollment custody pin".into());
    }
    let host = PathBuf::from(field(&value, "host")?);
    let config = PathBuf::from(field(&value, "config")?);
    let socket = PathBuf::from(field(&value, "operatorSocket")?);
    if [host.as_path(), config.as_path(), socket.as_path()]
        .iter()
        .any(|path| !path.is_absolute())
        || host_image_sha256(&host)? != field(&value, "hostSha256")?
        || digest(&bounded(&config, 65_536)?) != field(&value, "configSha256")?
    {
        return Err("enrollment Host, config, or operator socket pin changed".into());
    }
    let request = private_bytes(&directory.join("request.bin"), LIMIT)?;
    let plan = private_bytes(&directory.join("plan.bin"), LIMIT)?;
    if digest(&request) != field(&value, "requestSha256")?
        || digest(&plan) != field(&value, "planSha256")?
        || bounded(&directory.join("plan.frame"), transport::HOST_MAX_FRAME)?
            != [vec![PLAN_OP], plan.clone()].concat()
    {
        return Err("enrollment retained Request or Plan changed".into());
    }
    Ok(Pin {
        host,
        config,
        socket,
        request,
        plan,
    })
}

fn same_pin(directory: &Path, earlier: &Pin) -> Result<()> {
    let current = pin(directory)?;
    if current.host != earlier.host
        || current.config != earlier.config
        || current.socket != earlier.socket
        || current.request != earlier.request
        || current.plan != earlier.plan
    {
        return Err("enrollment custody changed during operation".into());
    }
    Ok(())
}

pub(super) fn plan(
    host: &Path,
    config: &Path,
    socket: &Path,
    request_json: &Path,
    directory: &Path,
) -> Result<()> {
    let host = absolute(host)?;
    let config = absolute(config)?;
    let socket = absolute(socket)?;
    let directory = absolute(directory)?;
    private_socket(&socket)?;
    let source_bytes = private_bytes(request_json, LIMIT)?;
    let config_bytes = bounded(&config, 65_536)?;
    let host_sha = host_image_sha256(&host)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|error| format!("cannot create enrollment directory: {error}"))?;
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
    let request = bounded(&request_path, LIMIT)?;
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
        return Err("enrollment source Request inspection differs".into());
    }
    let frame = session_invoke(&host, &socket, &config, PLAN_OP, &request)?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let plan_bytes = reply(&frame, PLAN_OP)?;
    let plan_path = directory.join("plan.bin");
    create_private(&plan_path, plan_bytes)?;
    let plan_view = source_inspect(
        &host,
        &config,
        PLAN_ROUTE,
        &plan_path,
        &directory.join("plan-inspected.json"),
    )?;
    exact_plan(&plan_view, &request_view, &request, plan_bytes)?;
    if host_image_sha256(&host)? != host_sha
        || bounded(&config, 65_536)? != config_bytes
        || private_bytes(request_json, LIMIT)? != source_bytes
    {
        return Err("enrollment Host, config, or source changed during plan".into());
    }
    retain_json(
        &directory.join("pin.json"),
        &json!({"format":FORMAT,"host":utf8_path(&host)?,"hostSha256":host_sha,
            "config":utf8_path(&directory.join("config.json"))?,
            "configSha256":digest(&config_bytes),
            "operatorSocket":utf8_path(&socket)?,
            "requestSha256":digest(&request),"planSha256":digest(plan_bytes)}),
    )?;
    print_json(&plan_view)
}

fn exact_ingress(view: &Value, plan_view: &Value, request: &[u8], ingress: &[u8]) -> Result<()> {
    if field(view, "type")? != INGRESS_TYPE
        || field(view, "canonicalIngressHex")? != hex(ingress)
        || field(view, "canonicalRequestHex")? != hex(request)
    {
        return Err("enrollment Ingress differs from exact source bytes".into());
    }
    for name in [
        "enrollmentHex",
        "issueReceiptHex",
        "issueReceipt",
        "appRoot",
        "manifestRoot",
        "ticketRoot",
    ] {
        if view.get(name).is_none() || view.get(name) != plan_view.get(name) {
            return Err(format!("enrollment Ingress differs from Plan {name}"));
        }
    }
    Ok(())
}

pub(super) fn seal(directory: &Path, approval_json: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let pinned = pin(&directory)?;
    private_socket(&pinned.socket)?;
    if directory.join("seal.json").exists() || directory.join("ingress.bin").exists() {
        return Err("enrollment plan already sealed".into());
    }
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid enrollment approval: {error}"))?;
    let retained = inspected(&directory, "plan-inspected.json")?;
    let request_view = inspected(&directory, "request-inspected.json")?;
    exact_plan(&retained, &request_view, &pinned.request, &pinned.plan)?;
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
        || field(&approval, "planInspectionSha256")?
            != digest(&private_bytes(
                &directory.join("plan-inspected.json"),
                JSON_LIMIT,
            )?)
        || fresh != retained
    {
        return Err("enrollment approval differs from exact source Plan".into());
    }
    let slots = retained
        .get("slots")
        .and_then(Value::as_array)
        .ok_or("enrollment Plan lacks ordered signing slots")?;
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("enrollment approval lacks ordered signers")?;
    if slots.len() < 4 || slots.len() > 16 || slots.len() != signers.len() {
        return Err("enrollment signer count differs from source slots".into());
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
    let length: u32 = pinned
        .plan
        .len()
        .try_into()
        .map_err(|_| "enrollment Plan exceeds pair frame")?;
    let mut pair = length.to_le_bytes().to_vec();
    pair.extend_from_slice(&pinned.plan);
    pair.extend_from_slice(&signatures_bytes);
    let frame = session_invoke(
        &pinned.host,
        &pinned.socket,
        &pinned.config,
        ASSEMBLE_OP,
        &pair,
    )?;
    create_private(&directory.join("assembly.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_pin(&directory, &pinned)?;
    let ingress = reply(&frame, ASSEMBLE_OP)?;
    create_private(&directory.join("ingress.bin"), ingress)?;
    sync_retained_call(&directory, &directory.join("ingress.bin"))?;
    let inspection = source_inspect(
        &pinned.host,
        &pinned.config,
        INGRESS_ROUTE,
        &directory.join("ingress.bin"),
        &directory.join("ingress-inspected.json"),
    )?;
    exact_ingress(&inspection, &retained, &pinned.request, ingress)?;
    retain_json(
        &directory.join("seal.json"),
        &json!({"format":FORMAT,"requestSha256":digest(&pinned.request),
            "planSha256":digest(&pinned.plan),"approvalSha256":digest(&approval_bytes),
            "ingressSha256":digest(ingress)}),
    )?;
    print_json(&inspection)
}

fn sealed(directory: &Path) -> Result<(Pin, Vec<u8>)> {
    let pinned = pin(directory)?;
    let seal = inspected(directory, "seal.json")?;
    let approval = inspected(directory, "approval.json")?;
    let ingress = private_bytes(&directory.join("ingress.bin"), LIMIT)?;
    if field(&seal, "format")? != FORMAT
        || field(&seal, "requestSha256")? != digest(&pinned.request)
        || field(&seal, "planSha256")? != digest(&pinned.plan)
        || field(&seal, "approvalSha256")?
            != digest(&private_bytes(&directory.join("approval.json"), 65_536)?)
        || field(&seal, "ingressSha256")? != digest(&ingress)
        || bounded(&directory.join("assembly.frame"), transport::HOST_MAX_FRAME)?
            != [vec![ASSEMBLE_OP], ingress.clone()].concat()
    {
        return Err("enrollment sealed Ingress differs from source assembly".into());
    }
    let plan_view = inspected(directory, "plan-inspected.json")?;
    if field(&approval, "type")? != APPROVAL
        || field(&approval, "requestSha256")? != digest(&pinned.request)
        || field(&approval, "planSha256")? != digest(&pinned.plan)
        || field(&approval, "planInspectionSha256")?
            != digest(&private_bytes(
                &directory.join("plan-inspected.json"),
                JSON_LIMIT,
            )?)
    {
        return Err("enrollment approved Plan changed after seal".into());
    }
    exact_plan(
        &plan_view,
        &inspected(directory, "request-inspected.json")?,
        &pinned.request,
        &pinned.plan,
    )?;
    let ingress_view = inspected(directory, "ingress-inspected.json")?;
    exact_ingress(&ingress_view, &plan_view, &pinned.request, &ingress)?;
    Ok((pinned, ingress))
}

fn same_seal(directory: &Path, pinned: &Pin, ingress: &[u8]) -> Result<()> {
    let (current, bytes) = sealed(directory)?;
    if current.host != pinned.host
        || current.config != pinned.config
        || current.socket != pinned.socket
        || current.request != pinned.request
        || current.plan != pinned.plan
        || bytes != ingress
    {
        return Err("enrollment sealed custody changed during operation".into());
    }
    Ok(())
}

fn outcome(directory: &Path, stem: &str, frame: &[u8], operation: u8, pin: &Pin) -> Result<Value> {
    let bytes = reply(frame, operation)?;
    let output = directory.join(format!("{stem}.outcome.bin"));
    create_private(&output, bytes)?;
    sync_directory_ancestors(directory)?;
    source_inspect(
        &pin.host,
        &pin.config,
        "outcome",
        &output,
        &directory.join(format!("{stem}.outcome.json")),
    )
}

fn receipt(value: &Value) -> Result<Value> {
    if field(value, "type")? != "confirmed"
        || !matches!(field(value, "confirmation")?, "installed" | "replayed" | "recoveredAfterUncertainResponse")
    {
        return Err("enrollment outcome did not confirm native acceptance".into());
    }
    let mut fields = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        let value = field(value, name)?;
        if !mini_sdk::decimal::is_canonical_max(value, 80) || (name == "acceptedCount" && value == "0") {
            return Err(format!("enrollment receipt has invalid {name}"));
        }
        fields.insert(name.to_owned(), Value::String(value.to_owned()));
    }
    Ok(Value::Object(fields))
}

fn send_once<F>(directory: &Path, ingress: &[u8], socket: &Path, send: F) -> Result<Vec<u8>>
where
    F: FnOnce() -> Result<Vec<u8>>,
{
    if directory.join("submit-marker.json").exists() {
        return Err("enrollment submit already attempted; use exact lookup".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({"type":"minidregg-session-enrollment-submit-v1",
            "ingressSha256":digest(ingress),"operatorSocket":utf8_path(socket)?}),
    )?;
    send()
}

pub(super) fn submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, ingress) = sealed(&directory)?;
    private_socket(&pinned.socket)?;
    let frame = send_once(&directory, &ingress, &pinned.socket, || {
        session_invoke(
            &pinned.host,
            &pinned.socket,
            &pinned.config,
            SUBMIT_OP,
            &ingress,
        )
        .map_err(|error| format!("enrollment op84 uncertain; use exact lookup: {error}"))
    })?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_seal(&directory, &pinned, &ingress)?;
    let result = outcome(&directory, "submit", &frame, SUBMIT_OP, &pinned)?;
    same_seal(&directory, &pinned, &ingress)?;
    let anchor = receipt(&result)?;
    retain_json(&directory.join("receipt.json"), &anchor)?;
    print_json(&result)
}

pub(super) fn lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, ingress) = sealed(&directory)?;
    private_socket(&pinned.socket)?;
    let marker = inspected(&directory, "submit-marker.json")?;
    if field(&marker, "type")? != "minidregg-session-enrollment-submit-v1"
        || field(&marker, "ingressSha256")? != digest(&ingress)
        || field(&marker, "operatorSocket")? != utf8_path(&pinned.socket)?
    {
        return Err("enrollment submit marker differs from exact Ingress".into());
    }
    let index = (0..10_000)
        .find(|index| {
            !directory
                .join(format!("lookup-{index:04}.marker.json"))
                .exists()
        })
        .ok_or("enrollment lookup names exhausted")?;
    let stem = format!("lookup-{index:04}");
    retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({"type":"minidregg-session-enrollment-lookup-v1",
            "ingressSha256":digest(&ingress),"operatorSocket":utf8_path(&pinned.socket)?}),
    )?;
    let frame = session_invoke(
        &pinned.host,
        &pinned.socket,
        &pinned.config,
        LOOKUP_OP,
        &ingress,
    )?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_seal(&directory, &pinned, &ingress)?;
    let result = outcome(&directory, &stem, &frame, LOOKUP_OP, &pinned)?;
    same_seal(&directory, &pinned, &ingress)?;
    if field(&result, "confirmation")? != "replayed" {
        return Err("enrollment lookup did not select accepted historical original".into());
    }
    let selected = receipt(&result)?;
    let anchor = directory.join("receipt.json");
    if anchor.exists() {
        if inspected(&directory, "receipt.json")? != selected {
            return Err("enrollment historical receipt differs".into());
        }
    } else {
        retain_json(&anchor, &selected)?;
    }
    print_json(&result)
}

/// Re-decode canonical source Plan bytes; old cached JSON may predate additive
/// source inspection fields. This is presentation, not a native verdict.
pub(super) fn inspect_plan_exact(directory: &Path) -> Result<Value> {
    let pinned = pin(directory)?;
    let output = fresh_inspection_path(directory, "reenroll-plan")?;
    let fresh = source_inspect(&pinned.host, &pinned.config, PLAN_ROUTE,
        &directory.join("plan.bin"), &output)?;
    same_pin(directory, &pinned)?;
    exact_plan(&fresh, &inspected(directory, "request-inspected.json")?, &pinned.request, &pinned.plan)?;
    Ok(fresh)
}
fn fresh_inspection_path(directory: &Path, stem: &str) -> Result<PathBuf> {
    (0..10_000).map(|i| directory.join(format!("{stem}-{i:04}.json")))
        .find(|p| !p.exists()).ok_or_else(|| "enrollment inspection names exhausted".into())
}
/// Exact historical native lookup followed by fresh source decoding. Host and
/// config must be the caller's pinned execution image; never use an old image
/// against a Store after a compatible upgrade.
pub(super) fn authenticated_anchor(directory: &Path, host: &Path, config: &Path, socket: &Path, inspector: &Path) -> Result<Value> {
    let (pinned, ingress) = sealed(directory)?;
    if pinned.host != host || pinned.socket != socket || bounded(&pinned.config, 65_536)? != bounded(config, 65_536)? {
        return Err("enrollment anchor execution pins differ".into());
    }
    lookup(directory)?;
    let output = fresh_inspection_path(directory, "reenroll-ingress")?;
    let fresh = source_inspect(inspector, &pinned.config, INGRESS_ROUTE,
        &directory.join("ingress.bin"), &output)?;
    same_seal(directory, &pinned, &ingress)?;
    exact_ingress(&fresh, &inspected(directory, "plan-inspected.json")?, &pinned.request, &ingress)?;
    Ok(fresh)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::os::unix::fs::DirBuilderExt;

    #[test]
    fn plan_and_ingress_must_echo_exact_source_request_and_receipt() {
        let request = b"request";
        let plan = b"plan";
        let ingress = b"ingress";
        let source = json!({"type":REQUEST_TYPE,"canonicalRequestHex":hex(request)});
        let view = json!({"type":PLAN_TYPE,"canonicalPlanHex":hex(plan),
            "canonicalRequestHex":hex(request),"request":source,"issueReceipt":{"acceptedCount":"1"},
            "enrollmentHex":"aa","issueReceiptHex":"bb","appRoot":"1",
            "manifestRoot":"2","ticketRoot":"3","slots":[{},{},{},{}]});
        exact_plan(&view, &source, request, plan).unwrap();
        let selected = json!({"type":INGRESS_TYPE,"canonicalIngressHex":hex(ingress),
            "canonicalRequestHex":hex(request),"enrollmentHex":"aa","issueReceiptHex":"bb",
            "issueReceipt":{"acceptedCount":"1"},"appRoot":"1",
            "manifestRoot":"2","ticketRoot":"3"});
        exact_ingress(&selected, &view, request, ingress).unwrap();
        let mut changed = selected;
        changed["ticketRoot"] = json!("4");
        assert!(exact_ingress(&changed, &view, request, ingress).is_err());
        assert!(exact_plan(&view, &source, b"another request", plan).is_err());
    }

    #[test]
    fn lost_submit_response_never_reinvokes_op84() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = env::temp_dir().join(format!(
            "mini-session-enrollment-{}-{unique}",
            std::process::id()
        ));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let sends = Cell::new(0);
        let socket = Path::new("/operator/mini.sock");
        assert!(send_once(&directory, b"exact ingress", socket, || {
            sends.set(sends.get() + 1);
            Err("lost native response".into())
        })
        .is_err());
        assert!(send_once(&directory, b"exact ingress", socket, || {
            sends.set(sends.get() + 1);
            Ok(vec![SUBMIT_OP, 1])
        })
        .is_err());
        assert_eq!(sends.get(), 1);
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn receipt_requires_a_positive_canonical_accepted_count() {
        let mut value = json!({"type":"confirmed","confirmation":"installed",
            "transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"});
        assert_eq!(
            field(&receipt(&value).unwrap(), "acceptedCount").unwrap(),
            "3"
        );
        let expected = receipt(&value).unwrap();
        value["confirmation"] = json!("recoveredAfterUncertainResponse");
        assert_eq!(receipt(&value).unwrap(), expected);
        for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            let mut missing = value.clone();
            missing.as_object_mut().unwrap().remove(name);
            assert!(receipt(&missing).is_err(), "{name}");
        }
        value["acceptedCount"] = json!("0");
        assert!(receipt(&value).is_err());
        value["acceptedCount"] = json!("03");
        assert!(receipt(&value).is_err());
    }
}
