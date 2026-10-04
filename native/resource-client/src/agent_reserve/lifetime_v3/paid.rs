//! Event 26 lifetime paid dispatch custody. A current source plan is bound to
//! the exact accepted event 27 grant and ordinary lifetime reserve before any
//! detached signatures or physical delivery permit can be requested.
use super::*;

const FORMAT: &str = "minidregg-agent-lifetime-paid-custody-v1";
const APPROVAL: &str = "minidregg-agent-lifetime-paid-approval-v1";
const SUBMIT_MARKER: &str = "minidregg-agent-lifetime-paid-submit-attempt-v1";
const LOOKUP_MARKER: &str = "minidregg-agent-lifetime-paid-lookup-v1";
const REQUEST_ROUTE: &str = "application-agent-lifetime-paid-request";
const PLAN_ROUTE: &str = "application-agent-lifetime-paid-plan";
const PLAN_TYPE: &str = "application-agent-lifetime-paid-plan-v3";
const COMMITTED_ROUTE: &str = "application-agent-lifetime-dispatch-committed";

struct PaidPin {
    reserve: PathBuf,
    grant: PathBuf,
    original: Pin,
    reserve_receipt: Value,
    grant_receipt: Value,
    request: Vec<u8>,
    plan: Vec<u8>,
}

fn receipt(directory: &Path) -> Result<Value> {
    let value: Value =
        serde_json::from_slice(&private_bytes(&directory.join("receipt.json"), 4096)?)
            .map_err(|error| format!("invalid accepted lifetime receipt: {error}"))?;
    let mut exact = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        let decimal = field(&value, name)?;
        if !mini_sdk::decimal::is_canonical_max(decimal, 80)
        {
            return Err(format!("noncanonical lifetime receipt {name}"));
        }
        exact.insert(name.to_owned(), Value::String(decimal.to_owned()));
    }
    Ok(Value::Object(exact))
}

fn grant_anchor(directory: &Path) -> Result<Value> {
    let seal: Value = serde_json::from_slice(&private_bytes(&directory.join("seal.json"), 4096)?)
        .map_err(|error| format!("invalid sealed grant anchor: {error}"))?;
    let call = private_bytes(&directory.join("call.bin"), REQUEST_LIMIT)?;
    let marker: Value =
        serde_json::from_slice(&private_bytes(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|error| format!("invalid submitted grant anchor: {error}"))?;
    if field(&seal, "format")? != "minidregg-agent-lifetime-grant-custody-v1"
        || field(&seal, "callSha256")? != digest(&call)
        || field(&marker, "type")? != "minidregg-agent-lifetime-grant-submit-attempt-v1"
        || field(&marker, "callSha256")? != digest(&call)
    {
        return Err("lifetime grant anchor is not a submitted sealed call".into());
    }
    let raw: Value = serde_json::from_slice(&private_bytes(&directory.join("receipt.json"), 4096)?)
        .map_err(|error| format!("invalid grant receipt: {error}"))?;
    let exact = receipt(directory)?;
    let expected = field(&exact, "acceptedCount")?
        .parse::<u64>()
        .map_err(|error| format!("invalid grant accepted count: {error}"))?
        .checked_sub(1)
        .ok_or("grant accepted count is zero")?;
    if field(&raw, "grantIndex")? != expected.to_string() {
        return Err("grant index differs from original accepted receipt".into());
    }
    Ok(exact)
}

fn json_digest(value: &Value) -> Result<String> {
    Ok(digest(
        &serde_json::to_vec(value).map_err(|error| error.to_string())?,
    ))
}

fn bound_inspection(directory: &Path, name: &str) -> Result<Value> {
    serde_json::from_slice(&private_bytes(&directory.join(name), JSON_LIMIT)?)
        .map_err(|error| format!("invalid retained lifetime inspection: {error}"))
}

fn initial_bindings(reserve: &Value, grant: &Value, reserve_receipt: &Value) -> Result<()> {
    if reserve
        .get("bindings")
        .and_then(|value| value.get("grantIssueReceipt"))
        != Some(grant)
        || reserve
            .get("bindings")
            .and_then(|value| value.get("grantIssueReceipt"))
            == Some(&Value::Null)
        || field(reserve_receipt, "acceptedCount")? == "0"
    {
        return Err("lifetime reserve is not bound to the accepted grant".into());
    }
    Ok(())
}

fn paid_pin(directory: &Path) -> Result<PaidPin> {
    crate::fsio::ensure_private_dir_durable(directory)?;
    let value: Value = serde_json::from_slice(&private_bytes(&directory.join("pin.json"), 4096)?)
        .map_err(|error| format!("invalid lifetime paid pin: {error}"))?;
    if field(&value, "format")? != FORMAT {
        return Err("unsupported lifetime paid custody format".into());
    }
    let reserve = PathBuf::from(field(&value, "reserveAttempt")?);
    let grant = PathBuf::from(field(&value, "grantAttempt")?);
    if !reserve.is_absolute() || !grant.is_absolute() {
        return Err("lifetime paid anchor paths must be absolute".into());
    }
    let original = super::sealed(&reserve)?.0;
    let reserve_receipt = receipt(&reserve)?;
    let grant_receipt = grant_anchor(&grant)?;
    let reserve_view = bound_inspection(&reserve, "plan-inspected.json")?;
    initial_bindings(&reserve_view, &grant_receipt, &reserve_receipt)?;
    let request = private_bytes(&directory.join("request.bin"), REQUEST_LIMIT)?;
    let plan = private_bytes(&directory.join("plan.bin"), REQUEST_LIMIT)?;
    if digest(&request) != field(&value, "requestSha256")?
        || digest(&plan) != field(&value, "planSha256")?
        || digest(&original.request) != field(&value, "originalRequestSha256")?
        || digest(&original.plan) != field(&value, "originalPlanSha256")?
        || json_digest(&reserve_receipt)? != field(&value, "reserveReceiptSha256")?
        || json_digest(&grant_receipt)? != field(&value, "grantReceiptSha256")?
        || bounded(&directory.join("plan.frame"), transport::HOST_MAX_FRAME)?
            != [vec![78], plan.clone()].concat()
    {
        return Err("lifetime paid exact source or accepted anchors changed".into());
    }
    Ok(PaidPin {
        reserve,
        grant,
        original,
        reserve_receipt,
        grant_receipt,
        request,
        plan,
    })
}

fn same_paid_pin(directory: &Path, previous: &PaidPin) -> Result<()> {
    let current = paid_pin(directory)?;
    if current.reserve != previous.reserve
        || current.grant != previous.grant
        || current.original.host != previous.original.host
        || current.original.config != previous.original.config
        || current.original.operator_socket != previous.original.operator_socket
        || current.original.request != previous.original.request
        || current.original.plan != previous.original.plan
        || current.reserve_receipt != previous.reserve_receipt
        || current.grant_receipt != previous.grant_receipt
        || current.request != previous.request
        || current.plan != previous.plan
    {
        return Err("lifetime paid custody pin changed".into());
    }
    Ok(())
}

pub(crate) fn lifetime_paid_plan(reserve: &Path, grant: &Path, directory: &Path) -> Result<()> {
    let reserve = absolute(reserve)?;
    let grant = absolute(grant)?;
    let directory = absolute(directory)?;
    let original = super::sealed(&reserve)?.0;
    private_socket(&original.operator_socket)?;
    let reserve_receipt = receipt(&reserve)?;
    let grant_receipt = grant_anchor(&grant)?;
    let reserve_view = bound_inspection(&reserve, "plan-inspected.json")?;
    initial_bindings(&reserve_view, &grant_receipt, &reserve_receipt)?;
    let reserve_index = field(&reserve_receipt, "acceptedCount")?
        .parse::<u64>()
        .map_err(|error| format!("invalid lifetime reserve count: {error}"))?
        .checked_sub(1)
        .ok_or("lifetime reserve accepted count is zero")?;
    crate::fsio::create_private_dir(&directory)?;
    sync_directory_ancestors(&directory)?;
    retain_json(
        &directory.join("selector.json"),
        &json!({
            "fixedRequestHex":hex(&original.request),
            "contextHex":field(&reserve_view["context"], "canonicalHex")?,
            "reserveIndex":reserve_index.to_string(),
        }),
    )?;
    source(
        &original.host,
        &original.config,
        &[
            OsStr::new("author"),
            OsStr::new(REQUEST_ROUTE),
            directory.join("selector.json").as_os_str(),
            directory.join("request.bin").as_os_str(),
        ],
    )?;
    retain_generated(&directory.join("request.bin"))?;
    let request = private_bytes(&directory.join("request.bin"), REQUEST_LIMIT)?;
    let request_view = source_inspect(
        &original.host,
        &original.config,
        REQUEST_ROUTE,
        &directory.join("request.bin"),
        &directory.join("request-inspected.json"),
    )?;
    if field(&request_view, "type")? != "application-agent-lifetime-paid-request-v3"
        || field(&request_view, "canonicalRequestHex")? != hex(&request)
        || field(&request_view, "reserveIndex")? != reserve_index.to_string()
    {
        return Err("Host inspected a different lifetime paid request".into());
    }
    let frame = session_invoke(
        &original.host,
        &original.operator_socket,
        &original.config,
        78,
        &request,
    )?;
    create_private(&directory.join("plan.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    let plan = expect_reply(&frame, 78)?;
    create_private(&directory.join("plan.bin"), plan)?;
    let inspection = source_inspect(
        &original.host,
        &original.config,
        PLAN_ROUTE,
        &directory.join("plan.bin"),
        &directory.join("plan-inspected.json"),
    )?;
    if field(&inspection, "type")? != PLAN_TYPE
        || field(&inspection, "canonicalPlanHex")? != hex(plan)
        || field(&inspection, "compactSelectorRequestHex")?.is_empty()
        || inspection.get("fixedSelectors") != reserve_view.get("fixedSelectors")
        || inspection.get("context") != reserve_view.get("context")
        || inspection.get("reserveReceipt") != Some(&reserve_receipt)
        || field(&inspection, "reserveIndex")? != reserve_index.to_string()
        || inspection
            .get("bindings")
            .and_then(|value| value.get("grantIssueReceipt"))
            != Some(&grant_receipt)
        || inspection
            .get("bindings")
            .and_then(|value| value.get("originalIssueReceipt"))
            != reserve_view
                .get("bindings")
                .and_then(|value| value.get("originalIssueReceipt"))
        || field(&inspection, "canonicalHttpHex")? != field(&reserve_view, "canonicalHttpHex")?
    {
        return Err("lifetime paid plan differs from original reserve or grant".into());
    }
    same_pin(&reserve, &original)?;
    retain_json(
        &directory.join("pin.json"),
        &json!({
            "format":FORMAT, "reserveAttempt":utf8_path(&reserve)?,
            "grantAttempt":utf8_path(&grant)?,
            "originalRequestSha256":digest(&original.request),
            "originalPlanSha256":digest(&original.plan),
            "reserveReceiptSha256":json_digest(&reserve_receipt)?,
            "grantReceiptSha256":json_digest(&grant_receipt)?,
            "requestSha256":digest(&request), "planSha256":digest(plan),
        }),
    )?;
    print_json(&inspection)
}

fn encode_signatures(
    pinned: &PaidPin,
    directory: &Path,
    name: &str,
    slots: &[Value],
    signers: &[Value],
) -> Result<Vec<u8>> {
    if slots.is_empty() || slots.len() != signers.len() || slots.len() > 16 {
        return Err(format!(
            "lifetime paid {name} signing slots differ from approval"
        ));
    }
    let signatures = slots
        .iter()
        .zip(signers)
        .map(|(slot, signer)| approve_slot(slot, signer).map(Value::String))
        .collect::<Result<Vec<_>>>()?;
    retain_json(
        &directory.join(format!("{name}-signatures.json")),
        &Value::Array(signatures),
    )?;
    source(
        &pinned.original.host,
        &pinned.original.config,
        &[
            OsStr::new("signatures"),
            directory
                .join(format!("{name}-signatures.json"))
                .as_os_str(),
            directory.join(format!("{name}-signatures.bin")).as_os_str(),
        ],
    )?;
    let path = directory.join(format!("{name}-signatures.bin"));
    retain_generated(&path)?;
    private_bytes(&path, 4096)
}

fn pair(left: &[u8], right: &[u8]) -> Result<Vec<u8>> {
    let length: u32 = left
        .len()
        .try_into()
        .map_err(|_| "lifetime paid pair too long")?;
    let mut bytes = length.to_le_bytes().to_vec();
    bytes.extend_from_slice(left);
    bytes.extend_from_slice(right);
    Ok(bytes)
}

/// Sign only the payer slots under the controller's protected purse key.
/// App and grant slots belong to the resident custodian and are never accepted
/// in this approval. The exact op78 plan is re-observed before key use; this
/// helper does not assemble op79 or submit public op76.
pub(crate) fn lifetime_paid_payer_sign(directory: &Path, approval_json: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let pinned = paid_pin(&directory)?;
    private_socket(&pinned.original.operator_socket)?;
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid lifetime payer-only approval: {error}"))?;
    let retained = bound_inspection(&directory, "plan-inspected.json")?;
    let fresh = source_inspect(
        &pinned.original.host,
        &pinned.original.config,
        PLAN_ROUTE,
        &directory.join("plan.bin"),
        &directory.join("payer-plan-inspected.json"),
    )?;
    if fresh != retained
        || field(&approval, "type")? != "minidregg-agent-lifetime-payer-approval-v1"
        || field(&approval, "requestSha256")? != digest(&pinned.request)
        || field(&approval, "planSha256")? != digest(&pinned.plan)
        || approval.get("fixedSelectors") != retained.get("fixedSelectors")
        || approval.get("context") != retained.get("context")
        || approval.get("bindings") != retained.get("bindings")
        || approval.get("canonicalHttpHex") != retained.get("canonicalHttpHex")
        || approval.get("reserveReceipt") != Some(&pinned.reserve_receipt)
        || approval.get("grantIssueReceipt") != Some(&pinned.grant_receipt)
        || approval.get("appSigners").is_some()
        || approval.get("grantSigner").is_some()
    {
        return Err("lifetime payer approval differs from exact source plan".into());
    }
    let current = session_invoke(
        &pinned.original.host,
        &pinned.original.operator_socket,
        &pinned.original.config,
        78,
        &pinned.request,
    )?;
    create_private(&directory.join("payer-current-plan.frame"), &current)?;
    sync_directory_ancestors(&directory)?;
    if expect_reply(&current, 78)? != pinned.plan {
        return Err("lifetime payer plan changed at current verified image".into());
    }
    let slots = retained
        .get("payerSlots")
        .and_then(Value::as_array)
        .ok_or("lifetime paid plan lacks payer slots")?;
    let signers = approval
        .get("payerSigners")
        .and_then(Value::as_array)
        .ok_or("lifetime payer approval lacks payer signers")?;
    payer_slot_shape(slots, signers)?;
    same_paid_pin(&directory, &pinned)?;
    let signatures = Value::Array(
        slots
            .iter()
            .zip(signers)
            .map(|(slot, signer)| approve_slot(slot, signer).map(Value::String))
            .collect::<Result<Vec<_>>>()?,
    );
    let bytes = serde_json::to_vec(&signatures)
        .map_err(|error| format!("lifetime payer signatures JSON: {error}"))?;
    create_private(&directory.join("payer-only-signatures.json"), &bytes)?;
    source(
        &pinned.original.host,
        &pinned.original.config,
        &[
            OsStr::new("signatures"),
            directory.join("payer-only-signatures.json").as_os_str(),
            directory.join("payer-only-signatures.bin").as_os_str(),
        ],
    )?;
    retain_generated(&directory.join("payer-only-signatures.bin"))?;
    same_paid_pin(&directory, &pinned)?;
    create_private(&directory.join("payer-only-approval.json"), &approval_bytes)?;
    retain_json(
        &directory.join("payer-only-result.json"),
        &json!({
            "type":"minidregg-agent-lifetime-payer-signatures-v1",
            "planSha256":digest(&pinned.plan),
            "requestSha256":digest(&pinned.request),
            "reserveReceipt":pinned.reserve_receipt,
            "grantIssueReceipt":pinned.grant_receipt,
            "signatures":signatures,
            "encodedSha256":digest(&private_bytes(
                &directory.join("payer-only-signatures.bin"), 4096)?),
        }),
    )?;
    print_json(
        &serde_json::from_slice::<Value>(&private_bytes(
            &directory.join("payer-only-result.json"),
            65_536,
        )?)
        .map_err(|error| format!("lifetime payer result JSON: {error}"))?,
    )
}

fn payer_slot_shape(slots: &[Value], signers: &[Value]) -> Result<()> {
    if slots.len() != 3 || signers.len() != 3 {
        return Err("lifetime payer requires exact target/observe/authority slots".into());
    }
    for ((slot, signer), role) in slots.iter().zip(signers).zip(["4", "8", "1"]) {
        if field(slot, "role")? != role
            || field(slot, "index")? != "0"
            || field(signer, "role")? != role
            || field(signer, "index")? != "0"
        {
            return Err("lifetime payer slot order or signer role differs".into());
        }
    }
    for signer in signers.iter().skip(1) {
        for name in ["keyId", "keyEpoch", "publicKey", "keyPath"] {
            if field(signer, name)? != field(&signers[0], name)? {
                return Err("lifetime payer slots use different custodians".into());
            }
        }
    }
    Ok(())
}

pub(crate) fn lifetime_paid_seal(directory: &Path, approval_json: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let pinned = paid_pin(&directory)?;
    private_socket(&pinned.original.operator_socket)?;
    if directory.join("seal.json").exists() || directory.join("ingress.bin").exists() {
        return Err("lifetime paid plan was already sealed".into());
    }
    let approval_bytes = private_bytes(approval_json, 65_536)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid lifetime paid approval: {error}"))?;
    let retained = bound_inspection(&directory, "plan-inspected.json")?;
    let fresh = source_inspect(
        &pinned.original.host,
        &pinned.original.config,
        PLAN_ROUTE,
        &directory.join("plan.bin"),
        &directory.join("seal-plan-inspected.json"),
    )?;
    if fresh != retained
        || field(&approval, "type")? != APPROVAL
        || field(&approval, "requestSha256")? != digest(&pinned.request)
        || field(&approval, "planSha256")? != digest(&pinned.plan)
        || approval.get("fixedSelectors") != retained.get("fixedSelectors")
        || approval.get("context") != retained.get("context")
        || approval.get("bindings") != retained.get("bindings")
        || approval.get("canonicalHttpHex") != retained.get("canonicalHttpHex")
        || approval.get("reserveReceipt") != Some(&pinned.reserve_receipt)
        || approval.get("grantIssueReceipt") != Some(&pinned.grant_receipt)
    {
        return Err("lifetime paid approval differs from source and accepted anchors".into());
    }
    let current = session_invoke(
        &pinned.original.host,
        &pinned.original.operator_socket,
        &pinned.original.config,
        78,
        &pinned.request,
    )?;
    create_private(&directory.join("seal-current-plan.frame"), &current)?;
    sync_directory_ancestors(&directory)?;
    if expect_reply(&current, 78)? != pinned.plan {
        return Err("lifetime paid plan changed at current verified image".into());
    }
    let app_slots = retained
        .get("appSlots")
        .and_then(Value::as_array)
        .ok_or("lifetime paid plan lacks app slots")?;
    let payer_slots = retained
        .get("payerSlots")
        .and_then(Value::as_array)
        .ok_or("lifetime paid plan lacks payer slots")?;
    let app_signers = approval
        .get("appSigners")
        .and_then(Value::as_array)
        .ok_or("lifetime paid approval lacks app signers")?;
    let payer_signers = approval
        .get("payerSigners")
        .and_then(Value::as_array)
        .ok_or("lifetime paid approval lacks payer signers")?;
    let grant_slot = retained
        .get("grantObservationSlot")
        .ok_or("lifetime paid plan lacks grant observation slot")?;
    let grant_signer = approval
        .get("grantSigner")
        .ok_or("lifetime paid approval lacks grant signer")?;
    // Recheck all approval structure and custody pins before the first key use.
    same_paid_pin(&directory, &pinned)?;
    let app_bytes = encode_signatures(&pinned, &directory, "app", app_slots, app_signers)?;
    let grant_hex = approve_slot(grant_slot, grant_signer)?;
    let grant_signature = decode_hex(&grant_hex)?;
    if grant_signature.len() != 64 {
        return Err("lifetime grant observation signature is not 64 bytes".into());
    }
    create_private(&directory.join("grant-signature.bin"), &grant_signature)?;
    let payer_bytes = encode_signatures(&pinned, &directory, "payer", payer_slots, payer_signers)?;
    same_paid_pin(&directory, &pinned)?;
    let nested = pair(&grant_signature, &payer_bytes)?;
    let signatures = pair(&app_bytes, &nested)?;
    let payload = pair(&pinned.plan, &signatures)?;
    let frame = session_invoke(
        &pinned.original.host,
        &pinned.original.operator_socket,
        &pinned.original.config,
        79,
        &payload,
    )?;
    create_private(&directory.join("assembly.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_paid_pin(&directory, &pinned)?;
    let ingress = expect_reply(&frame, 79)?;
    create_private(&directory.join("ingress.bin"), ingress)?;
    sync_retained_call(&directory, &directory.join("ingress.bin"))?;
    create_private(&directory.join("approval.json"), &approval_bytes)?;
    retain_json(
        &directory.join("seal.json"),
        &json!({
            "format":FORMAT, "requestSha256":digest(&pinned.request),
            "planSha256":digest(&pinned.plan), "approvalSha256":digest(&approval_bytes),
            "ingressSha256":digest(ingress),
        }),
    )?;
    println!("{}", directory.join("ingress.bin").display());
    Ok(())
}

fn paid_sealed(directory: &Path) -> Result<(PaidPin, Vec<u8>)> {
    let pinned = paid_pin(directory)?;
    let seal: Value = serde_json::from_slice(&private_bytes(&directory.join("seal.json"), 4096)?)
        .map_err(|error| format!("invalid lifetime paid seal: {error}"))?;
    let ingress = private_bytes(&directory.join("ingress.bin"), REQUEST_LIMIT)?;
    if field(&seal, "format")? != FORMAT
        || field(&seal, "requestSha256")? != digest(&pinned.request)
        || field(&seal, "planSha256")? != digest(&pinned.plan)
        || field(&seal, "approvalSha256")?
            != digest(&private_bytes(&directory.join("approval.json"), 65_536)?)
        || field(&seal, "ingressSha256")? != digest(&ingress)
        || bounded(&directory.join("assembly.frame"), transport::HOST_MAX_FRAME)?
            != [vec![79], ingress.clone()].concat()
    {
        return Err("lifetime paid exact sealed ingress differs from assembly".into());
    }
    Ok((pinned, ingress))
}

fn four_fields(value: &Value) -> Result<Value> {
    let mut fields = serde_json::Map::new();
    for name in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        let decimal = field(value, name)?;
        if !mini_sdk::decimal::is_canonical_max(decimal, 80)
        {
            return Err(format!("noncanonical lifetime paid receipt {name}"));
        }
        fields.insert(name.to_owned(), Value::String(decimal.to_owned()));
    }
    Ok(Value::Object(fields))
}

fn validate_committed(
    inspection: &Value,
    committed: &[u8],
    pinned: &PaidPin,
    plan: &Value,
) -> Result<Value> {
    if field(inspection, "type")? != "application-agent-lifetime-dispatch-committed-inspection-v3"
        || field(inspection, "frameHex")? != hex(committed)
        || inspection
            .get("purse")
            .and_then(|value| value.get("reserveReceipt"))
            != Some(&pinned.reserve_receipt)
        || inspection
            .get("grant")
            .and_then(|value| value.get("issueReceipt"))
            != Some(&pinned.grant_receipt)
        || inspection
            .get("request")
            .and_then(|value| value.get("canonicalHex"))
            .and_then(Value::as_str)
            != plan.get("canonicalHttpHex").and_then(Value::as_str)
    {
        return Err("lifetime paid permit differs from retained reserve/grant/request".into());
    }
    four_fields(field_value(inspection, "dispatchReceipt")?)
}

fn field_value<'a>(value: &'a Value, name: &str) -> Result<&'a Value> {
    value
        .get(name)
        .ok_or_else(|| format!("missing lifetime paid {name}"))
}

fn submit_once<F>(directory: &Path, ingress: &[u8], send: F) -> Result<Vec<u8>>
where
    F: FnOnce() -> Result<Vec<u8>>,
{
    if directory.join("submit-marker.json").exists() {
        return Err("lifetime paid submit already attempted; use receipt-only lookup".into());
    }
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({
            "type":SUBMIT_MARKER, "ingressSha256":digest(ingress),
        }),
    )?;
    send()
}

pub(crate) fn lifetime_paid_submit(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, ingress) = paid_sealed(&directory)?;
    private_socket(&pinned.original.operator_socket)?;
    let frame = submit_once(&directory, &ingress, || {
        session_invoke(
            &pinned.original.host,
            &pinned.original.operator_socket,
            &pinned.original.config,
            76,
            &ingress,
        )
        .map_err(|error| format!("lifetime paid op76 uncertain; use exact lookup: {error}"))
    })?;
    create_private(&directory.join("submit.frame"), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_paid_pin(&directory, &pinned)?;
    let committed = expect_reply(&frame, 76)?;
    create_private(&directory.join("committed.bin"), committed)?;
    let inspection = source_inspect(
        &pinned.original.host,
        &pinned.original.config,
        COMMITTED_ROUTE,
        &directory.join("committed.bin"),
        &directory.join("committed-inspected.json"),
    )?;
    let plan = bound_inspection(&directory, "plan-inspected.json")?;
    let receipt = validate_committed(&inspection, committed, &pinned, &plan)?;
    same_paid_pin(&directory, &pinned)?;
    retain_json(&directory.join("receipt.json"), &receipt)?;
    print_json(&inspection)
}

fn next_lookup(directory: &Path, ingress: &[u8]) -> Result<String> {
    let marker: Value =
        serde_json::from_slice(&private_bytes(&directory.join("submit-marker.json"), 4096)?)
            .map_err(|error| format!("invalid lifetime paid submit marker: {error}"))?;
    if field(&marker, "type")? != SUBMIT_MARKER
        || field(&marker, "ingressSha256")? != digest(ingress)
    {
        return Err("lifetime paid submit marker differs from exact ingress".into());
    }
    let mut index = 0;
    while directory
        .join(format!("lookup-{index:04}.marker.json"))
        .exists()
    {
        index += 1;
        if index >= 10_000 {
            return Err("lifetime paid lookup names exhausted".into());
        }
    }
    let stem = format!("lookup-{index:04}");
    retain_json(
        &directory.join(format!("{stem}.marker.json")),
        &json!({
            "type":LOOKUP_MARKER, "ingressSha256":digest(ingress),
        }),
    )?;
    Ok(stem)
}

pub(crate) fn lifetime_paid_lookup(directory: &Path) -> Result<()> {
    let directory = absolute(directory)?;
    let (pinned, ingress) = paid_sealed(&directory)?;
    private_socket(&pinned.original.operator_socket)?;
    let stem = next_lookup(&directory, &ingress)?;
    let frame = session_invoke(
        &pinned.original.host,
        &pinned.original.operator_socket,
        &pinned.original.config,
        77,
        &ingress,
    )?;
    create_private(&directory.join(format!("{stem}.frame")), &frame)?;
    sync_directory_ancestors(&directory)?;
    same_paid_pin(&directory, &pinned)?;
    let outcome_bytes = expect_reply(&frame, 77)?;
    create_private(
        &directory.join(format!("{stem}.outcome.bin")),
        outcome_bytes,
    )?;
    let outcome = source_inspect(
        &pinned.original.host,
        &pinned.original.config,
        "outcome",
        &directory.join(format!("{stem}.outcome.bin")),
        &directory.join(format!("{stem}.outcome.json")),
    )?;
    if field(&outcome, "confirmation")? != "replayed" {
        return Err("lifetime paid lookup did not confirm original history".into());
    }
    let receipt = exact_receipt(&outcome)?;
    let anchor = directory.join("receipt.json");
    if anchor.exists() {
        let previous: Value = serde_json::from_slice(&private_bytes(&anchor, 4096)?)
            .map_err(|error| format!("invalid retained lifetime paid receipt: {error}"))?;
        if previous != receipt {
            return Err("lifetime paid historical receipt differs from original".into());
        }
    } else {
        retain_json(&anchor, &receipt)?;
    }
    same_paid_pin(&directory, &pinned)?;
    print_json(&outcome)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn payer_only_approval_requires_three_ordered_source_incidence_slots() {
        let slot = |role: &str| {
            json!({"role":role,"index":"0",
            "keyId":"7007","keyEpoch":"1","publicKey":"ab",
            "keyPath":"/private/payer.key"})
        };
        let slots = vec![slot("4"), slot("8"), slot("1")];
        assert!(payer_slot_shape(&slots, &slots).is_ok());
        let mut swapped = slots.clone();
        swapped.swap(1, 2);
        assert!(payer_slot_shape(&swapped, &slots).is_err());
        let mut foreign = slots.clone();
        foreign[2]["index"] = json!("1");
        assert!(payer_slot_shape(&slots, &foreign).is_err());
        foreign = slots.clone();
        foreign[2]["keyPath"] = json!("/private/other.key");
        assert!(payer_slot_shape(&slots, &foreign).is_err());
        assert!(payer_slot_shape(&slots[..2], &slots[..2]).is_err());
    }

    #[test]
    fn lost_paid_submit_reply_never_reissues_and_lookups_are_numbered() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = std::env::temp_dir().join(format!("mini-lifetime-paid-{unique}"));
        fs::DirBuilder::new()
            .mode(0o700)
            .create(&directory)
            .unwrap();
        let sent = Cell::new(0);
        let ingress = b"exact event26 ingress";
        let first = submit_once(&directory, ingress, || {
            sent.set(sent.get() + 1);
            Err("host reply lost after install".into())
        });
        assert!(first.is_err());
        assert!(directory.join("submit-marker.json").exists());
        assert!(submit_once(&directory, ingress, || {
            sent.set(sent.get() + 1);
            Ok(vec![76])
        })
        .is_err());
        assert_eq!(sent.get(), 1);
        assert_eq!(next_lookup(&directory, ingress).unwrap(), "lookup-0000");
        assert_eq!(next_lookup(&directory, ingress).unwrap(), "lookup-0001");
        assert_eq!(sent.get(), 1);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn paid_plan_requires_original_grant_and_reserve_receipts() {
        let grant = json!({"transactionId":"1","eventId":"2",
            "acceptedCount":"3","worldRoot":"4"});
        let reserve = json!({"bindings":{"grantIssueReceipt":grant}});
        let accepted = json!({"transactionId":"5","eventId":"6",
            "acceptedCount":"7","worldRoot":"8"});
        assert!(initial_bindings(&reserve, &grant, &accepted).is_ok());
        let mut wrong = grant.clone();
        wrong["eventId"] = json!("9");
        assert!(initial_bindings(&reserve, &wrong, &accepted).is_err());
        let mut wrong_count = accepted;
        wrong_count["acceptedCount"] = json!("0");
        assert!(initial_bindings(&reserve, &grant, &wrong_count).is_err());
    }

    #[test]
    fn paid_assembly_payload_has_exact_nested_host_pair_shape() {
        let app = [1, 2, 3];
        let grant = [4; 64];
        let payer = [5, 6];
        let plan = [7, 8, 9, 10];
        let encoded = pair(&plan, &pair(&app, &pair(&grant, &payer).unwrap()).unwrap()).unwrap();
        assert_eq!(&encoded[..4], &(4_u32).to_le_bytes());
        assert_eq!(&encoded[4..8], &plan);
        assert_eq!(&encoded[8..12], &(3_u32).to_le_bytes());
        assert_eq!(&encoded[12..15], &app);
        assert_eq!(&encoded[15..19], &(64_u32).to_le_bytes());
        assert_eq!(&encoded[19..83], &grant);
        assert_eq!(&encoded[83..], &payer);
    }

    #[test]
    fn committed_permit_must_match_both_historical_receipts_and_http() {
        let reserve_receipt = json!({"transactionId":"1","eventId":"2",
            "acceptedCount":"3","worldRoot":"4"});
        let grant_receipt = json!({"transactionId":"5","eventId":"6",
            "acceptedCount":"7","worldRoot":"8"});
        let pinned = PaidPin {
            reserve: PathBuf::new(),
            grant: PathBuf::new(),
            original: Pin {
                host: PathBuf::new(),
                config: PathBuf::new(),
                operator_socket: PathBuf::new(),
                public_socket: PathBuf::new(),
                request: vec![],
                plan: vec![],
            },
            reserve_receipt: reserve_receipt.clone(),
            grant_receipt: grant_receipt.clone(),
            request: vec![],
            plan: vec![],
        };
        let committed = [1, 2, 3];
        let mut inspection = json!({
            "type":"application-agent-lifetime-dispatch-committed-inspection-v3",
            "frameHex":hex(&committed),
            "purse":{"reserveReceipt":reserve_receipt},
            "grant":{"issueReceipt":grant_receipt},
            "request":{"canonicalHex":"abcd"},
            "dispatchReceipt":{"transactionId":"9","eventId":"10",
                "acceptedCount":"11","worldRoot":"12"},
        });
        let plan = json!({"canonicalHttpHex":"abcd"});
        assert!(validate_committed(&inspection, &committed, &pinned, &plan).is_ok());
        inspection["grant"]["issueReceipt"]["eventId"] = json!("13");
        assert!(validate_committed(&inspection, &committed, &pinned, &plan).is_err());
    }
}
