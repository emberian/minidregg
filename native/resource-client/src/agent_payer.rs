//! Controller-only payer signatures for a source-inspected paid AgentGrain plan.
//! The original reserve attempt supplies the exact signed context and receipt;
//! neither a resident-provided plan nor an approval JSON is authority by itself.
use super::agent_reserve::{
    approve_slot, bounded, decode_hex, digest, field, payer_anchor, payer_pin_still, private_bytes,
    private_socket, retain_generated, retain_json, source, source_inspect,
};
use super::*;
use std::os::unix::fs::DirBuilderExt;

const FORMAT: &str = "minidregg-agent-payer-signatures-v1";
const APPROVAL: &str = "minidregg-agent-payer-approval-v1";
const JSON_LIMIT: usize = 8 * transport::HOST_MAX_FRAME;

fn validate_binding(
    paid: &Value,
    original: &Value,
    receipt: &Value,
    approval: &Value,
    plan_sha: &str,
    selector_sha: &str,
) -> Result<()> {
    if field(paid, "type")? != "application-agent-paid-dispatch-plan-v2"
        || field(approval, "type")? != APPROVAL
        || field(approval, "planSha256")? != plan_sha
        || field(approval, "compactSelectorRequestSha256")? != selector_sha
        || paid.get("fixedSelectors") != original.get("fixedSelectors")
        || paid.get("context") != original.get("context")
        || field(paid, "canonicalHttpHex")? != field(original, "canonicalHttpHex")?
        || approval.get("fixedSelectors") != original.get("fixedSelectors")
        || approval.get("context") != original.get("context")
        || field(approval, "canonicalHttpHex")? != field(original, "canonicalHttpHex")?
        || field(approval, "reserveIndex")? != field(receipt, "reserveIndex")?
        || field(paid, "reserveIndex")? != field(receipt, "reserveIndex")?
        || approval.get("reserveReceipt") != Some(receipt)
    {
        return Err("paid plan differs from original reserve or controller approval".into());
    }
    Ok(())
}

fn exact_current_plan(frame: &[u8], plan: &[u8]) -> Result<()> {
    if frame != [vec![48], plan.to_vec()].concat() {
        return Err("paid plan differs from current source op48 selection".into());
    }
    Ok(())
}

/// Read-only source inspection and detached payer signing. This never invokes
/// op46/op49, signs app slots, or gives the seed to the resident process.
pub(super) struct Inputs<'a> {
    pub host: &'a Path,
    pub config: &'a Path,
    pub operator_socket: &'a Path,
    pub reserve_attempt: &'a Path,
    pub paid_plan: &'a Path,
    pub approval_path: &'a Path,
    pub key_path: &'a Path,
    pub directory: &'a Path,
}

pub(super) fn sign(inputs: Inputs<'_>) -> Result<()> {
    let Inputs {
        host,
        config,
        operator_socket,
        reserve_attempt,
        paid_plan,
        approval_path,
        key_path,
        directory,
    } = inputs;
    let host = absolute(host)?;
    let config = absolute(config)?;
    let operator_socket = absolute(operator_socket)?;
    let reserve_attempt = absolute(reserve_attempt)?;
    let directory = absolute(directory)?;
    private_socket(&operator_socket)?;
    let plan = private_bytes(paid_plan, transport::HOST_MAX_FRAME - 1)?;
    let approval_bytes = private_bytes(approval_path, JSON_LIMIT)?;
    let approval: Value = serde_json::from_slice(&approval_bytes)
        .map_err(|error| format!("invalid private agent payer approval: {error}"))?;
    // Check the selected image/config before creating evidence or signing.
    let selected_host_sha = host_image_sha256(&host)?;
    let selected_config = bounded(&config, 65_536)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|error| format!("cannot create agent payer directory: {error}"))?;
    sync_directory_ancestors(&directory)?;
    let original = payer_anchor(&reserve_attempt, &directory)?;
    if host != original.host
        || config != original.config
        || operator_socket != original.operator_socket
        || host_image_sha256(&host)? != selected_host_sha
        || bounded(&config, 65_536)? != selected_config
    {
        return Err("agent payer selected Host/config/operator socket differs from reserve".into());
    }
    create_private(&directory.join("paid-plan.bin"), &plan)?;
    create_private(&directory.join("approval.json"), &approval_bytes)?;
    // Let the pinned Host encode the complete expected paid request from the
    // original exact request/context and confirmed reserve index. Op48 then
    // reselects the current verified image and derives the compact plan; Rust
    // does not reproduce its codec or source current-state checks.
    retain_json(
        &directory.join("expected-selector.json"),
        &json!({
            "fixedRequestHex":hex(&original.request),
            "contextHex":field(&original.plan_inspection["context"], "canonicalHex")?,
            "reserveIndex":field(&original.receipt, "reserveIndex")?
        }),
    )?;
    source(
        &host,
        &config,
        &[
            OsStr::new("author"),
            OsStr::new("application-agent-paid-request"),
            directory.join("expected-selector.json").as_os_str(),
            directory.join("expected-selector.bin").as_os_str(),
        ],
    )?;
    retain_generated(&directory.join("expected-selector.bin"))?;
    let expected = private_bytes(
        &directory.join("expected-selector.bin"),
        transport::HOST_MAX_FRAME - 1,
    )?;
    let fresh_frame = session_invoke(&host, &operator_socket, &config, 48, &expected)?;
    create_private(&directory.join("fresh-paid-plan.frame"), &fresh_frame)?;
    sync_directory_ancestors(&directory)?;
    exact_current_plan(&fresh_frame, &plan)?;
    let paid = source_inspect(
        &host,
        &config,
        "application-agent-paid-dispatch-plan",
        &directory.join("paid-plan.bin"),
        &directory.join("paid-plan-inspected.json"),
    )?;
    if field(&paid, "canonicalPlanHex")? != hex(&plan) {
        return Err("Host inspected a different paid plan".into());
    }
    let compact = decode_hex(field(&paid, "compactSelectorRequestHex")?)?;
    validate_binding(
        &paid,
        &original.plan_inspection,
        &original.receipt,
        &approval,
        &digest(&plan),
        &digest(&compact),
    )?;
    let slots = paid
        .get("payerSlots")
        .and_then(Value::as_array)
        .ok_or("paid plan has no ordered payer slots")?;
    let signers = approval
        .get("signers")
        .and_then(Value::as_array)
        .ok_or("agent payer approval has no ordered signers")?;
    if slots.is_empty() || slots.len() != signers.len() || slots.len() > 16 {
        return Err("payer slot count differs from private approval".into());
    }
    if paid.get("appSlots").and_then(Value::as_array).is_none() {
        return Err("paid plan lacks separate app signing slots".into());
    }
    let key_path = absolute(key_path)?;
    let key_path_text = utf8_path(&key_path)?;
    // All source and approval comparisons finish before the first signature.
    if host_image_sha256(&host)? != selected_host_sha
        || bounded(&config, 65_536)? != selected_config
    {
        return Err("selected Host/config changed before payer signing".into());
    }
    let signatures = slots
        .iter()
        .zip(signers)
        .map(|(slot, signer)| {
            let mut signer = signer.clone();
            signer["keyPath"] = Value::String(key_path_text.to_owned());
            approve_slot(slot, &signer).map(Value::String)
        })
        .collect::<Result<Vec<_>>>()?;
    // Signing is detached and has no native side effect, but never publish a
    // result after its original custody or selected Host/config changed.
    payer_pin_still(&reserve_attempt, &original)?;
    if host_image_sha256(&host)? != selected_host_sha
        || bounded(&config, 65_536)? != selected_config
        || private_bytes(paid_plan, transport::HOST_MAX_FRAME - 1)? != plan
        || private_bytes(approval_path, JSON_LIMIT)? != approval_bytes
    {
        return Err("agent payer custody changed after detached signing".into());
    }
    let result = json!({
        "type":FORMAT,
        "paidPlanSha256":digest(&plan),
        "compactSelectorRequestSha256":digest(&compact),
        "sourcePaidRequestSha256":digest(&expected),
        "originalRequestSha256":digest(&original.request),
        "reserveReceipt":original.receipt,
        "signatures":signatures,
    });
    retain_json(&directory.join("payer-signatures.json"), &result)?;
    sync_directory_ancestors(&directory)?;
    print_json(&result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn payer_binding_requires_original_full_http_context_and_receipt() {
        let original = json!({"fixedSelectors":{"purseTask":"7"},
            "context":{"canonicalHex":"aa","requestDigest":"9"},
            "canonicalHttpHex":"abcd"});
        let receipt = json!({"transactionId":"1","eventId":"2",
            "acceptedCount":"3","imageBoundary":"4","reserveIndex":"2"});
        let paid = json!({"type":"application-agent-paid-dispatch-plan-v2",
            "fixedSelectors":original["fixedSelectors"],"context":original["context"],
            "canonicalHttpHex":"abcd","reserveIndex":"2"});
        let approval = json!({"type":APPROVAL,"planSha256":"p",
            "compactSelectorRequestSha256":"s","fixedSelectors":original["fixedSelectors"],
            "context":original["context"],"canonicalHttpHex":"abcd",
            "reserveIndex":"2","reserveReceipt":receipt});
        assert!(validate_binding(&paid, &original, &receipt, &approval, "p", "s").is_ok());
        let mut changed = paid.clone();
        changed["canonicalHttpHex"] = json!("ef");
        assert!(validate_binding(&changed, &original, &receipt, &approval, "p", "s").is_err());
        changed = paid.clone();
        changed["context"]["requestDigest"] = json!("10");
        assert!(validate_binding(&changed, &original, &receipt, &approval, "p", "s").is_err());
        changed = paid.clone();
        changed["reserveIndex"] = json!("3");
        assert!(validate_binding(&changed, &original, &receipt, &approval, "p", "s").is_err());
        let mut changed = approval.clone();
        changed["reserveReceipt"]["eventId"] = json!("5");
        assert!(validate_binding(&paid, &original, &receipt, &changed, "p", "s").is_err());
    }

    #[test]
    fn payer_signature_requires_exact_current_op48_plan() {
        assert!(exact_current_plan(&[48, 1, 2], &[1, 2]).is_ok());
        assert!(exact_current_plan(&[255, 1, 2], &[1, 2]).is_err());
        assert!(exact_current_plan(&[48, 1, 3], &[1, 2]).is_err());
    }
}
