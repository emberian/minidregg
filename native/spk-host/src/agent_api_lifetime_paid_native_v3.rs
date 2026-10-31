//! Exact op78/79 lifetime paid assembly. This stage retains an ingress but
//! cannot deliver it: only a later fresh op76 installed callback may do that.

use crate::agent_api_lifetime_custody_v3::LifetimeCustodyV3;
use crate::agent_api_lifetime_reverse_v3::{LifetimeReverseClient, RetainedReserveV3};
use crate::agent_api_lifetime_v3::{match_paid_plan, LifetimeBinding};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::io;
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;
use crate::canonical::hex;

fn refused(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn source_payload(frame: &[u8], opcode: u8) -> io::Result<&[u8]> {
    if frame.len() < 6
        || u32::from_le_bytes(frame[..4].try_into().unwrap()) as usize + 4 != frame.len()
        || frame[4] != opcode
    {
        return Err(refused("lifetime paid native reply opcode/frame drift"));
    }
    Ok(&frame[5..])
}

// Preserve the authoritative reply before projecting it. A planning refusal
// does not settle the already-admitted reserve, so this is diagnostic only:
// the caller still retains its uncertain hold for reconciliation.
fn retained_source_payload(
    operator: &PrivateOperator,
    directory: &Path,
    name: &str,
    opcode: u8,
    frame: &[u8],
) -> io::Result<Vec<u8>> {
    write_new(directory, &format!("{name}.frame"), frame)?;
    match source_payload(frame, opcode) {
        Ok(payload) => Ok(payload.to_vec()),
        Err(error) => match outcome_words(operator, directory, name, frame)? {
            Some(words) => Err(io::Error::new(io::ErrorKind::InvalidData, format!("lifetime paid op{opcode}: {words}"))),
            None => Err(error),
        },
    }
}

/// The refusal words of a Host outcome frame (a no-record or Host outcome), read through the Host's own
/// outcome inspection; `None` when the frame is not an outcome. Diagnostic only: it decides nothing.
pub(crate) fn outcome_words(
    operator: &PrivateOperator,
    directory: &Path,
    name: &str,
    frame: &[u8],
) -> io::Result<Option<String>> {
    use crate::host_operations::{RESPONSE_HOST_OUTCOME, RESPONSE_NO_RECORD};
    use crate::lifecycle_receipt_lookup::OUTCOME_TAG;
    use crate::lifecycle_v3_native::framed_payload;
    let outcome = framed_payload("lifetime planning outcome", frame, RESPONSE_NO_RECORD, OUTCOME_TAG)
        .or_else(|_| framed_payload("lifetime planning outcome", frame, RESPONSE_HOST_OUTCOME, OUTCOME_TAG));
    let Ok(payload) = outcome else { return Ok(None) };
    let path = write_new(directory, &format!("{name}-outcome.bin"), payload)?;
    let bytes = operator.tool("inspect", "outcome", &path, &directory.join(format!("{name}-outcome.json")))?;
    let view: Value = serde_json::from_slice(&bytes)?;
    Ok(Some(crate::dispatch_fence::refusal_words(&view)))
}

fn pair(left: &[u8], right: &[u8]) -> io::Result<Vec<u8>> {
    let length = u32::try_from(left.len()).map_err(|_| refused("lifetime paid pair size"))?;
    let mut result = Vec::with_capacity(4 + left.len() + right.len());
    result.extend_from_slice(&length.to_le_bytes());
    result.extend_from_slice(left);
    result.extend_from_slice(right);
    Ok(result)
}

fn signatures(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    name: &str,
    values: &Value,
) -> io::Result<Vec<u8>> {
    let input = write_new(
        attempt_dir,
        &format!("{name}.json"),
        &serde_json::to_vec(values)?,
    )?;
    operator.tool(
        "signatures",
        "",
        &input,
        &attempt_dir.join(format!("{name}.bin")),
    )
}

pub(crate) struct AssembledLifetimePaidV3 {
    #[allow(dead_code)] // Agent API v3 is parked (ruling R7); retained beside the ingress it produced.
    pub plan: Vec<u8>,
    pub ingress: Vec<u8>,
    pub inspection: Value,
    pub signed_post_reserve_purse_physical_root: String,
}

pub(crate) struct PaidAssemblyInput<'a> {
    pub operator: &'a PrivateOperator,
    pub custody: &'a LifetimeCustodyV3,
    pub reverse: &'a LifetimeReverseClient,
    pub binding: &'a LifetimeBinding,
    pub reserve: &'a RetainedReserveV3,
    pub attempt_dir: &'a Path,
    pub cancelled: &'a AtomicBool,
    pub deadline: Instant,
}

pub(crate) fn assemble_once(input: PaidAssemblyInput<'_>) -> io::Result<AssembledLifetimePaidV3> {
    let PaidAssemblyInput {
        operator,
        custody,
        reverse,
        binding,
        reserve,
        attempt_dir,
        cancelled,
        deadline,
    } = input;
    if cancelled.load(Ordering::Acquire) {
        return Err(refused("lifetime caller cancelled before paid authoring"));
    }
    private_dir(attempt_dir)?;
    let reserve_plan_path = attempt_dir.join("reserve-plan-v3.bin");
    let reserve_view_bytes = operator.tool(
        "inspect",
        "application-agent-lifetime-reserve-plan",
        &reserve_plan_path,
        &attempt_dir.join("reserve-plan-paid-v3.json"),
    )?;
    let reserve_view: Value = serde_json::from_slice(&reserve_view_bytes)?;
    if reserve_view.get("canonicalPlanHex").and_then(Value::as_str)
        != Some(hex(&reserve.plan_bytes).as_str())
    {
        return Err(refused(
            "lifetime retained reserve plan differs from source",
        ));
    }
    let paid_json = json!({
        "fixedRequestHex":hex(&reserve.request_bytes),
        "contextHex":hex(&reserve.context_bytes),
        "reserveIndex":reserve.reserve_index,
    });
    let paid_json_path = write_new(
        attempt_dir,
        "paid-request-v3.json",
        &serde_json::to_vec(&paid_json)?,
    )?;
    let paid_request = operator.tool(
        "author",
        "application-agent-lifetime-paid-request",
        &paid_json_path,
        &attempt_dir.join("paid-request-v3.bin"),
    )?;
    let request_path = attempt_dir.join("paid-request-v3.bin");
    let request_view_bytes = operator.tool(
        "inspect",
        "application-agent-lifetime-paid-request",
        &request_path,
        &attempt_dir.join("paid-request-v3-inspected.json"),
    )?;
    let request_view: Value = serde_json::from_slice(&request_view_bytes)?;
    if request_view.get("type").and_then(Value::as_str)
        != Some("application-agent-lifetime-paid-request-v3")
        || request_view
            .get("canonicalRequestHex")
            .and_then(Value::as_str)
            != Some(hex(&paid_request).as_str())
        || request_view.get("contextHex").and_then(Value::as_str)
            != Some(hex(&reserve.context_bytes).as_str())
        || request_view.get("reserveIndex").and_then(Value::as_str)
            != Some(reserve.reserve_index.as_str())
    {
        return Err(refused("lifetime paid request source projection drift"));
    }
    let plan = retained_source_payload(operator, attempt_dir, "paid-plan-v3",
        crate::host_operations::AGENT_LIFETIME_DISPATCH_PLAN,
        &operator.invoke(crate::host_operations::AGENT_LIFETIME_DISPATCH_PLAN, &paid_request)?)?;
    let plan_path = write_new(attempt_dir, "paid-plan-v3.bin", &plan)?;
    let inspection_bytes = operator.tool(
        "inspect",
        "application-agent-lifetime-paid-plan",
        &plan_path,
        &attempt_dir.join("paid-plan-v3.json"),
    )?;
    let inspection: Value = serde_json::from_slice(&inspection_bytes)?;
    if inspection.get("canonicalPlanHex").and_then(Value::as_str) != Some(hex(&plan).as_str()) {
        return Err(refused("lifetime paid plan source projection drift"));
    }
    let payer = reverse.sign_payer_once(reserve, &plan, &inspection, cancelled, deadline)?;
    match_paid_plan(
        binding,
        &reserve.current_claims,
        &reserve_view,
        &inspection,
        &reserve.reserve_index,
        &reserve.reserve_receipt,
        &payer.signed_post_reserve_purse_physical_root,
    )?;
    custody.verify_payer_slots(&inspection, &plan, &payer.signatures)?;
    if cancelled.load(Ordering::Acquire) {
        return Err(refused("lifetime caller cancelled before paid assembly"));
    }
    let app = custody.sign_app_slots(&inspection, &plan)?;
    let grant = custody.sign_grant_slot(&inspection, &plan)?;
    let app_binary = signatures(operator, attempt_dir, "app-signatures-v3", &app)?;
    let payer_binary = signatures(
        operator,
        attempt_dir,
        "payer-signatures-v3",
        &json!(payer.signatures),
    )?;
    let detached = pair(&app_binary, &pair(&grant, &payer_binary)?)?;
    let ingress = retained_source_payload(operator, attempt_dir, "paid-ingress-v3",
        crate::host_operations::AGENT_LIFETIME_DISPATCH_ASSEMBLE,
        &operator.invoke(crate::host_operations::AGENT_LIFETIME_DISPATCH_ASSEMBLE, &pair(&plan, &detached)?)?)?;
    write_new(attempt_dir, "paid-ingress-v3.bin", &ingress)?;
    write_new(
        attempt_dir,
        "paid-assembled-v3.json",
        &serde_json::to_vec(&json!({
            "protocol":"mini-spk-lifetime-paid-assembled-v3",
            "bindingSha256":reserve.binding_sha256,
            "operationFingerprint":reserve.operation_fingerprint,
            "planSha256":hex(&Sha256::digest(&plan)),
            "ingressSha256":hex(&Sha256::digest(&ingress)),
            "signedPostReservePursePhysicalRoot":payer.signed_post_reserve_purse_physical_root,
        }))?,
    )?;
    Ok(AssembledLifetimePaidV3 {
        plan,
        ingress,
        inspection,
        signed_post_reserve_purse_physical_root: payer.signed_post_reserve_purse_physical_root,
    })
}

#[cfg(test)]
mod tests {
    use super::{pair, source_payload};

    #[test]
    fn op79_detached_signature_pair_keeps_grant_between_app_and_payer() {
        let grant = [7u8; 64];
        let nested = pair(b"app", &pair(&grant, b"payer").unwrap()).unwrap();
        assert_eq!(u32::from_le_bytes(nested[..4].try_into().unwrap()), 3);
        assert_eq!(&nested[4..7], b"app");
        assert_eq!(u32::from_le_bytes(nested[7..11].try_into().unwrap()), 64);
        assert_eq!(&nested[11..75], &grant);
        assert_eq!(&nested[75..], b"payer");
    }

    #[test]
    fn native_reply_must_be_exact_op_and_frame() {
        let mut reply = [0u8; 7];
        reply[..4].copy_from_slice(&3u32.to_le_bytes());
        reply[4] = 79;
        reply[5..].copy_from_slice(b"ok");
        assert_eq!(source_payload(&reply, crate::host_operations::AGENT_LIFETIME_DISPATCH_ASSEMBLE).unwrap(), b"ok");
        assert!(source_payload(&reply, crate::host_operations::AGENT_LIFETIME_DISPATCH_PLAN).is_err());
        reply[0] = 4;
        assert!(source_payload(&reply, crate::host_operations::AGENT_LIFETIME_DISPATCH_ASSEMBLE).is_err());
    }
}
