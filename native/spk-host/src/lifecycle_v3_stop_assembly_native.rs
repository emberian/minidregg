//! Current-image STOP claim plan and detached assembly, before fresh op26.
#![allow(dead_code)] // Awaiting the callable STOP supervisor cut.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text,
};
use crate::lifecycle_v3_stop_begin_native::AcceptedStopBegin;
use crate::lifecycle_v3_stop_claim_native::{self, FreshStopClaim};
use crate::resident_begin_native::allocate_operation_id;
use crate::resident_launch::SourceBoundLaunch;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::DirBuilder;
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::Path;

const MAX_FRAME: usize = 12_102_760;
const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LAUNCH-CLAIM-OPERATOR-PLAN/v1";
const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-INGRESS/v3";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn previous_index(count: &str) -> io::Result<String> {
    if !decimal(count) || count == "0" {
        return Err(invalid("STOP claim original BEGIN count refused"));
    }
    let mut bytes = count.as_bytes().to_vec();
    for byte in bytes.iter_mut().rev() {
        if *byte != b'0' {
            *byte -= 1;
            break;
        }
        *byte = b'9';
    }
    let first = bytes
        .iter()
        .position(|byte| *byte != b'0')
        .unwrap_or(bytes.len() - 1);
    String::from_utf8(bytes[first..].to_vec())
        .map_err(|_| invalid("STOP claim original index malformed"))
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedStopClaimSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl FixedStopClaimSigners {
    fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-claim-management-v1" {
            return Err(invalid("STOP claim fixed management custody refused"));
        }
        crate::lifecycle_selector::validate_custody(
            operator,
            &self.selector,
            &self.management_subject,
            &self.signers,
            app_uid,
        )
    }
}

pub(crate) struct AssembledStopClaim {
    begin: AcceptedStopBegin,
    ingress: Vec<u8>,
}

impl AssembledStopClaim {
    pub(crate) fn ingress(&self) -> &[u8] {
        &self.ingress
    }
    pub(crate) fn begin(&self) -> &AcceptedStopBegin {
        &self.begin
    }
}

struct ClaimPlanEvidence<'a> {
    plan: &'a [u8],
    request: &'a [u8],
    begin: &'a AcceptedStopBegin,
    original_index: &'a str,
    query_nonce: &'a str,
    launch: &'a SourceBoundLaunch<'a>,
    fixed: &'a FixedStopClaimSigners,
}

fn checked_plan<'a>(view: &'a Value, evidence: &ClaimPlanEvidence<'_>) -> io::Result<&'a [Value]> {
    let ClaimPlanEvidence {
        plan,
        request,
        begin,
        original_index,
        query_nonce,
        launch,
        fixed,
    } = evidence;
    if text(view, "type")? != "application-lifecycle-launch-claim-plan-v1"
        || text(view, "canonicalPlanHex")? != hex(plan)
        || text(view, "canonicalRequestHex")? != hex(request)
        || text(view, "originalBeginHex")? != hex(begin.ingress())
        || text(view, "descriptorHex")? != hex(&launch.descriptor().canonical)
        || text(view, "descriptorRoot")? != launch.descriptor().root
        || text(view, "volumeIdHex")? != begin.volume_id_hex()
        || text(view, "clientOperationId")? != begin.client_operation_id()
        || text(view, "authorizationOperationId")? != begin.authorization_operation_id()
        || text(view, "originalIndex")? != *original_index
        || text(view, "queryNonce")? != *query_nonce
        || text(view, "app")? != fixed.selector.app
        || text(view, "managementSubject")? != fixed.management_subject
        || text(view, "originalBeginTransactionId")? != begin.receipt().transaction_id()
        || text(view, "originalBeginEventId")? != begin.receipt().event_id()
        || text(view, "originalBeginAcceptedCount")? != begin.receipt().accepted_count()
        || text(view, "originalBeginWorldRoot")? != begin.receipt().world_root()
        || !lowercase_hex(text(view, "originalBeginReceiptHex")?)
        || text(view, "originalBeginReceiptHex")?.is_empty()
        || !lowercase_hex(text(view, "sourceHex")?)
        || text(view, "sourceHex")?.is_empty()
        || !decimal(text(view, "currentAppRoot")?)
        || !decimal(text(view, "currentPackageRoot")?)
        || !decimal(text(view, "currentWorldRoot")?)
        || !decimal(text(view, "worldRoot")?)
        || !decimal(text(view, "height")?)
        || view.get("binding") != Some(&Value::Null)
    {
        return Err(invalid("STOP claim plan differs from accepted STOP BEGIN"));
    }
    view.get("slots")
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| invalid("STOP claim signing slots absent"))
}

/// Author the claim only after a confirmed original STOP BEGIN. Current-image
/// op68 derives the original receipt and roots; Rust checks its inspection and
/// signs only pinned credential headers. This does not submit op26 or arm STOP.
pub(crate) fn assemble_once(
    operator: &PrivateOperator,
    fixed: &FixedStopClaimSigners,
    app_uid: u32,
    begin: AcceptedStopBegin,
    launch: &SourceBoundLaunch<'_>,
    nonce_ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AssembledStopClaim> {
    fixed.validate(operator, app_uid)?;
    if begin.ingress().is_empty() || begin.ingress().len() >= MAX_FRAME {
        return Err(invalid("STOP claim original BEGIN size refused"));
    }
    let original_index = previous_index(begin.receipt().accepted_count())?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("STOP claim assembly parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let query_nonce = allocate_operation_id(nonce_ledger)?;
    let source = json!({"originalIndex":original_index,"queryNonce":query_nonce});
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        "application-lifecycle-launch-claim-request",
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    let marker = json!({
        "protocol":"mini-spk-stop-claim-op68-requested-v1",
        "originalIndex":original_index,
        "queryNonce":query_nonce,
        "requestSha256":hex(&Sha256::digest(&request)),
        "originalBeginSha256":hex(&Sha256::digest(begin.ingress())),
    });
    let marker = serde_json::to_vec(&marker)?;
    write_new(attempt_dir, "op68-requested.json", &marker)?;
    write_new(parent, "lifecycle-stop-claim-assembly-active.json", &marker)?;
    let reply = operator.invoke(68, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op68-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 68, PLAN_TAG)?.to_vec();
    let plan_path = write_new(attempt_dir, "plan.bin", &plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-launch-claim-plan",
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let slots = checked_plan(
        &view,
        &ClaimPlanEvidence {
            plan: &plan,
            request: &request,
            begin: &begin,
            original_index: &original_index,
            query_nonce: &query_nonce,
            launch,
            fixed,
        },
    )?;
    let signatures = sign_pinned_slots(slots, &fixed.signers)?;
    let signatures_path = write_new(
        attempt_dir,
        "signatures.json",
        &serde_json::to_vec(&signatures)?,
    )?;
    let encoded = operator.tool(
        "signatures",
        "",
        &signatures_path,
        &attempt_dir.join("signatures.bin"),
    )?;
    let mut pair = Vec::with_capacity(4 + plan.len() + encoded.len());
    pair.extend_from_slice(&(plan.len() as u32).to_le_bytes());
    pair.extend_from_slice(&plan);
    pair.extend_from_slice(&encoded);
    write_new(attempt_dir, "op69-requested.bin", &pair)?;
    let reply = operator.invoke(69, &pair)?;
    write_new(attempt_dir, "op69-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 69, INGRESS_TAG)?.to_vec();
    write_new(attempt_dir, "claim-v3.bin", &ingress)?;
    Ok(AssembledStopClaim { begin, ingress })
}

/// The sole composition into the sealed fresh claim. The distinct op26
/// attempt directory is one-shot; historical op27 lookup has no path here.
pub(crate) fn submit_fresh_once(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    assembled: AssembledStopClaim,
) -> io::Result<FreshStopClaim> {
    lifecycle_v3_stop_claim_native::submit_once(
        operator,
        attempt_dir,
        assembled.begin.stop_plan(),
        assembled.begin.ingress(),
        &assembled.ingress,
        assembled.begin.receipt().clone(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stop_original_index_is_canonical() {
        assert_eq!(previous_index("1").unwrap(), "0");
        assert_eq!(previous_index("1000").unwrap(), "999");
        assert!(previous_index("0").is_err());
        assert!(previous_index("01").is_err());
    }
}
