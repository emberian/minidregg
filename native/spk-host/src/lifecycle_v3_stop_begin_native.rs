//! Source-authored STOP Plan-v2, detached BEGIN, and one-shot event23 receipt.
#![allow(dead_code)] // Awaiting the callable STOP supervisor cut.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_v3_native::{decimal, framed_payload, hex, sign_pinned_slots, text};
use crate::lifecycle_v3_stop_claim_native::ExactReceipt;
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
const STOP_PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LAUNCH-STOP-OPERATOR-PLAN/v2";
const BEGIN_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-BEGIN-INGRESS/v3";
const OUTCOME_TAG: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v4";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedStopBeginSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl FixedStopBeginSigners {
    fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-begin-management-v1" {
            return Err(invalid("STOP BEGIN fixed management custody refused"));
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

pub(crate) struct AcceptedStopBegin {
    stop_plan: Vec<u8>,
    ingress: Vec<u8>,
    receipt: ExactReceipt,
    client_operation_id: String,
    authorization_operation_id: String,
    process_generation: String,
    volume_id_hex: String,
}

impl AcceptedStopBegin {
    pub(crate) fn stop_plan(&self) -> &[u8] {
        &self.stop_plan
    }
    pub(crate) fn ingress(&self) -> &[u8] {
        &self.ingress
    }
    pub(crate) fn receipt(&self) -> &ExactReceipt {
        &self.receipt
    }
    pub(crate) fn client_operation_id(&self) -> &str {
        &self.client_operation_id
    }
    pub(crate) fn authorization_operation_id(&self) -> &str {
        &self.authorization_operation_id
    }
    pub(crate) fn process_generation(&self) -> &str {
        &self.process_generation
    }
    pub(crate) fn volume_id_hex(&self) -> &str {
        &self.volume_id_hex
    }
}

fn checked_plan<'a>(
    inspected: &'a Value,
    plan: &[u8],
    request: &[u8],
    client_operation_id: &str,
    launch: &SourceBoundLaunch<'_>,
    fixed: &FixedStopBeginSigners,
) -> io::Result<&'a [Value]> {
    let base = inspected
        .get("basePlan")
        .ok_or_else(|| invalid("STOP BEGIN base plan absent"))?;
    let request_view = base
        .get("request")
        .ok_or_else(|| invalid("STOP BEGIN request projection absent"))?;
    if text(inspected, "type")? != "application-lifecycle-launch-stop-plan-v2"
        || text(inspected, "canonicalPlanHex")? != hex(plan)
        || text(inspected, "canonicalRequestHex")? != hex(request)
        || text(base, "type")? != "application-lifecycle-launch-begin-plan-v1"
        || text(base, "canonicalRequestHex")? != hex(request)
        || text(request_view, "kind")? != "stop"
        || text(request_view, "clientOperationId")? != client_operation_id
        || text(request_view, "descriptorHex")? != hex(&launch.descriptor().canonical)
        || text(base, "descriptorRoot")? != launch.descriptor().root
        || text(base, "app")? != fixed.selector.app
        || text(base, "packageManifest")? != fixed.selector.package_manifest
        || text(base, "snapshotManifest")? != fixed.selector.snapshot_manifest
        || text(base, "managementSubject")? != fixed.management_subject
        || !decimal(text(base, "authorizationOperationId")?)
        || !decimal(text(base, "worldRoot")?)
        || !decimal(text(base, "height")?)
        || base.get("selectedCommandDigest") != Some(&Value::Null)
        || base.get("priorCreate") != Some(&Value::Null)
    {
        return Err(invalid("STOP BEGIN plan differs from selected signed SPK"));
    }
    base.get("slots")
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| invalid("STOP BEGIN signing slots absent"))
}

/// One current-image op66/67 and one signed event23 submit. Every response
/// and marker is retained in an owner-private directory. An uncertain op22
/// result cannot be retried through this function; inspect exact historical
/// receipt using the original ingress instead.
pub(crate) fn submit_once(
    operator: &PrivateOperator,
    fixed: &FixedStopBeginSigners,
    app_uid: u32,
    launch: &SourceBoundLaunch<'_>,
    nonce_ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AcceptedStopBegin> {
    fixed.validate(operator, app_uid)?;
    let descriptor = &launch.descriptor().canonical;
    if descriptor.is_empty() || descriptor.len() >= MAX_FRAME {
        return Err(invalid("STOP BEGIN signed descriptor size refused"));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("STOP BEGIN attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let client_operation_id = allocate_operation_id(nonce_ledger)?;
    let source = json!({
        "kind":"stop",
        "clientOperationId":client_operation_id,
        "descriptor":hex(descriptor),
        "createIndex":Value::Null,
    });
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        "application-lifecycle-launch-begin-request",
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    let active = json!({
        "protocol":"mini-spk-stop-begin-op66-requested-v1",
        "clientOperationId":client_operation_id,
        "requestSha256":hex(&Sha256::digest(&request)),
        "descriptorSha256":hex(&Sha256::digest(descriptor)),
    });
    let active_bytes = serde_json::to_vec(&active)?;
    write_new(attempt_dir, "op66-requested.json", &active_bytes)?;
    write_new(parent, "lifecycle-stop-begin-v3-active.json", &active_bytes)?;
    let reply = operator.invoke(66, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op66-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 66, STOP_PLAN_TAG)?.to_vec();
    let plan_path = write_new(attempt_dir, "stop-plan-v2.bin", &plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-launch-stop-plan",
        &plan_path,
        &attempt_dir.join("stop-plan-v2.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let slots = checked_plan(&view, &plan, &request, &client_operation_id, launch, fixed)?;
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
    write_new(attempt_dir, "op67-requested.bin", &pair)?;
    let reply = operator.invoke(67, &pair)?;
    write_new(attempt_dir, "op67-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 67, BEGIN_TAG)?.to_vec();
    write_new(attempt_dir, "begin-v3.bin", &ingress)?;
    let base = view
        .get("basePlan")
        .ok_or_else(|| invalid("STOP BEGIN base plan disappeared"))?;
    let submit_marker = json!({
        "protocol":"mini-spk-stop-begin-op22-requested-v1",
        "clientOperationId":client_operation_id,
        "authorizationOperationId":text(base, "authorizationOperationId")?,
        "ingressSha256":hex(&Sha256::digest(&ingress)),
    });
    write_new(
        attempt_dir,
        "op22-requested.json",
        &serde_json::to_vec(&submit_marker)?,
    )?;
    let reply = operator.invoke(22, &ingress)?;
    write_new(attempt_dir, "op22-frame.bin", &reply)?;
    let outcome = framed_payload(&reply, 22, OUTCOME_TAG)?;
    let outcome_path = write_new(attempt_dir, "op22-outcome.bin", outcome)?;
    let result = operator.tool(
        "inspect",
        "outcome",
        &outcome_path,
        &attempt_dir.join("op22-outcome.json"),
    )?;
    let result: Value = serde_json::from_slice(&result)?;
    if text(&result, "type")? != "confirmed" || text(&result, "confirmation")? != "installed" {
        return Err(invalid("STOP BEGIN was not freshly installed"));
    }
    let receipt = ExactReceipt::new(
        text(&result, "transactionId")?,
        text(&result, "eventId")?,
        text(&result, "acceptedCount")?,
        text(&result, "worldRoot")?,
    )?;
    Ok(AcceptedStopBegin {
        stop_plan: plan,
        ingress,
        receipt,
        client_operation_id,
        authorization_operation_id: text(base, "authorizationOperationId")?.to_owned(),
        process_generation: text(base, "processGeneration")?.to_owned(),
        volume_id_hex: text(base, "volumeIdHex")?.to_owned(),
    })
}
