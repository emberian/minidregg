//! A fresh, source-inspected STOP claim. Receipt-only recovery cannot create one.
//!
//! This module does not fence or stop a unit. The physical path must join this
//! sealed claim to the retained Running journal and volume witness, durably
//! mark the attempt, and perform the checked manager action under that lock.
#![allow(dead_code)] // The callable STOP supervisor is a later, separate cut.

use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::lifecycle_v3_native::{decimal, framed_payload, hex};
use crate::lifecycle_v3_stop_native::{ReceiptFields, StopTarget};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::path::Path;
use std::process::{Command, Stdio};

const COMMITTED_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v3";
const MAX_FRAME: usize = 12_102_760;
const MAX_INSPECTION: u64 = 2 * 1024 * 1024;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// Exact native four-field receipt, with no independent authority to stop.
#[derive(Clone)]
pub(crate) struct ExactReceipt {
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    world_root: String,
}

impl ExactReceipt {
    pub(crate) fn new(
        transaction_id: &str,
        event_id: &str,
        accepted_count: &str,
        world_root: &str,
    ) -> io::Result<Self> {
        if [transaction_id, event_id, accepted_count, world_root]
            .iter()
            .any(|value| !decimal(value))
            || accepted_count == "0"
        {
            return Err(invalid("STOP receipt fields are not canonical"));
        }
        Ok(Self {
            transaction_id: transaction_id.to_owned(),
            event_id: event_id.to_owned(),
            accepted_count: accepted_count.to_owned(),
            world_root: world_root.to_owned(),
        })
    }

    fn from_source(value: &Value) -> io::Result<Self> {
        let field = |name| -> io::Result<&str> {
            value
                .get(name)
                .and_then(Value::as_str)
                .ok_or_else(|| invalid("STOP committed receipt field absent"))
        };
        Self::new(
            field("transactionId")?,
            field("eventId")?,
            field("acceptedCount")?,
            field("worldRoot")?,
        )
    }

    fn borrowed(&self) -> ReceiptFields<'_> {
        ReceiptFields {
            transaction_id: &self.transaction_id,
            event_id: &self.event_id,
            accepted_count: &self.accepted_count,
            world_root: &self.world_root,
        }
    }

    pub(crate) fn transaction_id(&self) -> &str {
        &self.transaction_id
    }
    pub(crate) fn event_id(&self) -> &str {
        &self.event_id
    }
    pub(crate) fn accepted_count(&self) -> &str {
        &self.accepted_count
    }
    pub(crate) fn world_root(&self) -> &str {
        &self.world_root
    }
}

/// The constructor is deliberately private. The only producer below invokes
/// op26 once and accepts its fresh committed callback, never op27 or an
/// already-present/replayed outcome. A current source inspection then binds
/// the exact retained STOP plan, original BEGIN, both receipts and claim.
pub(crate) struct FreshStopClaim {
    target: StopTarget,
    stop_plan: Vec<u8>,
    original_begin: Vec<u8>,
    claim_ingress: Vec<u8>,
    committed_frame: Vec<u8>,
    inspection: Vec<u8>,
    begin_receipt: ExactReceipt,
    claim_receipt: ExactReceipt,
}

impl FreshStopClaim {
    pub(crate) fn target(&self) -> &StopTarget {
        &self.target
    }
    pub(crate) fn stop_plan(&self) -> &[u8] {
        &self.stop_plan
    }
    pub(crate) fn original_begin(&self) -> &[u8] {
        &self.original_begin
    }
    pub(crate) fn claim_ingress(&self) -> &[u8] {
        &self.claim_ingress
    }
    pub(crate) fn committed_frame(&self) -> &[u8] {
        &self.committed_frame
    }
    pub(crate) fn inspection(&self) -> &[u8] {
        &self.inspection
    }
    pub(crate) fn begin_receipt(&self) -> &ExactReceipt {
        &self.begin_receipt
    }
    pub(crate) fn claim_receipt(&self) -> &ExactReceipt {
        &self.claim_receipt
    }
}

fn read_inspection(path: &Path) -> io::Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.len() == 0
        || metadata.len() > MAX_INSPECTION
    {
        return Err(invalid("STOP source inspection identity or size refused"));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    File::open(path)?
        .take(MAX_INSPECTION + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != metadata.len() {
        return Err(invalid("STOP source inspection changed during read"));
    }
    Ok(bytes)
}

fn committed_source_receipt(
    view: &Value,
    committed: &[u8],
    claim_ingress: &[u8],
    original_begin: &[u8],
) -> io::Result<ExactReceipt> {
    let field = |name| -> io::Result<&str> {
        view.get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("STOP committed source inspection field absent"))
    };
    if field("type")? != "application-lifecycle-claim-committed-v3"
        || field("kind")? != "stop"
        || field("frameHex")? != hex(committed)
        || field("frameByteCount")? != committed.len().to_string()
        || field("originalClaimHex")? != hex(claim_ingress)
        || field("originalBeginHex")? != hex(original_begin)
    {
        return Err(invalid("STOP committed frame differs from original claim"));
    }
    let receipt = ExactReceipt::from_source(
        view.get("receipt")
            .ok_or_else(|| invalid("STOP committed source receipt absent"))?,
    )?;
    if field("postWorldRoot")? != receipt.world_root {
        return Err(invalid("STOP committed post-world root differs"));
    }
    Ok(receipt)
}

/// One durable attempt. An error after the pre-submit marker, including a
/// truncated/uncertain response or a later read-only inspection refusal,
/// leaves the exact bytes for receipt-only investigation. It must not be
/// reentered or translated into a fresh claim from historical lookup.
pub(crate) fn submit_once(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    retained_stop_plan: &[u8],
    original_begin: &[u8],
    claim_ingress: &[u8],
    begin_receipt: ExactReceipt,
) -> io::Result<FreshStopClaim> {
    if [retained_stop_plan, original_begin, claim_ingress]
        .iter()
        .any(|value| value.is_empty() || value.len() >= MAX_FRAME)
    {
        return Err(invalid("STOP retained input size refused"));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("STOP claim attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let plan_path = write_new(attempt_dir, "stop-plan-v2.bin", retained_stop_plan)?;
    let _ = write_new(attempt_dir, "original-begin-v3.bin", original_begin)?;
    let _ = write_new(attempt_dir, "claim-ingress-v3.bin", claim_ingress)?;
    // Refuse a non-STOP or noncanonical plan before attempting any Store write.
    // Current-image agreement is checked again after the fresh callback.
    let plan_inspection = operator.tool(
        "inspect",
        "application-lifecycle-launch-stop-plan",
        &plan_path,
        &attempt_dir.join("stop-plan-v2.json"),
    )?;
    let plan_view: Value = serde_json::from_slice(&plan_inspection)?;
    if plan_view.get("type").and_then(Value::as_str)
        != Some("application-lifecycle-launch-stop-plan-v2")
        || plan_view.get("canonicalPlanHex").and_then(Value::as_str)
            != Some(hex(retained_stop_plan).as_str())
        || plan_view
            .get("basePlan")
            .and_then(|base| base.get("request"))
            .and_then(|request| request.get("kind"))
            .and_then(Value::as_str)
            != Some("stop")
    {
        return Err(invalid("STOP source plan preflight refused"));
    }
    let marker = json!({
        "protocol":"mini-spk-stop-claim-op26-requested-v1",
        "stopPlanSha256":hex(&Sha256::digest(retained_stop_plan)),
        "originalBeginSha256":hex(&Sha256::digest(original_begin)),
        "claimIngressSha256":hex(&Sha256::digest(claim_ingress)),
        "beginReceipt":{
            "transactionId":begin_receipt.transaction_id(),
            "eventId":begin_receipt.event_id(),
            "acceptedCount":begin_receipt.accepted_count(),
            "worldRoot":begin_receipt.world_root(),
        }
    });
    write_new(
        attempt_dir,
        "op26-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    // This parent-level marker bars a second attempt in the same journal even
    // if the callback is lost. It is distinct from the later physical fence.
    write_new(
        parent,
        "lifecycle-stop-claim-v3-active.json",
        &serde_json::to_vec(&marker)?,
    )?;

    let response = operator.invoke(26, claim_ingress)?;
    write_new(attempt_dir, "op26-frame.bin", &response)?;
    // Only the pinned Host's fresh installed CAS-winner path emits this tag;
    // replay and op27 return a distinct receipt-only Outcome. Retain first.
    let committed = framed_payload(&response, 26, COMMITTED_TAG)?.to_vec();
    let committed_path = write_new(attempt_dir, "committed-v3.bin", &committed)?;
    let committed_json = operator.tool(
        "inspect",
        "application-lifecycle-claim-committed-v3",
        &committed_path,
        &attempt_dir.join("committed-v3.json"),
    )?;
    let committed_view: Value = serde_json::from_slice(&committed_json)?;
    let claim_receipt =
        committed_source_receipt(&committed_view, &committed, claim_ingress, original_begin)?;

    // This Host CLI reopens the current verified image. Its output cannot be
    // substituted by a caller-supplied JSON file or a stale op27 lookup.
    let _ = operator.pinned_config()?;
    let inspection_path = attempt_dir.join("stop-claim-current.json");
    let status = Command::new(&operator.host)
        .arg(&operator.config)
        .arg("inspect-stop-claim")
        .arg(&plan_path)
        .arg(&committed_path)
        .arg(&inspection_path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?;
    if !status.success() {
        return Err(invalid("pinned Mini Host STOP current inspection refused"));
    }
    let inspection = read_inspection(&inspection_path)?;
    let target = StopTarget::from_verified_inspection(
        retained_stop_plan,
        &committed,
        original_begin,
        &inspection,
        begin_receipt.borrowed(),
        claim_receipt.borrowed(),
    )?;
    Ok(FreshStopClaim {
        target,
        stop_plan: retained_stop_plan.to_vec(),
        original_begin: original_begin.to_vec(),
        claim_ingress: claim_ingress.to_vec(),
        committed_frame: committed,
        inspection,
        begin_receipt,
        claim_receipt,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn receipt_fields_require_canonical_positive_count() {
        assert!(ExactReceipt::new("1", "2", "3", "4").is_ok());
        assert!(ExactReceipt::new("01", "2", "3", "4").is_err());
        assert!(ExactReceipt::new("1", "2", "0", "4").is_err());
    }

    #[test]
    fn committed_inspection_binds_exact_originals() {
        let frame = b"frame";
        let claim = b"claim";
        let begin = b"begin";
        let source = json!({
            "type":"application-lifecycle-claim-committed-v3",
            "kind":"stop",
            "frameHex":hex(frame),
            "frameByteCount":frame.len().to_string(),
            "originalClaimHex":hex(claim),
            "originalBeginHex":hex(begin),
            "postWorldRoot":"4",
            "receipt":{"transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"}
        });
        assert!(committed_source_receipt(&source, frame, claim, begin).is_ok());
        assert!(committed_source_receipt(&source, frame, b"changed", begin).is_err());
        assert!(committed_source_receipt(&source, frame, claim, b"changed").is_err());
    }

    #[test]
    fn historical_outcome_cannot_be_fresh_callback() {
        let mut reply = Vec::new();
        let payload = b"DREGG/NATIVE-HOST/OUTCOME/v5:replayed";
        reply.extend_from_slice(&(payload.len() as u32 + 1).to_le_bytes());
        reply.push(26);
        reply.extend_from_slice(payload);
        assert!(framed_payload(&reply, 26, COMMITTED_TAG).is_err());
        reply[4] = 27;
        assert!(framed_payload(&reply, 26, COMMITTED_TAG).is_err());
    }
}
