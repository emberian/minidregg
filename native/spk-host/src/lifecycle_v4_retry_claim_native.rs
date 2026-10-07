//! Governed repeat-CREATE CLAIM (event70), modeled line by line on
//! `lifecycle_v3_claim_native`. op68 plan / op69 assemble / op26 submit with
//! the fresh-tip committed v4 projection / op27 receipt-only lookup. The
//! claim consumes the one-use retry token; it never clears the v3
//! first-attempt marker. Only a fresh op26 committed projection can arm the
//! physical launch, exactly as in v3.
use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::VerifiedBegin;
use crate::lifecycle_v3_claim_native::{later_decimal, CommittedLaunchClaim};
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text, AcceptedLaunchBegin,
    LaunchBeginAction,
};
use crate::lifecycle_receipt_lookup::{lookup_retained, retained_submitted_ingress, RecoveredReceipt};
use crate::lifecycle_v4_retry_native::{
    checked_retry_fields, decimal_predecessor, encode_nat_decimal, RetrySelection, BEGIN_TAG,
};
use crate::operation_ledger::allocate_operation_id;
use crate::resident_launch::SourceBoundLaunch;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder};
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

/// Host/ApplicationLifecycleRetryClaimV4Authoring.lean:39-40 (requestCodec frame).
pub(crate) const REQUEST_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-CLAIM-OPERATOR-REQUEST/v4";
/// CONTRACT-V4-WIRE op68 plan frame.
const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-CLAIM-OPERATOR-PLAN/v4";
/// Kernel/ApplicationLifecycleRetryClaimV4Ingress.lean:28-29.
pub(crate) const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-CLAIM-INGRESS/v4";
/// Kernel/ApplicationLifecycleRetryClaimV4Projection.lean:34.
pub(crate) const COMMITTED_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-CLAIM-COMMITTED/v4";

const REQUEST_INSPECT_KIND: &str = "application-lifecycle-retry-claim-request";
const PLAN_INSPECT_KIND: &str = "application-lifecycle-retry-claim-plan";
pub(crate) const COMMITTED_INSPECT_KIND: &str = "application-lifecycle-claim-committed-v4";
const REQUEST_VIEW_TYPE: &str = "application-lifecycle-retry-claim-request-v4";
const PLAN_VIEW_TYPE: &str = "application-lifecycle-retry-claim-plan-v4";
pub(crate) const COMMITTED_VIEW_TYPE: &str = "application-lifecycle-claim-committed-v4";

pub(crate) const ACTIVE_MARKER: &str = "lifecycle-claim-retry-v4-active.json";
pub(crate) const CLAIM_ATTEMPT_DIR: &str = "claim-author-attempt-retry-v4";
pub(crate) const CLAIM_INGRESS_FILE: &str = "claim-retry-v4.bin";
pub(crate) const COMMITTED_FILE: &str = "committed-retry-v4.bin";
pub(crate) const COMMITTED_INSPECTION_FILE: &str = "committed-retry-v4.json";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

/// `requestCodec` (Host/ApplicationLifecycleRetryClaimV4Authoring.lean:33-40):
/// `REQUEST_TAG ++ nat originalIndex ++ nat queryNonce`.
pub(crate) fn request_bytes(original_index: &str, query_nonce: &str) -> io::Result<Vec<u8>> {
    let mut request = REQUEST_TAG.to_vec();
    request.extend_from_slice(&encode_nat_decimal(original_index)?);
    request.extend_from_slice(&encode_nat_decimal(query_nonce)?);
    Ok(request)
}

/// Same custody file and protocol as the v3 claim signers.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedRetryClaimSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

struct ClaimPlanEvidence<'a> {
    plan: &'a [u8],
    request: &'a [u8],
    begin: &'a AcceptedLaunchBegin,
    launch: &'a SourceBoundLaunch<'a>,
    original_index: &'a str,
    query_nonce: &'a str,
}

fn create_index(begin: &AcceptedLaunchBegin) -> io::Result<usize> {
    match begin.action {
        LaunchBeginAction::Create(index) if begin.prior_create.is_none() => Ok(index),
        _ => Err(invalid("v4 retry claim requires a repeat CREATE BEGIN")),
    }
}

fn checked_create_binding(
    binding: &Value,
    index: usize,
    launch: &SourceBoundLaunch<'_>,
) -> io::Result<()> {
    let selected = launch
        .descriptor()
        .create_digests
        .get(index)
        .ok_or_else(|| invalid("v4 retry claim create index absent"))?;
    if text(binding, "choice")? != "create"
        || text(binding, "createIndex")? != index.to_string()
        || text(binding, "commandDigest")? != selected
        || binding.get("priorCreate") != Some(&Value::Null)
    {
        return Err(invalid("v4 retry claim create choice differs from signed SPK"));
    }
    Ok(())
}

impl FixedRetryClaimSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-resident-claim-management-v1" {
            return Err(invalid("v4 retry claim fixed management custody refused"));
        }
        crate::lifecycle_selector::validate_custody(
            operator,
            &self.selector,
            &self.management_subject,
            &self.signers,
            app_uid,
        )
    }

    fn checked_plan_slots<'a>(
        &self,
        view: &'a Value,
        evidence: &ClaimPlanEvidence<'_>,
    ) -> io::Result<&'a [Value]> {
        let ClaimPlanEvidence {
            plan,
            request,
            begin,
            launch,
            original_index,
            query_nonce,
        } = evidence;
        let descriptor = launch.descriptor();
        if text(view, "type")? != PLAN_VIEW_TYPE
            || text(view, "canonicalPlanHex")? != hex(plan)
            || text(view, "canonicalRequestHex")? != hex(request)
            || text(view, "originalBeginHex")? != hex(&begin.ingress)
            || text(view, "descriptorHex")? != hex(&descriptor.canonical)
            || text(view, "descriptorRoot")? != descriptor.root
            || text(view, "volumeIdHex")? != begin.volume_id_hex
            || text(view, "clientOperationId")? != begin.client_operation_id
            || text(view, "authorizationOperationId")? != begin.authorization_operation_id
            || text(view, "originalIndex")? != *original_index
            || text(view, "queryNonce")? != *query_nonce
            || text(view, "app")? != self.selector.app
            || text(view, "managementSubject")? != self.management_subject
            || text(view, "originalBeginTransactionId")? != begin.transaction_id
            || text(view, "originalBeginEventId")? != begin.event_id
            || text(view, "originalBeginAcceptedCount")? != begin.accepted_count
            || text(view, "originalBeginWorldRoot")? != begin.world_root
            || !lowercase_hex(text(view, "originalBeginReceiptHex")?)
            || text(view, "originalBeginReceiptHex")?.is_empty()
            || !lowercase_hex(text(view, "sourceHex")?)
            || text(view, "sourceHex")?.is_empty()
            || !decimal(text(view, "currentAppRoot")?)
            || !decimal(text(view, "currentPackageRoot")?)
            || !decimal(text(view, "currentWorldRoot")?)
            || !decimal(text(view, "worldRoot")?)
            || !decimal(text(view, "height")?)
        {
            return Err(invalid("v4 retry claim plan differs from retained fresh BEGIN"));
        }
        let binding = view
            .get("binding")
            .ok_or_else(|| invalid("v4 retry claim binding field absent"))?;
        checked_create_binding(binding, create_index(begin)?, launch)?;
        let slots = view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("v4 retry claim signing slots absent"))?;
        if slots.len() > self.signers.len() {
            return Err(invalid("v4 retry claim signing slot count exceeds custody pins"));
        }
        Ok(slots)
    }
}

pub(crate) struct AssembledRetryClaim {
    attempt_dir: PathBuf,
    active_marker: Vec<u8>,
    begin_sha256: String,
    descriptor_sha256: String,
    ingress: Vec<u8>,
    original_index: String,
    query_nonce: String,
}

/// Current-image op68 plan plus detached op69 ingress. This does not submit
/// op26 or authorize a physical action.
#[allow(clippy::too_many_arguments)]
pub(crate) fn assemble_once(
    operator: &PrivateOperator,
    fixed: &FixedRetryClaimSigners,
    app_uid: u32,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    selection: &RetrySelection,
    nonce_ledger: &Path,
    attempt_dir: &Path,
) -> io::Result<AssembledRetryClaim> {
    fixed.validate(operator, app_uid)?;
    create_index(begin)?;
    if !begin.ingress.starts_with(BEGIN_TAG) {
        return Err(invalid("v4 retry claim original BEGIN is not v4"));
    }
    let original_index = decimal_predecessor(&begin.accepted_count)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v4 retry claim attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let query_nonce = allocate_operation_id(nonce_ledger)?;
    let source = json!({"originalIndex":original_index,"queryNonce":query_nonce});
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        REQUEST_INSPECT_KIND,
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    if request != request_bytes(&original_index, &query_nonce)? {
        return Err(invalid("v4 retry claim request differs from Lean requestCodec layout"));
    }
    let request_path = attempt_dir.join("request.bin");
    let inspected = operator.tool(
        "inspect",
        REQUEST_INSPECT_KIND,
        &request_path,
        &attempt_dir.join("request-inspection.json"),
    )?;
    let request_view: Value = serde_json::from_slice(&inspected)?;
    if text(&request_view, "type")? != REQUEST_VIEW_TYPE
        || text(&request_view, "canonicalRequestHex")? != hex(&request)
        || text(&request_view, "originalIndex")? != original_index
        || text(&request_view, "queryNonce")? != query_nonce
    {
        return Err(invalid("v4 retry claim request differs from Rust encoding"));
    }
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-launch-retry-claim-prepare-requested-v4",
        "originalIndex":original_index,
        "queryNonce":query_nonce,
        "requestSha256":hex(&Sha256::digest(&request)),
        "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
        "retryRecoveryIndex":selection.recovery_index,
    }))?;
    write_new(attempt_dir, "op68-requested.json", &active)?;
    write_new(parent, ACTIVE_MARKER, &active)?;
    let reply = operator.invoke(68, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op68-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 68, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        PLAN_INSPECT_KIND,
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let slots = fixed.checked_plan_slots(
        &view,
        &ClaimPlanEvidence {
            plan,
            request: &request,
            begin,
            launch,
            original_index: &original_index,
            query_nonce: &query_nonce,
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
    pair.extend_from_slice(plan);
    pair.extend_from_slice(&encoded);
    write_new(attempt_dir, "op69-requested.bin", &pair)?;
    let reply = operator.invoke(69, &pair)?;
    write_new(attempt_dir, "op69-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 69, INGRESS_TAG)?.to_vec();
    write_new(attempt_dir, CLAIM_INGRESS_FILE, &ingress)?;
    Ok(AssembledRetryClaim {
        attempt_dir: attempt_dir.to_path_buf(),
        active_marker: active,
        begin_sha256: hex(&Sha256::digest(&begin.ingress)),
        descriptor_sha256: hex(&Sha256::digest(&launch.descriptor().canonical)),
        ingress,
        original_index,
        query_nonce,
    })
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn checked_committed(
    view: &Value,
    committed: &[u8],
    claim_ingress: &[u8],
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    app: &str,
    package_manifest: &str,
    selection: &RetrySelection,
) -> io::Result<(String, String, String, String)> {
    let descriptor = launch.descriptor();
    if text(view, "type")? != COMMITTED_VIEW_TYPE
        || text(view, "frameHex")? != hex(committed)
        || text(view, "frameByteCount")? != committed.len().to_string()
        || text(view, "originalClaimHex")? != hex(claim_ingress)
        || text(view, "originalBeginHex")? != hex(&begin.ingress)
        || text(view, "app")? != app
        || text(view, "kind")? != "start"
        || text(view, "clientOperationId")? != begin.client_operation_id
        || text(view, "authorizationOperationId")? != begin.authorization_operation_id
        || text(view, "packageManifest")? != package_manifest
        || text(view, "snapshotManifest")? != begin.snapshot_manifest
        || text(view, "processGeneration")? != begin.process_generation
        || text(view, "processIdentityHex")? != begin.process_identity_hex
        || text(view, "descriptorHex")? != hex(&descriptor.canonical)
        || text(view, "descriptorRoot")? != descriptor.root
        || text(view, "volumeIdHex")? != begin.volume_id_hex
        || text(view, "originalTransaction")? != begin.transaction_id
        || text(view, "originalEvent")? != begin.event_id
        || text(view, "imageIdentityHex")? != hex(&descriptor.package.image_identity)
        || !decimal(text(view, "originalNullifier")?)
        || !decimal(text(view, "claimNullifier")?)
        || !decimal(text(view, "appPhysicalRoot")?)
        || !decimal(text(view, "packagePhysicalRoot")?)
        || !decimal(text(view, "authorityPhysicalRoot")?)
        || !decimal(text(view, "postWorldRoot")?)
    {
        return Err(invalid(
            "v4 retry committed claim differs from fresh ingress or signed SPK",
        ));
    }
    checked_retry_fields(view, selection)?;
    let binding = view
        .get("binding")
        .ok_or_else(|| invalid("v4 retry committed claim binding absent"))?;
    checked_create_binding(binding, create_index(begin)?, launch)?;
    let receipt = view
        .get("receipt")
        .ok_or_else(|| invalid("v4 retry committed receipt absent"))?;
    let receipt_field = |name| -> io::Result<String> {
        let value = text(receipt, name)?;
        if !decimal(value) {
            return Err(invalid("v4 retry committed receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    let transaction_id = receipt_field("transactionId")?;
    let event_id = receipt_field("eventId")?;
    let accepted_count = receipt_field("acceptedCount")?;
    let world_root = receipt_field("worldRoot")?;
    if !later_decimal(&accepted_count, &begin.accepted_count)
        || world_root != text(view, "postWorldRoot")?
    {
        return Err(invalid(
            "v4 retry committed receipt differs from claimed post-image",
        ));
    }
    Ok((transaction_id, event_id, accepted_count, world_root))
}

/// Submit once to op26. Only its fresh-tip committed-v4 callback can arm a
/// physical caller; an op27 receipt-only lookup never enters this path.
pub(crate) fn submit_fresh_once(
    operator: &PrivateOperator,
    assembled: AssembledRetryClaim,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    fixed: &FixedRetryClaimSigners,
    selection: &RetrySelection,
) -> io::Result<CommittedLaunchClaim> {
    checked_assembled(&assembled, begin, launch)?;
    let attempt_dir = &assembled.attempt_dir;
    let marker = json!({
        "protocol":"mini-spk-launch-retry-claim-submit-requested-v4",
        "originalIndex":assembled.original_index,
        "queryNonce":assembled.query_nonce,
        "ingressSha256":hex(&Sha256::digest(&assembled.ingress)),
        "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
    });
    write_new(
        attempt_dir,
        "op26-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let reply = operator.invoke(26, &assembled.ingress)?;
    write_new(attempt_dir, "op26-frame.bin", &reply)?;
    let committed = framed_payload(&reply, 26, COMMITTED_TAG)?.to_vec();
    let committed_path = write_new(attempt_dir, COMMITTED_FILE, &committed)?;
    let inspection = operator.tool(
        "inspect",
        COMMITTED_INSPECT_KIND,
        &committed_path,
        &attempt_dir.join(COMMITTED_INSPECTION_FILE),
    )?;
    let view: Value = serde_json::from_slice(&inspection)?;
    let (transaction_id, event_id, accepted_count, world_root) = checked_committed(
        &view,
        &committed,
        &assembled.ingress,
        begin,
        launch,
        &fixed.selector.app,
        &fixed.selector.package_manifest,
        selection,
    )?;
    let physical_begin = verified_physical_begin(fixed, begin, launch, &transaction_id, &event_id)?;
    Ok(CommittedLaunchClaim {
        committed,
        inspection,
        claim_ingress: assembled.ingress,
        physical_begin,
        transaction_id,
        event_id,
        accepted_count,
        world_root,
    })
}

fn verified_physical_begin(
    fixed: &FixedRetryClaimSigners,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
    transaction_id: &str,
    event_id: &str,
) -> io::Result<VerifiedBegin> {
    let app: u64 = fixed
        .selector
        .app
        .parse()
        .map_err(|_| invalid("v4 retry claimed app exceeds host unit range"))?;
    let generation: u64 = begin
        .process_generation
        .parse()
        .map_err(|_| invalid("v4 retry claimed generation exceeds host unit range"))?;
    if app == 0
        || generation == 0
        || !decimal(&begin.authorization_operation_id)
        || !decimal(transaction_id)
        || !decimal(event_id)
    {
        return Err(invalid("v4 retry claimed physical identity malformed"));
    }
    let unit = String::from_utf8(crate::lifecycle_v3_native::unhex(&begin.process_identity_hex)?)
        .map_err(|_| invalid("v4 retry claimed unit is not UTF-8"))?;
    if !crate::broker::parse_resident_unit(&unit).is_some_and(|(_, unit_app, unit_generation)| {
        unit_app == app.to_string() && unit_generation == generation.to_string()
    }) {
        return Err(invalid("v4 retry claimed unit differs from inspected BEGIN"));
    }
    Ok(VerifiedBegin {
        app,
        generation,
        operation_id: begin.authorization_operation_id.clone(),
        transaction_id: transaction_id.to_owned(),
        event_id: event_id.to_owned(),
        package_sha256: launch.signed_package_sha256().to_owned(),
        image_identity: hex(&launch.descriptor().package.image_identity),
        process_identity: unit.clone(),
        unit,
    })
}

fn checked_assembled(
    assembled: &AssembledRetryClaim,
    begin: &AcceptedLaunchBegin,
    launch: &SourceBoundLaunch<'_>,
) -> io::Result<()> {
    let attempt_dir = &assembled.attempt_dir;
    private_dir(attempt_dir)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v4 retry claim attempt parent absent"))?;
    private_dir(parent)?;
    if fs::read(parent.join(ACTIVE_MARKER))? != assembled.active_marker
        || fs::read(attempt_dir.join(CLAIM_INGRESS_FILE))? != assembled.ingress
        || assembled.begin_sha256 != hex(&Sha256::digest(&begin.ingress))
        || assembled.descriptor_sha256 != hex(&Sha256::digest(&launch.descriptor().canonical))
    {
        return Err(invalid("v4 retry claim attempt artifacts differ before submit"));
    }
    if !decimal(&assembled.original_index) || !decimal(&assembled.query_nonce) {
        return Err(invalid("v4 retry assembled claim identity malformed"));
    }
    Ok(())
}

/// Op27 after an uncertain op26: the exact retained v4 claim only. The
/// receipt is historical evidence and can never arm a physical launch.
pub(crate) fn recover_claim_receipt_only(
    operator: &PrivateOperator,
    attempt_dir: &Path,
) -> io::Result<RecoveredReceipt> {
    let ingress = retained_submitted_ingress(
        attempt_dir,
        ACTIVE_MARKER,
        "op68-requested.json",
        "op26-requested.json",
        "mini-spk-launch-retry-claim-submit-requested-v4",
        CLAIM_INGRESS_FILE,
    )?;
    if !ingress.starts_with(INGRESS_TAG) {
        return Err(invalid("v4 retry retained claim frame refused"));
    }
    lookup_retained(operator, attempt_dir, 27, &ingress)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retry_v4_claim_request_is_tag_then_two_naturals() {
        let mut expected = b"DREGG/APPLICATION/RETRY-CREATE-CLAIM-OPERATOR-REQUEST/v4".to_vec();
        expected.extend_from_slice(&[78, 255, 0, 1, 255]);
        assert_eq!(request_bytes("78", "255").unwrap(), expected);
        assert!(request_bytes("078", "1").is_err());
    }

    #[test]
    fn retry_v4_claim_committed_tag_refuses_v3_projection() {
        let v3 = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v3";
        let mut reply = ((v3.len() + 2) as u32).to_le_bytes().to_vec();
        reply.push(26);
        reply.extend_from_slice(v3);
        reply.push(1);
        assert!(framed_payload(&reply, 26, COMMITTED_TAG).is_err());
        let mut reply = ((COMMITTED_TAG.len() + 2) as u32).to_le_bytes().to_vec();
        reply.push(26);
        reply.extend_from_slice(COMMITTED_TAG);
        reply.push(1);
        assert!(framed_payload(&reply, 26, COMMITTED_TAG).is_ok());
    }
}
