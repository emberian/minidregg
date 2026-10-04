//! Governed repeat-CREATE physical report and COMPLETION (event72).
//! The report half is modeled on `lifecycle_v3_report_native` (Host author
//! kinds `application-lifecycle-retry-physical-*`, same JSON fields, the v4
//! committed claim in "committedClaim"); the completion half on
//! `lifecycle_v3_completion_native` (op70 plan / op71 assemble / op38 submit /
//! op39 receipt-only lookup). Uncertain op38 is never resubmitted.
#![allow(dead_code)] // The op39 arm is reached only by operator recovery.

use crate::dispatch_author::{private_signing_key, SignerPin};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::Journal;
use crate::lifecycle_v3_claim_native::CommittedLaunchClaim;
use crate::lifecycle_v3_completion_native::{
    checked_receipt, ConfirmedLaunchCompletion, RecoveredLaunchCompletion,
};
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text, AcceptedLaunchBegin,
    LaunchBeginAction,
};
use crate::lifecycle_v4_retry_claim_native::COMMITTED_TAG;
use crate::lifecycle_v4_retry_native::{
    checked_retry_fields, encode_bytes, encode_nat_decimal, retained_submitted_ingress,
    RetrySelection, BEGIN_TAG, OUTCOME_TAG,
};
use crate::resident_launch::SourceBoundLaunch;
use crate::volume_custody::VolumeWitness;
use ed25519_dalek::Signer;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File};
use std::io::{self, Read};
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

const MAX_REPORT: usize = 12_102_759;

/// Kernel/ApplicationLifecycleRetryCompletionV4Report.lean:60-61, 136-137, 142-143.
const REPORT_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-PHYSICAL-REPORT/v4";
const SIGNED_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-PHYSICAL-SIGNED/v4";
const SIGNATURE_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-PHYSICAL-SIGNATURE/v4";
/// Host/ApplicationLifecycleRetryCompletionV4Authoring.lean:43-45.
pub(crate) const REQUEST_TAG: &[u8] =
    b"DREGG/APPLICATION/RETRY-CREATE-COMPLETION-OPERATOR-REQUEST/v4";
/// CONTRACT-V4-WIRE op70 plan frame.
const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-COMPLETION-OPERATOR-PLAN/v4";
/// Kernel/ApplicationLifecycleRetryCompletionV4Ingress.lean:43-44.
pub(crate) const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/RETRY-CREATE-COMPLETION-INGRESS/v4";

const REQUEST_INSPECT_KIND: &str = "application-lifecycle-retry-completion-request";
const REPORT_KIND: &str = "application-lifecycle-retry-physical-report";
const SIGNING_FRAME_KIND: &str = "application-lifecycle-retry-physical-signing-frame";
const SIGNED_REPORT_KIND: &str = "application-lifecycle-retry-physical-signed-report";
const REPORT_VIEW_TYPE: &str = "application-lifecycle-retry-physical-report-v4";
const SIGNED_REPORT_VIEW_TYPE: &str = "application-lifecycle-retry-physical-signed-report-v4";
const PLAN_INSPECT_KIND: &str = "application-lifecycle-retry-completion-plan";
const REQUEST_VIEW_TYPE: &str = "application-lifecycle-retry-completion-request-v4";
const PLAN_VIEW_TYPE: &str = "application-lifecycle-retry-completion-plan-v4";

pub(crate) const ACTIVE_MARKER: &str = "lifecycle-completion-retry-v4-active.json";
pub(crate) const REPORT_ATTEMPT_DIR: &str = "completion-attempt-retry-v4";
pub(crate) const COMPLETION_ATTEMPT_DIR: &str = "completion-sign-attempt-retry-v4";
pub(crate) const COMPLETION_INGRESS_FILE: &str = "completion-retry-v4.bin";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

// ---------------------------------------------------------------------------
// Physical report (custodian-signed), modeled on lifecycle_v3_report_native

pub(crate) struct SignedRetryPhysicalReport {
    pub signed_report: Vec<u8>,
    pub attempt_dir: PathBuf,
}

pub(crate) struct RetryReportInput<'a> {
    pub begin: &'a AcceptedLaunchBegin,
    pub claim: &'a CommittedLaunchClaim,
    pub launch: &'a SourceBoundLaunch<'a>,
    pub journal: &'a Journal,
    pub volume: &'a VolumeWitness,
    pub selection: &'a RetrySelection,
}

fn nonce() -> io::Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    let value = u128::from_le_bytes(bytes);
    if value == 0 {
        return Err(invalid("v4 retry physical nonce zero"));
    }
    Ok(value.to_string())
}

fn checked_observation(input: &RetryReportInput<'_>) -> io::Result<Value> {
    let RetryReportInput {
        begin,
        claim,
        launch,
        journal,
        volume,
        selection: _,
    } = input;
    let physical = &claim.physical_begin;
    if !matches!(begin.action, LaunchBeginAction::Create(_))
        || !begin.ingress.starts_with(BEGIN_TAG)
        || !claim.committed.starts_with(COMMITTED_TAG)
        || physical.operation_id != begin.authorization_operation_id
        || physical.transaction_id != claim.transaction_id
        || physical.event_id != claim.event_id
        || physical.package_sha256 != launch.signed_package_sha256()
        || physical.image_identity != hex(&launch.descriptor().package.image_identity)
    {
        return Err(invalid(
            "v4 retry physical observation differs from committed claim",
        ));
    }
    let record = journal
        .read()?
        .ok_or_else(|| invalid("v4 retry physical Running journal absent"))?;
    record.verify_running_instance()?;
    if record.app() != physical.app
        || record.generation() != physical.generation
        || record.operation_id() != physical.operation_id
        || record.unit() != physical.unit
        || record.transaction_id() != physical.transaction_id
        || record.event_id() != physical.event_id
        || record.image_identity() != physical.image_identity
        || volume.volume_id != begin.volume_id_hex
    {
        return Err(invalid("v4 retry physical running unit or volume differs"));
    }
    volume.recheck_handoff()?;
    let invocation = record
        .invocation_id()
        .filter(|value| !value.is_empty())
        .ok_or_else(|| invalid("v4 retry physical invocation absent"))?;
    let group = record
        .control_group()
        .filter(|value| !value.is_empty())
        .ok_or_else(|| invalid("v4 retry physical cgroup absent"))?;
    let pid = record
        .child_pid
        .filter(|value| *value > 0)
        .ok_or_else(|| invalid("v4 retry physical child pid absent"))?;
    Ok(json!({
        "begin":hex(&begin.ingress), "committedClaim":hex(&claim.committed),
        "nonce":nonce()?, "unit":hex(physical.unit.as_bytes()),
        "materializedImage":physical.image_identity,
        "outcome":"running", "invocationId":hex(invocation.as_bytes()),
        "controlGroup":hex(group.as_bytes()), "pid":pid.to_string(),
        "stopAudit":Value::Null,
        "volumeWitness":hex(&volume.bytes),
    }))
}

/// Mirrors v3 `checked_report` against the
/// `application-lifecycle-retry-physical-report-v4` view (Host/Json.lean
/// `retryPhysicalReportJson`), plus the retry selector fields.
fn checked_report(
    view: &Value,
    report: &[u8],
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    observation: &Value,
    selection: &RetrySelection,
) -> io::Result<()> {
    let same = |field: &str, expected: &str| -> io::Result<()> {
        if text(view, field)? != expected {
            return Err(invalid("v4 retry physical report differs from observation"));
        }
        Ok(())
    };
    same("type", REPORT_VIEW_TYPE)?;
    same("frameHex", &hex(report))?;
    same("originalBeginHex", &hex(&begin.ingress))?;
    same("committedClaimHex", &hex(&claim.committed))?;
    for (actual, source) in [
        ("nonce", "nonce"),
        ("unitHex", "unit"),
        ("materializedImageHex", "materializedImage"),
        ("outcome", "outcome"),
        ("invocationIdHex", "invocationId"),
        ("controlGroupHex", "controlGroup"),
        ("pid", "pid"),
    ] {
        same(actual, text(observation, source)?)?;
    }
    if !decimal(text(view, "nonce")?)
        || !decimal(text(view, "pid")?)
        || !text(view, "stopAuditHex")?.is_empty()
        || text(view, "installedManifestHex")?.is_empty()
    {
        return Err(invalid("v4 retry physical report source fields refused"));
    }
    let custody = view
        .get("volumeCustody")
        .ok_or_else(|| invalid("v4 retry physical volume custody absent"))?;
    if text(custody, "volumeIdHex")? != begin.volume_id_hex
        || text(custody, "physicalWitnessHex")? != text(observation, "volumeWitness")?
    {
        return Err(invalid("v4 retry physical source volume custody differs"));
    }
    checked_retry_fields(view, selection)
}

fn unhex_field(observation: &Value, field: &str) -> io::Result<Vec<u8>> {
    crate::lifecycle_v3_native::unhex(text(observation, field)?)
}

/// `reportStream` (ApplicationLifecycleRetryCompletionV4Report.lean:37-48)
/// opens with `committedStream claim ++ nat nonce ++ bytes unit ++ bytes
/// materializedImage`. The committed claim is the v4 projection frame minus
/// its tag. The tail (outcome, ids, manifest, custody) is Mini-derived and
/// re-checked by `Report.validFor` in Mini.
fn expected_report_prefix(committed: &[u8], observation: &Value) -> io::Result<Vec<u8>> {
    let claim = committed
        .strip_prefix(COMMITTED_TAG)
        .filter(|stream| !stream.is_empty())
        .ok_or_else(|| invalid("v4 retry committed projection frame refused"))?;
    let mut prefix = REPORT_TAG.to_vec();
    prefix.extend_from_slice(claim);
    prefix.extend_from_slice(&encode_nat_decimal(text(observation, "nonce")?)?);
    prefix.extend_from_slice(&encode_bytes(&unhex_field(observation, "unit")?));
    prefix.extend_from_slice(&encode_bytes(&unhex_field(
        observation,
        "materializedImage",
    )?));
    Ok(prefix)
}

/// `signingFrame` (…Report.lean:141-145) ends with `bytes report`;
/// `signedCodec` (…Report.lean:130-140) is `SIGNED_TAG ++ reportStream ++
/// bytes signature`. Both are fixed by the exact report bytes.
fn checked_signing_frame(frame: &[u8], report: &[u8]) -> io::Result<()> {
    if !frame.starts_with(SIGNATURE_TAG) || !frame.ends_with(&encode_bytes(report)) {
        return Err(invalid("v4 retry physical signing frame differs from report"));
    }
    Ok(())
}

fn expected_signed(report: &[u8], signature: &[u8]) -> io::Result<Vec<u8>> {
    let stream = report
        .strip_prefix(REPORT_TAG)
        .ok_or_else(|| invalid("v4 retry physical report frame refused"))?;
    let mut signed = SIGNED_TAG.to_vec();
    signed.extend_from_slice(stream);
    signed.extend_from_slice(&encode_bytes(signature));
    Ok(signed)
}

/// The caller must first verify the live unit and retain its exact v4 claim.
pub(crate) fn prepare_report_once(
    operator: &PrivateOperator,
    input: RetryReportInput<'_>,
    custodian_seed: &Path,
    semantics: &str,
    attempt_dir: &Path,
) -> io::Result<SignedRetryPhysicalReport> {
    crate::completion_native::preflight_custodian(operator, custodian_seed, semantics)?;
    let observation = checked_observation(&input)?;
    let begin = input.begin;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v4 retry physical report parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let source = write_new(
        attempt_dir,
        "report-source.json",
        &serde_json::to_vec(&observation)?,
    )?;
    let report = operator.tool(
        "author",
        REPORT_KIND,
        &source,
        &attempt_dir.join("report.bin"),
    )?;
    if report.is_empty()
        || report.len() > MAX_REPORT
        || !report.starts_with(&expected_report_prefix(&input.claim.committed, &observation)?)
    {
        return Err(invalid("v4 retry physical report differs from observation"));
    }
    let report_path = attempt_dir.join("report.bin");
    let inspection = operator.tool(
        "inspect",
        REPORT_KIND,
        &report_path,
        &attempt_dir.join("report-inspection.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspection)?;
    checked_report(
        &view,
        &report,
        begin,
        input.claim,
        &observation,
        input.selection,
    )?;
    let frame_input = write_new(
        attempt_dir,
        "signing-frame-source.json",
        &serde_json::to_vec(&json!({"begin":hex(&begin.ingress),"report":hex(&report)}))?,
    )?;
    let frame = operator.tool(
        "author",
        SIGNING_FRAME_KIND,
        &frame_input,
        &attempt_dir.join("signing-frame.bin"),
    )?;
    if frame.is_empty() || frame.len() > MAX_REPORT {
        return Err(invalid("v4 retry physical signing frame bound refused"));
    }
    checked_signing_frame(&frame, &report)?;
    let after = checked_observation(&input)?;
    for field in [
        "unit",
        "materializedImage",
        "outcome",
        "invocationId",
        "controlGroup",
        "pid",
        "volumeWitness",
    ] {
        if observation.get(field) != after.get(field) {
            return Err(invalid(
                "v4 retry physical running observation changed before signing",
            ));
        }
    }
    let signature = private_signing_key(custodian_seed)?.sign(&frame).to_bytes();
    let signed_input = write_new(
        attempt_dir,
        "signed-report-source.json",
        &serde_json::to_vec(&json!({
            "begin":hex(&begin.ingress), "report":hex(&report), "signature":hex(&signature)
        }))?,
    )?;
    let signed = operator.tool(
        "author",
        SIGNED_REPORT_KIND,
        &signed_input,
        &attempt_dir.join("signed-report.bin"),
    )?;
    if signed != expected_signed(&report, &signature)? {
        return Err(invalid("v4 retry signed physical report differs"));
    }
    let signed_path = attempt_dir.join("signed-report.bin");
    let inspected = operator.tool(
        "inspect",
        SIGNED_REPORT_KIND,
        &signed_path,
        &attempt_dir.join("signed-report-inspection.json"),
    )?;
    let signed_view: Value = serde_json::from_slice(&inspected)?;
    if text(&signed_view, "type")? != SIGNED_REPORT_VIEW_TYPE
        || text(&signed_view, "frameHex")? != hex(&signed)
        || text(&signed_view, "signatureHex")? != hex(&signature)
    {
        return Err(invalid("v4 retry signed physical report view differs"));
    }
    checked_report(
        signed_view
            .get("report")
            .ok_or_else(|| invalid("v4 retry signed physical report absent"))?,
        &report,
        begin,
        input.claim,
        &observation,
        input.selection,
    )?;
    Ok(SignedRetryPhysicalReport {
        signed_report: signed,
        attempt_dir: attempt_dir.to_path_buf(),
    })
}

// ---------------------------------------------------------------------------
// Completion, modeled on lifecycle_v3_completion_native

/// `requestCodec` (Host/ApplicationLifecycleRetryCompletionV4Authoring.lean:28-45):
/// `REQUEST_TAG ++ bytes begin ++ bytes claimIngress ++ bytes signedReport`.
pub(crate) fn request_bytes(begin: &[u8], claim: &[u8], report: &[u8]) -> Vec<u8> {
    let mut request = REQUEST_TAG.to_vec();
    request.extend_from_slice(&encode_bytes(begin));
    request.extend_from_slice(&encode_bytes(claim));
    request.extend_from_slice(&encode_bytes(report));
    request
}

/// Same custody file and protocol as the v3 completion signers.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedRetryCompletionSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

struct CompletionEvidence<'a> {
    plan: &'a [u8],
    request: &'a [u8],
    begin: &'a [u8],
    claim: &'a [u8],
    descriptor_root: &'a str,
    volume_id_hex: &'a str,
    report: &'a [u8],
}

impl FixedRetryCompletionSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-completion-management-v1" {
            return Err(invalid("v4 retry completion fixed management refused"));
        }
        crate::lifecycle_selector::validate_custody(
            operator,
            &self.selector,
            &self.management_subject,
            &self.signers,
            app_uid,
        )
    }

    fn checked_slots<'a>(
        &self,
        view: &'a Value,
        evidence: &CompletionEvidence<'_>,
    ) -> io::Result<&'a [Value]> {
        if text(view, "type")? != PLAN_VIEW_TYPE
            || text(view, "canonicalPlanHex")? != hex(evidence.plan)
            || text(view, "canonicalRequestHex")? != hex(evidence.request)
            || text(view, "originalBeginHex")? != hex(evidence.begin)
            || text(view, "originalClaimHex")? != hex(evidence.claim)
            || text(view, "signedReportHex")? != hex(evidence.report)
            || text(view, "app")? != self.selector.app
            || text(view, "descriptorRoot")? != evidence.descriptor_root
            || text(view, "volumeIdHex")? != evidence.volume_id_hex
            || !lowercase_hex(text(view, "sourceHex")?)
            || text(view, "sourceHex")?.is_empty()
            || !decimal(text(view, "currentAppRoot")?)
            || !decimal(text(view, "currentPackageRoot")?)
            || !decimal(text(view, "worldRoot")?)
            || !decimal(text(view, "height")?)
        {
            return Err(invalid(
                "v4 retry completion plan differs from retained lifecycle",
            ));
        }
        let slots = view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("v4 retry completion signing slots absent"))?;
        if slots.len() > self.signers.len() {
            return Err(invalid(
                "v4 retry completion signing slot count exceeds custody pins",
            ));
        }
        Ok(slots)
    }
}

pub(crate) struct AssembledRetryCompletion {
    attempt_dir: PathBuf,
    active_marker: Vec<u8>,
    ingress: Vec<u8>,
    begin_sha256: String,
    claim_sha256: String,
    report_sha256: String,
}

pub(crate) struct RetryCompletionInput<'a> {
    pub begin: &'a AcceptedLaunchBegin,
    pub claim: &'a CommittedLaunchClaim,
    pub launch: &'a SourceBoundLaunch<'a>,
    pub signed_report: &'a [u8],
}

/// Op70/71 are current-image authoring only; op38 admission is separate.
pub(crate) fn assemble_once(
    operator: &PrivateOperator,
    fixed: &FixedRetryCompletionSigners,
    app_uid: u32,
    input: RetryCompletionInput<'_>,
    attempt_dir: &Path,
) -> io::Result<AssembledRetryCompletion> {
    let RetryCompletionInput {
        begin,
        claim,
        launch,
        signed_report,
    } = input;
    fixed.validate(operator, app_uid)?;
    if signed_report.is_empty()
        || signed_report.len() > MAX_REPORT
        || !signed_report.starts_with(SIGNED_TAG)
        || !begin.ingress.starts_with(BEGIN_TAG)
    {
        return Err(invalid("v4 retry signed physical report bound refused"));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v4 retry completion attempt parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let source = json!({
        "begin":hex(&begin.ingress),
        "claimIngress":hex(&claim.claim_ingress),
        "signedReport":hex(signed_report),
    });
    let source_path = write_new(attempt_dir, "request.json", &serde_json::to_vec(&source)?)?;
    let request = operator.tool(
        "author",
        REQUEST_INSPECT_KIND,
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    if request != request_bytes(&begin.ingress, &claim.claim_ingress, signed_report) {
        return Err(invalid(
            "v4 retry completion request differs from Lean requestCodec layout",
        ));
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
        || text(&request_view, "originalBeginHex")? != hex(&begin.ingress)
        || text(&request_view, "originalClaimHex")? != hex(&claim.claim_ingress)
        || text(&request_view, "signedReportHex")? != hex(signed_report)
        || text(&request_view, "app")? != fixed.selector.app
        || text(&request_view, "descriptorRoot")? != launch.descriptor().root
        || text(&request_view, "volumeIdHex")? != begin.volume_id_hex
    {
        return Err(invalid(
            "v4 retry completion request differs from retained lifecycle",
        ));
    }
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-launch-retry-completion-prepare-requested-v4",
        "requestSha256":hex(&Sha256::digest(&request)),
        "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
        "originalClaimSha256":hex(&Sha256::digest(&claim.claim_ingress)),
        "signedReportSha256":hex(&Sha256::digest(signed_report)),
    }))?;
    write_new(attempt_dir, "op70-requested.json", &active)?;
    write_new(parent, ACTIVE_MARKER, &active)?;
    let reply = operator.invoke(70, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op70-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 70, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        PLAN_INSPECT_KIND,
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let slots = fixed.checked_slots(
        &view,
        &CompletionEvidence {
            plan,
            request: &request,
            begin: &begin.ingress,
            claim: &claim.claim_ingress,
            descriptor_root: &launch.descriptor().root,
            volume_id_hex: &begin.volume_id_hex,
            report: signed_report,
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
    write_new(attempt_dir, "op71-requested.bin", &pair)?;
    let reply = operator.invoke(71, &pair)?;
    write_new(attempt_dir, "op71-frame.bin", &reply)?;
    let ingress = framed_payload(&reply, 71, INGRESS_TAG)?.to_vec();
    write_new(attempt_dir, COMPLETION_INGRESS_FILE, &ingress)?;
    Ok(AssembledRetryCompletion {
        attempt_dir: attempt_dir.to_path_buf(),
        active_marker: active,
        ingress,
        begin_sha256: hex(&Sha256::digest(&begin.ingress)),
        claim_sha256: hex(&Sha256::digest(&claim.claim_ingress)),
        report_sha256: hex(&Sha256::digest(signed_report)),
    })
}

fn checked_assembled(
    assembled: &AssembledRetryCompletion,
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    signed_report: &[u8],
) -> io::Result<()> {
    let attempt = &assembled.attempt_dir;
    private_dir(attempt)?;
    let parent = attempt
        .parent()
        .ok_or_else(|| invalid("v4 retry completion parent absent"))?;
    private_dir(parent)?;
    if fs::read(parent.join(ACTIVE_MARKER))? != assembled.active_marker
        || fs::read(attempt.join(COMPLETION_INGRESS_FILE))? != assembled.ingress
        || assembled.begin_sha256 != hex(&Sha256::digest(&begin.ingress))
        || assembled.claim_sha256 != hex(&Sha256::digest(&claim.claim_ingress))
        || assembled.report_sha256 != hex(&Sha256::digest(signed_report))
    {
        return Err(invalid(
            "v4 retry completion attempt artifacts differ before submit",
        ));
    }
    Ok(())
}

/// Op38 has no physical authority on a replayed or uncertain outcome.
pub(crate) fn submit_fresh_once(
    operator: &PrivateOperator,
    assembled: &AssembledRetryCompletion,
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    signed_report: &[u8],
    journal: &Journal,
) -> io::Result<ConfirmedLaunchCompletion> {
    checked_assembled(assembled, begin, claim, signed_report)?;
    if !matches!(begin.action, LaunchBeginAction::Create(_)) {
        return Err(invalid("v4 retry completion physical phase differs from BEGIN"));
    }
    let record = journal
        .read()?
        .ok_or_else(|| invalid("v4 retry START physical journal absent"))?;
    record.verify_running_instance()?;
    if record.app() != claim.physical_begin.app
        || record.generation() != claim.physical_begin.generation
        || record.unit() != claim.physical_begin.unit
        || record.transaction_id() != claim.physical_begin.transaction_id
        || record.event_id() != claim.physical_begin.event_id
    {
        return Err(invalid(
            "v4 retry START running journal differs from fresh claim",
        ));
    }
    let attempt = &assembled.attempt_dir;
    let marker = json!({
        "protocol":"mini-spk-launch-retry-completion-submit-requested-v4",
        "ingressSha256":hex(&Sha256::digest(&assembled.ingress)),
        "claimSha256":hex(&Sha256::digest(&claim.committed)),
    });
    write_new(
        attempt,
        "op38-requested.json",
        &serde_json::to_vec(&marker)?,
    )?;
    let reply = operator.invoke(38, &assembled.ingress)?;
    write_new(attempt, "op38-frame.bin", &reply)?;
    let outcome = framed_payload(&reply, 38, OUTCOME_TAG)?;
    let outcome_path = write_new(attempt, "op38-outcome.bin", outcome)?;
    let inspected = operator.tool(
        "inspect",
        "outcome",
        &outcome_path,
        &attempt.join("op38-outcome.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let confirmed = checked_receipt(&view, "installed", &claim.accepted_count)?;
    journal
        .read()?
        .ok_or_else(|| invalid("v4 retry START journal lost after completion"))?
        .verify_running_instance()?;
    Ok(confirmed)
}

/// Op39 reads the exact original event72 receipt after an uncertain op38.
/// Never invokes op38, assembles another ingress, or grants launch authority.
pub(crate) fn recover_receipt_only(
    operator: &PrivateOperator,
    attempt_dir: &Path,
    claim: &CommittedLaunchClaim,
) -> io::Result<RecoveredLaunchCompletion> {
    let ingress = retained_submitted_ingress(
        attempt_dir,
        ACTIVE_MARKER,
        "op70-requested.json",
        "op38-requested.json",
        "mini-spk-launch-retry-completion-submit-requested-v4",
        COMPLETION_INGRESS_FILE,
    )?;
    let marker: Value = serde_json::from_slice(&fs::read(attempt_dir.join("op38-requested.json"))?)?;
    if !ingress.starts_with(INGRESS_TAG)
        || text(&marker, "claimSha256")? != hex(&Sha256::digest(&claim.committed))
    {
        return Err(invalid("v4 retry completion original submit marker differs"));
    }
    let receipt = crate::lifecycle_v4_retry_native::lookup_retained(
        operator,
        attempt_dir,
        39,
        &ingress,
    )?;
    let confirmed = ConfirmedLaunchCompletion {
        transaction_id: receipt.transaction_id,
        event_id: receipt.event_id,
        accepted_count: receipt.accepted_count,
        world_root: receipt.world_root,
    };
    if !crate::lifecycle_v3_claim_native::later_decimal(
        &confirmed.accepted_count,
        &claim.accepted_count,
    ) {
        return Err(invalid("v4 retry completion receipt does not follow claim"));
    }
    Ok(RecoveredLaunchCompletion {
        receipt: confirmed,
        inspection_name: receipt.inspection_name,
        inspection_sha256: receipt.inspection_sha256,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retry_v4_completion_request_is_three_length_prefixed_byte_strings() {
        let mut expected =
            b"DREGG/APPLICATION/RETRY-CREATE-COMPLETION-OPERATOR-REQUEST/v4".to_vec();
        expected.extend_from_slice(&[1, 255, b'b', 2, 255, b'c', b'c', 0, 255]);
        assert_eq!(request_bytes(b"b", b"cc", b""), expected);
    }

    #[test]
    fn retry_v4_report_frames_bind_exact_committed_claim_and_report() {
        let mut committed = COMMITTED_TAG.to_vec();
        committed.extend_from_slice(b"claim");
        let observation = json!({
            "nonce":"1", "unit":hex(b"u"), "materializedImage":hex(b"img"),
        });
        let mut wanted = REPORT_TAG.to_vec();
        wanted.extend_from_slice(b"claim");
        wanted.extend_from_slice(&[1, 255, 1, 255, b'u', 3, 255, b'i', b'm', b'g']);
        assert_eq!(expected_report_prefix(&committed, &observation).unwrap(), wanted);
        assert!(expected_report_prefix(b"claim", &observation).is_err());
        let mut report = wanted.clone();
        report.extend_from_slice(b"tail");
        let mut frame = SIGNATURE_TAG.to_vec();
        frame.extend_from_slice(b"domain-semantics");
        frame.extend_from_slice(&encode_bytes(&report));
        checked_signing_frame(&frame, &report).unwrap();
        frame.push(0);
        assert!(checked_signing_frame(&frame, &report).is_err());
        let signed = expected_signed(&report, &[7u8; 64]).unwrap();
        assert!(signed.starts_with(SIGNED_TAG));
        assert!(signed.ends_with(&encode_bytes(&[7u8; 64])));
    }

    #[test]
    fn retry_v4_completion_ingress_tag_is_distinct_from_v2() {
        assert_ne!(
            INGRESS_TAG,
            b"DREGG/APPLICATION/LIFECYCLE-COMPLETION-INGRESS/v2".as_slice()
        );
    }
}
