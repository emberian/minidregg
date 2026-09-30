//! Distinct v3 launch completion plan and one-shot event25 submission.
//! A source-authored, custodian-signed v2 physical report is required; this
//! module never encodes that report or infers process/volume evidence.
#![allow(dead_code)] // Awaiting v2 report Host route and physical caller.

use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::Journal;
use crate::lifecycle_v3_claim_native::{later_decimal, CommittedLaunchClaim};
use crate::lifecycle_v3_native::{
    decimal, framed_payload, hex, lowercase_hex, sign_pinned_slots, text, AcceptedLaunchBegin,
    LaunchBeginAction,
};
use crate::resident_launch::SourceBoundLaunch;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-LAUNCH-COMPLETION-OPERATOR-PLAN/v1";
const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-COMPLETION-INGRESS/v2";
const OUTCOME_TAG: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v2";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn number(value: &Value) -> io::Result<String> {
    let result = value
        .as_str()
        .map(str::to_owned)
        .or_else(|| value.as_u64().map(|number| number.to_string()))
        .ok_or_else(|| invalid("v3 completion management number malformed"))?;
    if !decimal(&result) {
        return Err(invalid("v3 completion management number noncanonical"));
    }
    Ok(result)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct FixedLaunchCompletionSigners {
    protocol: String,
    app: String,
    package_manifest: String,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl FixedLaunchCompletionSigners {
    pub(crate) fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-completion-management-v1"
            || self.signers.is_empty()
            || self.signers.len() > 64
            || ![&self.app, &self.package_manifest, &self.management_subject]
                .iter()
                .all(|value| decimal(value))
        {
            return Err(invalid("v3 completion fixed management refused"));
        }
        let config: Value = serde_json::from_slice(&operator.pinned_config()?)?;
        let manager = config
            .get("completionManagement")
            .ok_or_else(|| invalid("Mini completion management pin absent"))?;
        for (field, expected) in [
            ("app", &self.app),
            ("packageManifest", &self.package_manifest),
            ("managementSubject", &self.management_subject),
        ] {
            if number(
                manager
                    .get(field)
                    .ok_or_else(|| invalid("Mini completion management field absent"))?,
            )? != *expected
            {
                return Err(invalid("v3 completion signer differs from Mini pin"));
            }
        }
        let key_id = number(
            manager
                .get("managementKeyId")
                .ok_or_else(|| invalid("Mini completion management key absent"))?,
        )?;
        for signer in &self.signers {
            if signer.key_id != key_id {
                return Err(invalid("v3 completion signer key differs from Mini pin"));
            }
            crate::sandbox::open_protected_directory(
                signer
                    .seed_path
                    .parent()
                    .ok_or_else(|| invalid("v3 completion signer parent absent"))?,
                app_uid,
                false,
            )?;
        }
        Ok(())
    }

    fn checked_slots<'a>(
        &self,
        view: &'a Value,
        evidence: &CompletionEvidence<'_>,
    ) -> io::Result<&'a [Value]> {
        if text(view, "type")? != "application-lifecycle-launch-completion-plan-v1"
            || text(view, "canonicalPlanHex")? != hex(evidence.plan)
            || text(view, "canonicalRequestHex")? != hex(evidence.request)
            || text(view, "originalBeginHex")? != hex(evidence.begin)
            || text(view, "originalClaimHex")? != hex(evidence.claim)
            || text(view, "signedReportHex")? != hex(evidence.report)
            || text(view, "app")? != self.app
            || text(view, "descriptorRoot")? != evidence.descriptor_root
            || text(view, "volumeIdHex")? != evidence.volume_id_hex
            || !lowercase_hex(text(view, "sourceHex")?)
            || text(view, "sourceHex")?.is_empty()
            || !decimal(text(view, "currentAuthorityRoot")?)
            || !decimal(text(view, "currentAppRoot")?)
            || !decimal(text(view, "currentPackageRoot")?)
            || !decimal(text(view, "imageBoundary")?)
            || !decimal(text(view, "height")?)
        {
            return Err(invalid(
                "v3 completion plan differs from retained lifecycle",
            ));
        }
        let slots = view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or_else(|| invalid("v3 completion signing slots absent"))?;
        if slots.len() != self.signers.len() {
            return Err(invalid("v3 completion signing slot count differs"));
        }
        Ok(slots)
    }
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

pub(crate) struct CompletionInput<'a> {
    pub begin: &'a AcceptedLaunchBegin,
    pub claim: &'a CommittedLaunchClaim,
    pub launch: &'a SourceBoundLaunch<'a>,
    pub signed_report: &'a [u8],
}

pub(crate) struct AssembledLaunchCompletion {
    attempt_dir: PathBuf,
    active_marker: Vec<u8>,
    ingress: Vec<u8>,
    begin_sha256: String,
    claim_sha256: String,
    report_sha256: String,
}

pub(crate) struct ConfirmedLaunchCompletion {
    pub transaction_id: String,
    pub event_id: String,
    pub accepted_count: String,
    pub image_boundary: String,
}

/// Historical evidence only. This cannot authorize a second physical launch.
pub(crate) struct RecoveredLaunchCompletion {
    pub receipt: ConfirmedLaunchCompletion,
    pub inspection_name: String,
    pub inspection_sha256: String,
}

pub(crate) fn checked_receipt(
    view: &Value,
    confirmation: &str,
    prior_accepted_count: &str,
) -> io::Result<ConfirmedLaunchCompletion> {
    if text(view, "type")? != "confirmed" || text(view, "confirmation")? != confirmation {
        return Err(invalid("v3 completion receipt confirmation refused"));
    }
    let receipt = |name| -> io::Result<String> {
        let value = text(view, name)?;
        if !decimal(value) {
            return Err(invalid("v3 completion receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    let confirmed = ConfirmedLaunchCompletion {
        transaction_id: receipt("transactionId")?,
        event_id: receipt("eventId")?,
        accepted_count: receipt("acceptedCount")?,
        image_boundary: receipt("imageBoundary")?,
    };
    if !later_decimal(&confirmed.accepted_count, prior_accepted_count) {
        return Err(invalid(
            "v3 completion receipt does not follow retained claim",
        ));
    }
    Ok(confirmed)
}

/// Op70/71 are current-image authoring only. The caller supplies an exact
/// source-authored signed V2 physical report; op38 admission is separate.
pub(crate) fn assemble_once(
    operator: &PrivateOperator,
    fixed: &FixedLaunchCompletionSigners,
    app_uid: u32,
    input: CompletionInput<'_>,
    attempt_dir: &Path,
) -> io::Result<AssembledLaunchCompletion> {
    let CompletionInput {
        begin,
        claim,
        launch,
        signed_report,
    } = input;
    fixed.validate(operator, app_uid)?;
    if signed_report.is_empty() || signed_report.len() > 12_102_759 {
        return Err(invalid("v3 signed physical report bound refused"));
    }
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v3 completion attempt parent absent"))?;
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
        "application-lifecycle-launch-completion-request",
        &source_path,
        &attempt_dir.join("request.bin"),
    )?;
    let request_path = attempt_dir.join("request.bin");
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-launch-completion-request",
        &request_path,
        &attempt_dir.join("request-inspection.json"),
    )?;
    let request_view: Value = serde_json::from_slice(&inspected)?;
    if text(&request_view, "type")? != "application-lifecycle-launch-completion-request-v1"
        || text(&request_view, "canonicalRequestHex")? != hex(&request)
        || text(&request_view, "originalBeginHex")? != hex(&begin.ingress)
        || text(&request_view, "originalClaimHex")? != hex(&claim.claim_ingress)
        || text(&request_view, "signedReportHex")? != hex(signed_report)
        || text(&request_view, "app")? != fixed.app
        || text(&request_view, "descriptorRoot")? != launch.descriptor().root
        || text(&request_view, "volumeIdHex")? != begin.volume_id_hex
    {
        return Err(invalid(
            "v3 completion request differs from retained lifecycle",
        ));
    }
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-launch-completion-prepare-requested-v1",
        "requestSha256":hex(&Sha256::digest(&request)),
        "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
        "originalClaimSha256":hex(&Sha256::digest(&claim.claim_ingress)),
        "signedReportSha256":hex(&Sha256::digest(signed_report)),
    }))?;
    write_new(attempt_dir, "op70-requested.json", &active)?;
    write_new(parent, "lifecycle-completion-v2-active.json", &active)?;
    let reply = operator.invoke(70, &request)?;
    write_new(attempt_dir, "op70-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 70, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-launch-completion-plan",
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
    write_new(attempt_dir, "completion-v2.bin", &ingress)?;
    Ok(AssembledLaunchCompletion {
        attempt_dir: attempt_dir.to_path_buf(),
        active_marker: active,
        ingress,
        begin_sha256: hex(&Sha256::digest(&begin.ingress)),
        claim_sha256: hex(&Sha256::digest(&claim.claim_ingress)),
        report_sha256: hex(&Sha256::digest(signed_report)),
    })
}

fn checked_assembled(
    assembled: &AssembledLaunchCompletion,
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    signed_report: &[u8],
) -> io::Result<()> {
    let attempt = &assembled.attempt_dir;
    private_dir(attempt)?;
    let parent = attempt
        .parent()
        .ok_or_else(|| invalid("v3 completion parent absent"))?;
    private_dir(parent)?;
    if fs::read(parent.join("lifecycle-completion-v2-active.json"))? != assembled.active_marker
        || fs::read(attempt.join("completion-v2.bin"))? != assembled.ingress
        || assembled.begin_sha256 != hex(&Sha256::digest(&begin.ingress))
        || assembled.claim_sha256 != hex(&Sha256::digest(&claim.claim_ingress))
        || assembled.report_sha256 != hex(&Sha256::digest(signed_report))
    {
        return Err(invalid(
            "v3 completion attempt artifacts differ before submit",
        ));
    }
    Ok(())
}

fn retained_file(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o600
        || metadata.len() == 0
        || metadata.len() > max
    {
        return Err(invalid("v3 completion retained artifact identity refused"));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let opened = file.metadata()?;
    if opened.dev() != metadata.dev() || opened.ino() != metadata.ino() {
        return Err(invalid("v3 completion retained artifact changed"));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.by_ref().take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != metadata.len() {
        return Err(invalid("v3 completion retained artifact length changed"));
    }
    Ok(bytes)
}

/// Reopens one protected op71 result after process restart. The caller must
/// supply its separately retained original BEGIN, claim and signed report;
/// the active marker and all three hashes are compared before op39 lookup.
pub(crate) fn load_retained(
    attempt_dir: &Path,
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    signed_report: &[u8],
) -> io::Result<AssembledLaunchCompletion> {
    private_dir(attempt_dir)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v3 completion retained parent absent"))?;
    private_dir(parent)?;
    let active_marker = retained_file(&parent.join("lifecycle-completion-v2-active.json"), 4096)?;
    let view: Value = serde_json::from_slice(&active_marker)?;
    if text(&view, "protocol")? != "mini-spk-launch-completion-prepare-requested-v1"
        || text(&view, "originalBeginSha256")? != hex(&Sha256::digest(&begin.ingress))
        || text(&view, "originalClaimSha256")? != hex(&Sha256::digest(&claim.claim_ingress))
        || text(&view, "signedReportSha256")? != hex(&Sha256::digest(signed_report))
    {
        return Err(invalid("v3 completion retained marker differs"));
    }
    let request = retained_file(&attempt_dir.join("request.bin"), 12_102_759)?;
    if text(&view, "requestSha256")? != hex(&Sha256::digest(&request)) {
        return Err(invalid("v3 completion retained request differs"));
    }
    let ingress = retained_file(&attempt_dir.join("completion-v2.bin"), 12_102_759)?;
    let assembled = AssembledLaunchCompletion {
        attempt_dir: attempt_dir.to_path_buf(),
        active_marker,
        ingress,
        begin_sha256: hex(&Sha256::digest(&begin.ingress)),
        claim_sha256: hex(&Sha256::digest(&claim.claim_ingress)),
        report_sha256: hex(&Sha256::digest(signed_report)),
    };
    checked_assembled(&assembled, begin, claim, signed_report)?;
    Ok(assembled)
}

/// Op38 has no physical authority on a replayed or uncertain outcome. The
/// caller's exact mode is checked against its source-selected BEGIN action.
pub(crate) fn submit_fresh_once(
    operator: &PrivateOperator,
    assembled: &AssembledLaunchCompletion,
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    signed_report: &[u8],
    running_journal: Option<&Journal>,
) -> io::Result<ConfirmedLaunchCompletion> {
    checked_assembled(assembled, begin, claim, signed_report)?;
    match (&begin.action, running_journal) {
        (LaunchBeginAction::Install, None) => {}
        (LaunchBeginAction::Create(_) | LaunchBeginAction::Continue { .. }, Some(journal)) => {
            let record = journal
                .read()?
                .ok_or_else(|| invalid("v3 START physical journal absent"))?;
            record.verify_running_instance()?;
            if record.app() != claim.physical_begin.app
                || record.generation() != claim.physical_begin.generation
                || record.unit() != claim.physical_begin.unit
                || record.transaction_id() != claim.physical_begin.transaction_id
                || record.event_id() != claim.physical_begin.event_id
            {
                return Err(invalid("v3 START running journal differs from fresh claim"));
            }
        }
        _ => return Err(invalid("v3 completion physical phase differs from BEGIN")),
    }
    let attempt = &assembled.attempt_dir;
    let marker = json!({
        "protocol":"mini-spk-launch-completion-submit-requested-v1",
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
    if let Some(journal) = running_journal {
        journal
            .read()?
            .ok_or_else(|| invalid("v3 START journal lost after completion"))?
            .verify_running_instance()?;
    }
    Ok(confirmed)
}

/// Op39 reads the exact original event25 receipt after an uncertain op38.
/// The retained one-shot marker and ingress are mandatory; this never invokes
/// op38, assembles another ingress, or converts history into launch authority.
pub(crate) fn recover_receipt_only(
    operator: &PrivateOperator,
    assembled: &AssembledLaunchCompletion,
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    signed_report: &[u8],
) -> io::Result<RecoveredLaunchCompletion> {
    checked_assembled(assembled, begin, claim, signed_report)?;
    let attempt = &assembled.attempt_dir;
    let marker: Value = serde_json::from_slice(&fs::read(attempt.join("op38-requested.json"))?)?;
    if text(&marker, "protocol")? != "mini-spk-launch-completion-submit-requested-v1"
        || text(&marker, "ingressSha256")? != hex(&Sha256::digest(&assembled.ingress))
        || text(&marker, "claimSha256")? != hex(&Sha256::digest(&claim.committed))
    {
        return Err(invalid("v3 completion original submit marker differs"));
    }
    // A lookup may be repeated after another lost reply. Each read-only probe
    // owns fresh output paths; the original op38 marker and ingress stay fixed.
    let mut nonce = [0u8; 16];
    std::fs::File::open("/dev/urandom")?.read_exact(&mut nonce)?;
    let lookup_dir = attempt.join(format!("op39-lookup-{}", hex(&nonce)));
    DirBuilder::new().mode(0o700).create(&lookup_dir)?;
    let reply = operator.invoke(39, &assembled.ingress)?;
    let payload = framed_payload(&reply, 39, OUTCOME_TAG)?;
    let payload_path = write_new(&lookup_dir, "outcome.bin", payload)?;
    let inspected = operator.tool(
        "inspect",
        "outcome",
        &payload_path,
        &lookup_dir.join("outcome.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let lookup_name = lookup_dir
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| invalid("v3 completion lookup name absent"))?;
    Ok(RecoveredLaunchCompletion {
        receipt: checked_receipt(&view, "replayed", &claim.accepted_count)?,
        inspection_name: format!("{lookup_name}/outcome.json"),
        inspection_sha256: hex(&Sha256::digest(&inspected)),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hostd::VerifiedBegin;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn completion_plan_pins_exact_begin_claim_report_and_volume() {
        let fixed = FixedLaunchCompletionSigners {
            protocol: "mini-spk-completion-management-v1".into(),
            app: "5".into(),
            package_manifest: "6".into(),
            management_subject: "7".into(),
            signers: vec![],
        };
        let evidence = CompletionEvidence {
            plan: b"plan",
            request: b"request",
            begin: b"begin",
            claim: b"claim",
            descriptor_root: "8",
            volume_id_hex: "aa",
            report: b"signed report",
        };
        let mut view = json!({
            "type":"application-lifecycle-launch-completion-plan-v1",
            "canonicalPlanHex":hex(evidence.plan),
            "canonicalRequestHex":hex(evidence.request),
            "sourceHex":"abcd",
            "originalBeginHex":hex(evidence.begin),
            "originalClaimHex":hex(evidence.claim),
            "signedReportHex":hex(evidence.report),
            "app":"5", "descriptorRoot":"8", "volumeIdHex":"aa",
            "currentAuthorityRoot":"1", "currentAppRoot":"2",
            "currentPackageRoot":"3", "imageBoundary":"4", "height":"5",
            "slots":[],
        });
        assert!(fixed.checked_slots(&view, &evidence).is_ok());
        for (field, wrong) in [
            ("originalBeginHex", "00"),
            ("originalClaimHex", "00"),
            ("signedReportHex", "00"),
            ("volumeIdHex", "bb"),
            ("descriptorRoot", "9"),
        ] {
            let saved = view[field].clone();
            view[field] = json!(wrong);
            assert!(fixed.checked_slots(&view, &evidence).is_err());
            view[field] = saved;
        }
    }

    #[test]
    fn event25_ingress_and_fresh_outcome_tags_do_not_alias() {
        let frame = |operation: u8, tag: &[u8]| {
            let mut result = ((tag.len() + 2) as u32).to_le_bytes().to_vec();
            result.push(operation);
            result.extend_from_slice(tag);
            result.push(0);
            result
        };
        let ingress = frame(71, INGRESS_TAG);
        assert!(framed_payload(&ingress, 71, INGRESS_TAG).is_ok());
        assert!(framed_payload(&ingress, 38, OUTCOME_TAG).is_err());
        assert!(framed_payload(
            &ingress,
            71,
            b"DREGG/APPLICATION/LIFECYCLE-COMPLETION-INGRESS/v1"
        )
        .is_err());
    }

    #[test]
    fn completion_receipt_order_and_historical_kind_are_distinct() {
        let prior = "340282366920938463463374607431768211455";
        let mut view = json!({
            "type":"confirmed", "confirmation":"installed",
            "transactionId":"1", "eventId":"2",
            "acceptedCount":"340282366920938463463374607431768211456",
            "imageBoundary":"3",
        });
        assert!(checked_receipt(&view, "installed", prior).is_ok());
        assert!(checked_receipt(&view, "replayed", prior).is_err());
        view["confirmation"] = json!("replayed");
        assert!(checked_receipt(&view, "replayed", prior).is_ok());
        assert!(checked_receipt(&view, "installed", prior).is_err());
        view["acceptedCount"] = json!(prior);
        assert!(checked_receipt(&view, "replayed", prior).is_err());
        view["acceptedCount"] = json!("0");
        assert!(checked_receipt(&view, "replayed", prior).is_err());
    }

    #[test]
    fn retained_completion_recovery_requires_exact_originals_and_submit_marker() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let parent = std::env::temp_dir().join(format!(
            "spk-v3-completion-recovery-{}-{stamp}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&parent).unwrap();
        let attempt = parent.join("completion");
        DirBuilder::new().mode(0o700).create(&attempt).unwrap();
        let begin = AcceptedLaunchBegin {
            ingress: b"begin".to_vec(),
            action: LaunchBeginAction::Install,
            prior_create: None,
            client_operation_id: "1".into(),
            authorization_operation_id: "2".into(),
            volume_id_hex: "aa".repeat(32),
            snapshot_manifest: "3".into(),
            process_generation: "4".into(),
            process_identity_hex: "".into(),
            transaction_id: "5".into(),
            event_id: "6".into(),
            accepted_count: "7".into(),
            image_boundary: "8".into(),
        };
        let claim = CommittedLaunchClaim {
            committed: b"committed".to_vec(),
            inspection: Vec::new(),
            claim_ingress: b"claim".to_vec(),
            physical_begin: VerifiedBegin {
                app: 1,
                generation: 4,
                operation_id: "2".into(),
                transaction_id: "9".into(),
                event_id: "10".into(),
                package_sha256: "aa".repeat(32),
                image_identity: "bb".repeat(32),
                process_identity: "unit".into(),
                unit: "unit".into(),
            },
            transaction_id: "9".into(),
            event_id: "10".into(),
            accepted_count: "11".into(),
            image_boundary: "12".into(),
        };
        let report = b"signed report";
        let request = b"request";
        let ingress = b"ingress";
        let active = serde_json::to_vec(&json!({
            "protocol":"mini-spk-launch-completion-prepare-requested-v1",
            "requestSha256":hex(&Sha256::digest(request)),
            "originalBeginSha256":hex(&Sha256::digest(&begin.ingress)),
            "originalClaimSha256":hex(&Sha256::digest(&claim.claim_ingress)),
            "signedReportSha256":hex(&Sha256::digest(report)),
        }))
        .unwrap();
        write_new(&parent, "lifecycle-completion-v2-active.json", &active).unwrap();
        write_new(&attempt, "request.bin", request).unwrap();
        write_new(&attempt, "completion-v2.bin", ingress).unwrap();
        assert!(load_retained(&attempt, &begin, &claim, report).is_ok());
        assert!(load_retained(&attempt, &begin, &claim, b"other report").is_err());
        let submit = serde_json::to_vec(&json!({
            "protocol":"mini-spk-launch-completion-submit-requested-v1",
            "ingressSha256":hex(&Sha256::digest(ingress)),
            "claimSha256":hex(&Sha256::digest(&claim.committed)),
        }))
        .unwrap();
        write_new(&attempt, "op38-requested.json", &submit).unwrap();
        assert_eq!(
            fs::read(attempt.join("op38-requested.json")).unwrap(),
            submit
        );
        fs::remove_dir_all(parent).unwrap();
    }
}
