//! Source-authored v2 physical report for a retained v3 BEGIN and committed claim.
//! Rust supplies physical observations and signs only Mini's exact signing frame.
#![allow(dead_code)] // Physical INSTALL/START caller awaits linked v3 Host and STOP.

use crate::dispatch_author::private_signing_key;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::Journal;
use crate::lifecycle_v3_claim_native::CommittedLaunchClaim;
use crate::lifecycle_v3_native::{
    decimal, hex, text, unhex, AcceptedLaunchBegin, LaunchBeginAction,
};
use crate::resident_launch::SourceBoundLaunch;
use crate::volume_custody::VolumeWitness;
use ed25519_dalek::Signer;
use serde_json::{json, Value};
use std::fs::{DirBuilder, File};
use std::io::{self, Read};
use std::os::unix::fs::DirBuilderExt;
use std::path::{Path, PathBuf};

const MAX_REPORT: usize = 12_102_759;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

pub(crate) enum PhysicalMode<'a> {
    Materialized,
    Running {
        journal: &'a Journal,
        volume: &'a VolumeWitness,
    },
}

pub(crate) struct SignedLaunchPhysicalReport {
    pub signed_report: Vec<u8>,
    pub attempt_dir: PathBuf,
}

pub(crate) struct ReportInput<'a> {
    pub begin: &'a AcceptedLaunchBegin,
    pub claim: &'a CommittedLaunchClaim,
    pub launch: &'a SourceBoundLaunch<'a>,
    pub mode: PhysicalMode<'a>,
}

fn nonce() -> io::Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    let value = u128::from_le_bytes(bytes);
    if value == 0 {
        return Err(invalid("v3 physical nonce zero"));
    }
    Ok(value.to_string())
}

fn checked_observation(
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    launch: &SourceBoundLaunch<'_>,
    mode: &PhysicalMode<'_>,
) -> io::Result<Value> {
    let physical = &claim.physical_begin;
    if physical.operation_id != begin.authorization_operation_id
        || physical.transaction_id != claim.transaction_id
        || physical.event_id != claim.event_id
        || physical.package_sha256 != launch.signed_package_sha256()
        || physical.image_identity != hex(&launch.descriptor().package.image_identity)
    {
        return Err(invalid(
            "v3 physical observation differs from committed claim",
        ));
    }
    let (outcome, invocation, control_group, pid, witness) = match (&begin.action, mode) {
        (LaunchBeginAction::Install, PhysicalMode::Materialized) => (
            "materialized",
            String::new(),
            String::new(),
            "0".to_owned(),
            None,
        ),
        (
            LaunchBeginAction::Create(_) | LaunchBeginAction::Continue { .. },
            PhysicalMode::Running { journal, volume },
        ) => {
            let record = journal
                .read()?
                .ok_or_else(|| invalid("v3 physical Running journal absent"))?;
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
                return Err(invalid("v3 physical running unit or volume differs"));
            }
            volume.recheck_handoff()?;
            let invocation = record
                .invocation_id()
                .filter(|value| !value.is_empty())
                .ok_or_else(|| invalid("v3 physical invocation absent"))?;
            let group = record
                .control_group()
                .filter(|value| !value.is_empty())
                .ok_or_else(|| invalid("v3 physical cgroup absent"))?;
            let pid = record
                .child_pid
                .filter(|value| *value > 0)
                .ok_or_else(|| invalid("v3 physical child pid absent"))?;
            (
                "running",
                invocation.to_owned(),
                group.to_owned(),
                pid.to_string(),
                Some(&volume.bytes),
            )
        }
        _ => return Err(invalid("v3 physical report outcome differs from BEGIN")),
    };
    Ok(json!({
        "begin":hex(&begin.ingress), "committedClaim":hex(&claim.committed),
        "nonce":nonce()?, "unit":hex(physical.unit.as_bytes()),
        "materializedImage":physical.image_identity,
        "outcome":outcome, "invocationId":hex(invocation.as_bytes()),
        "controlGroup":hex(control_group.as_bytes()), "pid":pid,
        "stopAudit":Value::Null,
        "volumeWitness":witness.map(|bytes| Value::String(hex(bytes))).unwrap_or(Value::Null),
    }))
}

fn checked_report(
    view: &Value,
    report: &[u8],
    begin: &AcceptedLaunchBegin,
    claim: &CommittedLaunchClaim,
    observation: &Value,
) -> io::Result<()> {
    let same = |field: &str, expected: &str| -> io::Result<()> {
        if text(view, field)? != expected {
            return Err(invalid("v3 physical report differs from observation"));
        }
        Ok(())
    };
    same("type", "application-lifecycle-launch-physical-report-v2")?;
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
        return Err(invalid("v3 physical report source fields refused"));
    }
    let custody = view
        .get("volumeCustody")
        .ok_or_else(|| invalid("v3 physical volume custody absent"))?;
    match observation.get("volumeWitness") {
        Some(Value::Null) if custody.is_null() => {}
        Some(Value::String(witness)) => {
            if text(custody, "volumeIdHex")? != begin.volume_id_hex
                || text(custody, "physicalWitnessHex")? != witness
            {
                return Err(invalid("v3 physical source volume custody differs"));
            }
        }
        _ => return Err(invalid("v3 physical volume custody shape refused")),
    }
    Ok(())
}

/// The caller must first verify the protected image or live unit and retain
/// its exact claim. This path cannot generate a report from config identity.
pub(crate) fn prepare_once(
    operator: &PrivateOperator,
    input: ReportInput<'_>,
    custodian_seed: &Path,
    semantics: &str,
    attempt_dir: &Path,
) -> io::Result<SignedLaunchPhysicalReport> {
    let ReportInput {
        begin,
        claim,
        launch,
        mode,
    } = input;
    crate::completion_native::preflight_custodian(operator, custodian_seed, semantics)?;
    let observation = checked_observation(begin, claim, launch, &mode)?;
    let parent = attempt_dir
        .parent()
        .ok_or_else(|| invalid("v3 physical report parent absent"))?;
    private_dir(parent)?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let input = write_new(
        attempt_dir,
        "report-source.json",
        &serde_json::to_vec(&observation)?,
    )?;
    let report = operator.tool(
        "author",
        "application-lifecycle-launch-physical-report",
        &input,
        &attempt_dir.join("report.bin"),
    )?;
    if report.is_empty() || report.len() > MAX_REPORT {
        return Err(invalid("v3 physical report bound refused"));
    }
    let report_path = attempt_dir.join("report.bin");
    let inspection = operator.tool(
        "inspect",
        "application-lifecycle-launch-physical-report",
        &report_path,
        &attempt_dir.join("report-inspection.json"),
    )?;
    let view: Value = serde_json::from_slice(&inspection)?;
    checked_report(&view, &report, begin, claim, &observation)?;
    let frame_input = write_new(
        attempt_dir,
        "signing-frame-source.json",
        &serde_json::to_vec(&json!({"begin":hex(&begin.ingress),"report":hex(&report)}))?,
    )?;
    let frame = operator.tool(
        "author",
        "application-lifecycle-launch-physical-signing-frame",
        &frame_input,
        &attempt_dir.join("signing-frame.bin"),
    )?;
    if frame.is_empty() || frame.len() > MAX_REPORT {
        return Err(invalid("v3 physical signing frame bound refused"));
    }
    if let PhysicalMode::Running { .. } = &mode {
        let after = checked_observation(begin, claim, launch, &mode)?;
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
                    "v3 physical running observation changed before signing",
                ));
            }
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
        "application-lifecycle-launch-physical-signed-report",
        &signed_input,
        &attempt_dir.join("signed-report.bin"),
    )?;
    let signed_path = attempt_dir.join("signed-report.bin");
    let inspected = operator.tool(
        "inspect",
        "application-lifecycle-launch-physical-signed-report",
        &signed_path,
        &attempt_dir.join("signed-report-inspection.json"),
    )?;
    let signed_view: Value = serde_json::from_slice(&inspected)?;
    if text(&signed_view, "type")? != "application-lifecycle-launch-physical-signed-report-v2"
        || text(&signed_view, "frameHex")? != hex(&signed)
        || text(&signed_view, "signatureHex")? != hex(&signature)
    {
        return Err(invalid("v3 signed physical report differs"));
    }
    checked_report(
        signed_view
            .get("report")
            .ok_or_else(|| invalid("v3 signed physical report absent"))?,
        &report,
        begin,
        claim,
        &observation,
    )?;
    // Decode to reject a typed but noncanonical source echo before handing it to op70.
    if unhex(text(&signed_view, "frameHex")?)? != signed {
        return Err(invalid("v3 physical signed frame noncanonical"));
    }
    Ok(SignedLaunchPhysicalReport {
        signed_report: signed,
        attempt_dir: attempt_dir.to_path_buf(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hostd::VerifiedBegin;

    #[test]
    fn report_inspection_requires_exact_observation_and_source_volume() {
        let begin = AcceptedLaunchBegin {
            ingress: b"begin".to_vec(),
            action: LaunchBeginAction::Create(0),
            prior_create: None,
            client_operation_id: "1".into(),
            authorization_operation_id: "2".into(),
            volume_id_hex: "aa".repeat(32),
            snapshot_manifest: "3".into(),
            process_generation: "4".into(),
            process_identity_hex: hex(b"mini-spk-s0123456789abcdef-a5-g4.service"),
            transaction_id: "6".into(),
            event_id: "7".into(),
            accepted_count: "8".into(),
            world_root: "9".into(),
        };
        let claim = CommittedLaunchClaim {
            committed: b"committed".to_vec(),
            inspection: Vec::new(),
            claim_ingress: Vec::new(),
            physical_begin: VerifiedBegin {
                app: 5,
                generation: 4,
                operation_id: "2".into(),
                transaction_id: "10".into(),
                event_id: "11".into(),
                package_sha256: "bb".repeat(32),
                image_identity: hex(b"image"),
                process_identity: "mini-spk-s0123456789abcdef-a5-g4.service".into(),
                unit: "mini-spk-s0123456789abcdef-a5-g4.service".into(),
            },
            transaction_id: "10".into(),
            event_id: "11".into(),
            accepted_count: "12".into(),
            world_root: "13".into(),
        };
        let observation = json!({
            "nonce":"1", "unit":hex(b"mini-spk-s0123456789abcdef-a5-g4.service"),
            "materializedImage":hex(b"image"), "outcome":"running",
            "invocationId":hex(b"invocation"), "controlGroup":hex(b"group"),
            "pid":"42", "volumeWitness":hex(b"root witness"),
        });
        let report = b"source report";
        let mut inspection = json!({
            "type":"application-lifecycle-launch-physical-report-v2",
            "frameHex":hex(report), "originalBeginHex":hex(&begin.ingress),
            "committedClaimHex":hex(&claim.committed), "nonce":"1",
            "unitHex":hex(b"mini-spk-s0123456789abcdef-a5-g4.service"),
            "materializedImageHex":hex(b"image"), "outcome":"running",
            "invocationIdHex":hex(b"invocation"), "controlGroupHex":hex(b"group"),
            "pid":"42", "stopAuditHex":"", "installedManifestHex":"abcd",
            "volumeCustody":{"volumeIdHex":begin.volume_id_hex,
                "physicalWitnessHex":hex(b"root witness")},
        });
        assert!(checked_report(&inspection, report, &begin, &claim, &observation).is_ok());
        inspection["volumeCustody"]["physicalWitnessHex"] = json!("00");
        assert!(checked_report(&inspection, report, &begin, &claim, &observation).is_err());
        inspection["volumeCustody"]["physicalWitnessHex"] = json!(hex(b"root witness"));
        inspection["committedClaimHex"] = json!("00");
        assert!(checked_report(&inspection, report, &begin, &claim, &observation).is_err());
    }
}
