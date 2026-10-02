//! One source-authorized STOP of a previously completed resident incarnation.
//!
//! The only physical fence entry consumes a sealed fresh op26 callback. After
//! a crash, retained artifacts may resume an already-fsynced Fenced journal
//! or audit Stopped, but can never mint another fresh callback or fence Running.

use crate::completion_native::preflight_custodian;
use crate::dispatch_author::private_signing_key;
use crate::dispatch_author::SignerPin;
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::{Journal, Phase, UnitStopAudit};
use crate::lifecycle_v3_native::{decimal, framed_payload, hex, sign_pinned_slots, text};
use crate::lifecycle_v3_stop_assembly_native::{self, FixedStopClaimSigners};
use crate::lifecycle_v3_stop_begin_native::{self, FixedStopBeginSigners};
use crate::lifecycle_v3_stop_claim_native::ExactReceipt;
use crate::lifecycle_v3_stop_native::{self, ReceiptFields, StopTarget};
use crate::materialize::verify_installed_spk;
use crate::resident_launch::SourceBoundLaunch;
use crate::volume_custody::{read_attested_volume, VolumeSite, VolumeWitness};
use ed25519_dalek::Signer;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, DirBuilder, File, OpenOptions};
use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const MAX_CONFIG: u64 = 65_536;
const MAX_FRAME: u64 = 12_102_760;
const MAX_INSPECTION: u64 = 2 * 1024 * 1024;
const MAX_AUTHOR_JSON: u64 = 22 * 1024 * 1024;
const REPORT_BOUND: usize = 12_102_759;
const PLAN_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-LAUNCH-COMPLETION-OPERATOR-PLAN/v1";
const INGRESS_TAG: &[u8] = b"DREGG/APPLICATION/LIFECYCLE-COMPLETION-INGRESS/v2";
const OUTCOME_TAG: &[u8] = b"DREGG/NATIVE-HOST/OUTCOME/v4";

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn absent(path: &Path) -> io::Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(false),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Ok(true),
        Err(error) => Err(error),
    }
}

/// One live STOP supervisor owns all attempt selection, source authoring,
/// physical audit, and op38 disposition. A second process must not mistake
/// the first process's unfinished pre-submit directory for a crashed attempt.
fn acquire_run_lock(journal_dir: &Path) -> io::Result<File> {
    private_dir(journal_dir)?;
    let path = journal_dir.join(".resident-stop.lock");
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)?;
    let named = fs::symlink_metadata(&path)?;
    let opened = lock.metadata()?;
    if !opened.is_file()
        || named.dev() != opened.dev()
        || named.ino() != opened.ino()
        || opened.uid() != unsafe { libc::geteuid() }
        || opened.nlink() != 1
        || opened.permissions().mode() & 0o777 != 0o600
    {
        return Err(invalid("STOP supervisor lock identity refused"));
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        let error = io::Error::last_os_error();
        return if matches!(error.raw_os_error(), Some(libc::EWOULDBLOCK)) {
            Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "resident STOP supervisor already active",
            ))
        } else {
            Err(error)
        };
    }
    let named = fs::symlink_metadata(&path)?;
    if named.dev() != opened.dev() || named.ino() != opened.ino() {
        return Err(invalid("STOP supervisor lock path changed"));
    }
    Ok(lock)
}

fn read_private(path: &Path, maximum: u64) -> io::Result<Vec<u8>> {
    private_dir(
        path.parent()
            .ok_or_else(|| invalid("STOP file parent absent"))?,
    )?;
    let named = fs::symlink_metadata(path)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let before = file.metadata()?;
    if !path.is_absolute()
        || !before.is_file()
        || named.dev() != before.dev()
        || named.ino() != before.ino()
        || before.uid() != unsafe { libc::geteuid() }
        || before.nlink() != 1
        || before.permissions().mode() & 0o777 != 0o600
        || before.len() == 0
        || before.len() > maximum
    {
        return Err(invalid("STOP retained file identity refused"));
    }
    let mut bytes = Vec::with_capacity(before.len() as usize);
    file.by_ref().take(maximum + 1).read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if bytes.len() as u64 != before.len()
        || after.dev() != before.dev()
        || after.ino() != before.ino()
        || after.len() != before.len()
        || after.mtime() != before.mtime()
        || after.mtime_nsec() != before.mtime_nsec()
        || after.ctime() != before.ctime()
        || after.ctime_nsec() != before.ctime_nsec()
    {
        return Err(invalid("STOP retained file changed during read"));
    }
    Ok(bytes)
}

fn ensure_artifact(directory: &Path, name: &str, expected: &[u8], bound: u64) -> io::Result<()> {
    let path = directory.join(name);
    if absent(&path)? {
        write_new(directory, name, expected)?;
    } else if read_private(&path, bound)? != expected {
        return Err(invalid(
            "STOP partial artifact differs from source rederivation",
        ));
    }
    Ok(())
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct StopConfig {
    protocol: String,
    resident_start_config: PathBuf,
    begin_attempt_dir: PathBuf,
    claim_author_attempt_dir: PathBuf,
    claim_attempt_dir: PathBuf,
    report_attempt_dir: PathBuf,
    completion_attempt_dir: PathBuf,
}

/// A strict subset of the already protected START config. Additional START
/// fields (HTTP entrances, agent custody and sandbox) cannot authorize STOP.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ResidentPins {
    protocol: String,
    journal_dir: PathBuf,
    image_dir: PathBuf,
    expected_raw_sha256: String,
    launch_qualification: PathBuf,
    volume_resource: u64,
    expected_volume_id: String,
    persistent_var: PathBuf,
    persistent_var_max_bytes: u64,
    grains_root: PathBuf,
    #[serde(default)]
    broker_socket: Option<PathBuf>,
    store: String,
    deployment_id: String,
    host_id: String,
    app_uid: u32,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    mini_operator_socket: PathBuf,
    begin_management_custody: PathBuf,
    claim_management_custody: PathBuf,
    completion_management_custody: PathBuf,
    completion_custodian_seed: PathBuf,
    completion_semantics: String,
    begin_operation_ledger: PathBuf,
    claim_nonce_ledger: PathBuf,
    descriptor_attempt_dir: PathBuf,
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn load_config(path: &Path) -> io::Result<(StopConfig, ResidentPins)> {
    let config: StopConfig = serde_json::from_slice(&read_private(path, MAX_CONFIG)?)?;
    let pins: ResidentPins =
        serde_json::from_slice(&read_private(&config.resident_start_config, MAX_CONFIG)?)?;
    let dir = &pins.journal_dir;
    if config.protocol != "mini-spk-resident-stop-v3"
        || pins.protocol != "mini-spk-resident-start-v3"
        || path.parent() != Some(dir.as_path())
        || config.resident_start_config.parent() != Some(dir.as_path())
        || config.begin_attempt_dir.parent() != Some(dir.as_path())
        || config.claim_author_attempt_dir.parent() != Some(dir.as_path())
        || config.claim_attempt_dir.parent() != Some(dir.as_path())
        || config.report_attempt_dir.parent() != Some(dir.as_path())
        || config.completion_attempt_dir.parent() != Some(dir.as_path())
        || pins.descriptor_attempt_dir.parent() != Some(dir.as_path())
        || pins.begin_operation_ledger.parent() != Some(dir.as_path())
        || pins.claim_nonce_ledger.parent() != Some(dir.as_path())
        || !hex64(&pins.expected_raw_sha256)
        || !hex64(&pins.expected_volume_id)
        || !hex64(&pins.deployment_id)
        || !hex64(&pins.host_id)
        || pins.volume_resource == 0
        || pins.app_uid == 0
        || pins.persistent_var_max_bytes == 0
        || !decimal(&pins.completion_semantics)
        || ![
            &pins.image_dir,
            &pins.launch_qualification,
            &pins.persistent_var,
            &pins.mini_host,
            &pins.mini_config,
            &pins.mini_operator_socket,
            &pins.begin_management_custody,
            &pins.claim_management_custody,
            &pins.completion_management_custody,
            &pins.completion_custodian_seed,
        ]
        .iter()
        .all(|path| path.is_absolute())
    {
        return Err(invalid("resident STOP config or START pin refused"));
    }
    let attempts = [
        &config.begin_attempt_dir,
        &config.claim_author_attempt_dir,
        &config.claim_attempt_dir,
        &config.report_attempt_dir,
        &config.completion_attempt_dir,
    ];
    if attempts.iter().enumerate().any(|(index, path)| {
        attempts[..index].contains(path) || **path == pins.descriptor_attempt_dir
    }) {
        return Err(invalid("resident STOP attempt paths overlap"));
    }
    Ok((config, pins))
}

fn receipt(value: &Value) -> io::Result<ExactReceipt> {
    ExactReceipt::new(
        text(value, "transactionId")?,
        text(value, "eventId")?,
        text(value, "acceptedCount")?,
        text(value, "worldRoot")?,
    )
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct QualifiedLaunch {
    protocol: String,
    raw_sha256: String,
    package_root: String,
    launch_root: String,
    launch_canonical_sha256: String,
    create_count: String,
    create_digests: Vec<String>,
    continue_digest: String,
}

fn match_qualification(pins: &ResidentPins, launch: &SourceBoundLaunch<'_>) -> io::Result<()> {
    let saved: QualifiedLaunch =
        serde_json::from_slice(&read_private(&pins.launch_qualification, MAX_CONFIG)?)?;
    let descriptor = launch.descriptor();
    if saved.protocol != "mini-spk-launch-qualified-v2"
        || saved.raw_sha256 != pins.expected_raw_sha256
        || saved.raw_sha256 != launch.signed_package_sha256()
        || saved.package_root != descriptor.package.root
        || saved.launch_root != descriptor.root
        || saved.launch_canonical_sha256 != hex(&Sha256::digest(&descriptor.canonical))
        || saved.create_count != descriptor.create_digests.len().to_string()
        || saved.create_digests != descriptor.create_digests
        || saved.continue_digest != descriptor.continue_digest
    {
        return Err(invalid(
            "STOP launch differs from retained signed qualification",
        ));
    }
    Ok(())
}

struct StopEvidence {
    target: StopTarget,
    begin: Vec<u8>,
    claim_ingress: Vec<u8>,
    committed: Vec<u8>,
    claim_receipt: ExactReceipt,
}

/// Re-inspect the exact first fresh op26 callback against current Verified
/// history. This produces no physical permit; the durable fence marker and
/// journal phase decide which recovery action, if any, remains possible.
fn inspect_original(
    operator: &PrivateOperator,
    claim_dir: &Path,
    probe_dir: &Path,
) -> io::Result<StopEvidence> {
    private_dir(claim_dir)?;
    let plan = read_private(&claim_dir.join("stop-plan-v2.bin"), MAX_FRAME)?;
    let begin = read_private(&claim_dir.join("original-begin-v3.bin"), MAX_FRAME)?;
    let claim_ingress = read_private(&claim_dir.join("claim-ingress-v3.bin"), MAX_FRAME)?;
    let committed = read_private(&claim_dir.join("committed-v3.bin"), MAX_FRAME)?;
    let original_frame = read_private(&claim_dir.join("op26-frame.bin"), MAX_FRAME)?;
    let committed_tag = b"DREGG/APPLICATION/LIFECYCLE-CLAIM-COMMITTED/v3";
    if framed_payload(&original_frame, 26, committed_tag)? != committed {
        return Err(invalid("STOP original fresh callback differs"));
    }
    let requested: Value = serde_json::from_slice(&read_private(
        &claim_dir.join("op26-requested.json"),
        MAX_CONFIG,
    )?)?;
    if text(&requested, "protocol")? != "mini-spk-stop-claim-op26-requested-v1"
        || text(&requested, "stopPlanSha256")? != hex(&Sha256::digest(&plan))
        || text(&requested, "originalBeginSha256")? != hex(&Sha256::digest(&begin))
        || text(&requested, "claimIngressSha256")? != hex(&Sha256::digest(&claim_ingress))
    {
        return Err(invalid("STOP original request marker differs"));
    }
    let begin_receipt = receipt(
        requested
            .get("beginReceipt")
            .ok_or_else(|| invalid("STOP original BEGIN receipt absent"))?,
    )?;
    let committed_view: Value = serde_json::from_slice(&read_private(
        &claim_dir.join("committed-v3.json"),
        MAX_INSPECTION,
    )?)?;
    if text(&committed_view, "type")? != "application-lifecycle-claim-committed-v3"
        || text(&committed_view, "kind")? != "stop"
        || text(&committed_view, "frameHex")? != hex(&committed)
        || text(&committed_view, "originalClaimHex")? != hex(&claim_ingress)
        || text(&committed_view, "originalBeginHex")? != hex(&begin)
    {
        return Err(invalid("STOP original claim inspection differs"));
    }
    let claim_receipt = receipt(
        committed_view
            .get("receipt")
            .ok_or_else(|| invalid("STOP original claim receipt absent"))?,
    )?;
    private_dir(
        probe_dir
            .parent()
            .ok_or_else(|| invalid("STOP probe parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(probe_dir)?;
    let plan_path = write_new(probe_dir, "stop-plan-v2.bin", &plan)?;
    let committed_path = write_new(probe_dir, "committed-v3.bin", &committed)?;
    let output_path = probe_dir.join("current.json");
    let _ = operator.pinned_config()?;
    let status = Command::new(&operator.host)
        .arg(&operator.config)
        .arg("inspect-stop-claim")
        .arg(&plan_path)
        .arg(&committed_path)
        .arg(&output_path)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()?;
    if !status.success() {
        return Err(invalid("pinned STOP current source inspection refused"));
    }
    let _ = operator.pinned_config()?;
    let inspection = fs::read(&output_path)?;
    if inspection.is_empty() || inspection.len() as u64 > MAX_INSPECTION {
        return Err(invalid("STOP current source inspection bound refused"));
    }
    let target = StopTarget::from_verified_inspection(
        &plan,
        &committed,
        &begin,
        &inspection,
        ReceiptFields {
            transaction_id: begin_receipt.transaction_id(),
            event_id: begin_receipt.event_id(),
            accepted_count: begin_receipt.accepted_count(),
            world_root: begin_receipt.world_root(),
        },
        ReceiptFields {
            transaction_id: claim_receipt.transaction_id(),
            event_id: claim_receipt.event_id(),
            accepted_count: claim_receipt.accepted_count(),
            world_root: claim_receipt.world_root(),
        },
    )?;
    target.check_marker(claim_dir)?;
    Ok(StopEvidence {
        target,
        begin,
        claim_ingress,
        committed,
        claim_receipt,
    })
}

fn fresh_probe(journal_dir: &Path, label: &str) -> io::Result<PathBuf> {
    let mut random = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut random)?;
    Ok(journal_dir.join(format!("{label}-{}", hex(&random))))
}

fn nonce() -> io::Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    let number = u128::from_le_bytes(bytes);
    if number == 0 {
        return Err(invalid("STOP report nonce zero"));
    }
    Ok(number.to_string())
}

fn checked_report_view(
    view: &Value,
    report: &[u8],
    evidence: &StopEvidence,
    observation: &Value,
    volume: &VolumeWitness,
) -> io::Result<()> {
    for (name, expected) in [
        ("type", "application-lifecycle-launch-physical-report-v2"),
        ("frameHex", hex(report).as_str()),
        ("originalBeginHex", hex(&evidence.begin).as_str()),
        ("committedClaimHex", hex(&evidence.committed).as_str()),
        ("nonce", text(observation, "nonce")?),
        ("unitHex", text(observation, "unit")?),
        (
            "materializedImageHex",
            text(observation, "materializedImage")?,
        ),
        ("outcome", "stopped"),
        ("invocationIdHex", text(observation, "invocationId")?),
        ("controlGroupHex", text(observation, "controlGroup")?),
        ("pid", "0"),
    ] {
        if text(view, name)? != expected {
            return Err(invalid(
                "STOP source report differs from checked physical audit",
            ));
        }
    }
    if !decimal(text(view, "nonce")?)
        || text(view, "stopAuditHex")?.is_empty()
        || text(view, "installedManifestHex")?.is_empty()
    {
        return Err(invalid("STOP typed source audit or manifest absent"));
    }
    let custody = view
        .get("volumeCustody")
        .ok_or_else(|| invalid("STOP volume custody absent"))?;
    if text(custody, "volumeIdHex")? != volume.volume_id
        || text(custody, "physicalWitnessHex")? != hex(&volume.bytes)
    {
        return Err(invalid("STOP source report volume differs"));
    }
    Ok(())
}

/// Source-author/sign one v2 stopped report. The exact typed hostd audit was
/// obtained only after an under-lock fence or read-only Stopped verification.
struct ReportCustody<'a> {
    seed: &'a Path,
    semantics: &'a str,
}

fn prepare_report(
    operator: &PrivateOperator,
    evidence: &StopEvidence,
    audit: &UnitStopAudit,
    journal: &Journal,
    volume: &VolumeWitness,
    custody: ReportCustody<'_>,
    attempt_dir: &Path,
) -> io::Result<Vec<u8>> {
    preflight_custodian(operator, custody.seed, custody.semantics)?;
    let identity = evidence.target.stop_identity();
    evidence.target.recheck_volume(volume)?;
    let checked = journal
        .audit_stopped_manager_checked(&identity, || evidence.target.recheck_volume(volume))?;
    let stop_audit = audit.source_stop_audit(&identity)?;
    if checked.source_stop_audit(&identity)? != stop_audit {
        return Err(invalid("STOP manager audit changed before report signing"));
    }
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("STOP report parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let observation = json!({
        "begin":hex(&evidence.begin), "committedClaim":hex(&evidence.committed),
        "nonce":nonce()?, "unit":hex(identity.unit.as_bytes()),
        "materializedImage":identity.image_identity,
        "outcome":"stopped", "invocationId":hex(identity.invocation_id.as_bytes()),
        "controlGroup":hex(identity.control_group.as_bytes()), "pid":"0",
        "stopAudit":stop_audit, "volumeWitness":hex(&volume.bytes),
    });
    let source = write_new(
        attempt_dir,
        "report-source.json",
        &serde_json::to_vec(&observation)?,
    )?;
    let report = operator.tool(
        "author",
        "application-lifecycle-launch-physical-report",
        &source,
        &attempt_dir.join("report.bin"),
    )?;
    if report.is_empty() || report.len() > REPORT_BOUND {
        return Err(invalid("STOP report bound refused"));
    }
    let report_path = attempt_dir.join("report.bin");
    let inspection: Value = serde_json::from_slice(&operator.tool(
        "inspect",
        "application-lifecycle-launch-physical-report",
        &report_path,
        &attempt_dir.join("report-inspection.json"),
    )?)?;
    checked_report_view(&inspection, &report, evidence, &observation, volume)?;
    let signing_source = write_new(
        attempt_dir,
        "signing-frame-source.json",
        &serde_json::to_vec(&json!({"begin":hex(&evidence.begin),"report":hex(&report)}))?,
    )?;
    let frame = operator.tool(
        "author",
        "application-lifecycle-launch-physical-signing-frame",
        &signing_source,
        &attempt_dir.join("signing-frame.bin"),
    )?;
    if frame.is_empty() || frame.len() > REPORT_BOUND {
        return Err(invalid("STOP signing frame bound refused"));
    }
    let after = journal
        .audit_stopped_manager_checked(&identity, || evidence.target.recheck_volume(volume))?;
    if after.source_stop_audit(&identity)? != stop_audit {
        return Err(invalid("STOP audit changed before custodian signature"));
    }
    let signature = private_signing_key(custody.seed)?.sign(&frame).to_bytes();
    let signed_source = write_new(
        attempt_dir,
        "signed-report-source.json",
        &serde_json::to_vec(&json!({"begin":hex(&evidence.begin),
            "report":hex(&report),"signature":hex(&signature)}))?,
    )?;
    let signed = operator.tool(
        "author",
        "application-lifecycle-launch-physical-signed-report",
        &signed_source,
        &attempt_dir.join("signed-report.bin"),
    )?;
    let signed_view: Value = serde_json::from_slice(&operator.tool(
        "inspect",
        "application-lifecycle-launch-physical-signed-report",
        &attempt_dir.join("signed-report.bin"),
        &attempt_dir.join("signed-report-inspection.json"),
    )?)?;
    if text(&signed_view, "type")? != "application-lifecycle-launch-physical-signed-report-v2"
        || text(&signed_view, "frameHex")? != hex(&signed)
        || text(&signed_view, "signatureHex")? != hex(&signature)
    {
        return Err(invalid("STOP signed report source echo differs"));
    }
    checked_report_view(
        signed_view
            .get("report")
            .ok_or_else(|| invalid("STOP signed report nested report absent"))?,
        &report,
        evidence,
        &observation,
        volume,
    )?;
    Ok(signed)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct StopCompletionSigners {
    protocol: String,
    selector: crate::lifecycle_selector::LifecycleSelector,
    management_subject: String,
    signers: Vec<SignerPin>,
}

impl StopCompletionSigners {
    fn validate(&self, operator: &PrivateOperator, app_uid: u32) -> io::Result<()> {
        if self.protocol != "mini-spk-completion-management-v1" {
            return Err(invalid("STOP completion management custody refused"));
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

fn signed_report_retained(
    operator: &PrivateOperator,
    evidence: &StopEvidence,
    audit: &UnitStopAudit,
    volume: &VolumeWitness,
    seed: &Path,
    attempt_dir: &Path,
    probe_dir: &Path,
) -> io::Result<Vec<u8>> {
    private_dir(attempt_dir)?;
    private_dir(
        probe_dir
            .parent()
            .ok_or_else(|| invalid("STOP report probe parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(probe_dir)?;
    let source: Value = serde_json::from_slice(&read_private(
        &attempt_dir.join("report-source.json"),
        MAX_AUTHOR_JSON,
    )?)?;
    if text(&source, "begin")? != hex(&evidence.begin)
        || text(&source, "committedClaim")? != hex(&evidence.committed)
        || text(&source, "outcome")? != "stopped"
        || text(&source, "unit")? != hex(evidence.target.stop_identity().unit.as_bytes())
        || text(&source, "materializedImage")? != evidence.target.stop_identity().image_identity
        || text(&source, "invocationId")?
            != hex(evidence.target.stop_identity().invocation_id.as_bytes())
        || text(&source, "controlGroup")?
            != hex(evidence.target.stop_identity().control_group.as_bytes())
        || text(&source, "pid")? != "0"
        || source.get("stopAudit")
            != Some(&audit.source_stop_audit(&evidence.target.stop_identity())?)
        || text(&source, "volumeWitness")? != hex(&volume.bytes)
    {
        return Err(invalid("STOP retained report source differs"));
    }
    let source_path = write_new(
        probe_dir,
        "report-source.json",
        &serde_json::to_vec(&source)?,
    )?;
    let report = operator.tool(
        "author",
        "application-lifecycle-launch-physical-report",
        &source_path,
        &probe_dir.join("rederived-report.bin"),
    )?;
    ensure_artifact(attempt_dir, "report.bin", &report, MAX_FRAME)?;
    let report_path = write_new(probe_dir, "report.bin", &report)?;
    let report_inspection = operator.tool(
        "inspect",
        "application-lifecycle-launch-physical-report",
        &report_path,
        &probe_dir.join("report.json"),
    )?;
    let report_view: Value = serde_json::from_slice(&report_inspection)?;
    // The retained source is checked against the journal and volume again by
    // the caller; the source inspector binds the canonical original claim.
    checked_report_view(&report_view, &report, evidence, &source, volume)?;
    ensure_artifact(
        attempt_dir,
        "report-inspection.json",
        &report_inspection,
        96_822_080,
    )?;
    let frame_source_bytes = serde_json::to_vec(&json!({
        "begin":hex(&evidence.begin),"report":hex(&report)}))?;
    ensure_artifact(
        attempt_dir,
        "signing-frame-source.json",
        &frame_source_bytes,
        MAX_AUTHOR_JSON,
    )?;
    let frame_source = write_new(probe_dir, "signing-frame-source.json", &frame_source_bytes)?;
    let frame = operator.tool(
        "author",
        "application-lifecycle-launch-physical-signing-frame",
        &frame_source,
        &probe_dir.join("rederived-signing-frame.bin"),
    )?;
    ensure_artifact(attempt_dir, "signing-frame.bin", &frame, MAX_FRAME)?;
    let signature = private_signing_key(seed)?.sign(&frame).to_bytes();
    let signed_source_bytes = serde_json::to_vec(&json!({
        "begin":hex(&evidence.begin), "report":hex(&report),
        "signature":hex(&signature)}))?;
    ensure_artifact(
        attempt_dir,
        "signed-report-source.json",
        &signed_source_bytes,
        MAX_AUTHOR_JSON,
    )?;
    let signed_source = write_new(probe_dir, "signed-report-source.json", &signed_source_bytes)?;
    let signed = operator.tool(
        "author",
        "application-lifecycle-launch-physical-signed-report",
        &signed_source,
        &probe_dir.join("rederived-signed-report.bin"),
    )?;
    ensure_artifact(attempt_dir, "signed-report.bin", &signed, MAX_FRAME)?;
    let signed_path = write_new(probe_dir, "signed-report.bin", &signed)?;
    let signed_inspection = operator.tool(
        "inspect",
        "application-lifecycle-launch-physical-signed-report",
        &signed_path,
        &probe_dir.join("signed.json"),
    )?;
    let signed_view: Value = serde_json::from_slice(&signed_inspection)?;
    if text(&signed_view, "type")? != "application-lifecycle-launch-physical-signed-report-v2"
        || text(&signed_view, "frameHex")? != hex(&signed)
        || text(&signed_view, "signatureHex")? != hex(&signature)
        || signed_view.get("report") != Some(&report_view)
    {
        return Err(invalid("STOP retained signed report differs"));
    }
    ensure_artifact(
        attempt_dir,
        "signed-report-inspection.json",
        &signed_inspection,
        96_822_080,
    )?;
    Ok(signed)
}

fn report_needs_fresh(directory: &Path) -> io::Result<bool> {
    if absent(directory)? {
        return Ok(true);
    }
    private_dir(directory)?;
    if !absent(&directory.join("report-source.json"))? {
        return Ok(false);
    }
    if fs::read_dir(directory)?.next().is_some() {
        return Err(invalid(
            "STOP report directory has artifacts but no first source",
        ));
    }
    // An empty directory is the crash point immediately after mkdir; there
    // are no nonce or signed bytes to preserve yet.
    fs::remove_dir(directory)?;
    Ok(true)
}

fn assemble_completion(
    operator: &PrivateOperator,
    fixed: &StopCompletionSigners,
    app_uid: u32,
    evidence: &StopEvidence,
    launch: &SourceBoundLaunch<'_>,
    signed_report: &[u8],
    attempt_dir: &Path,
) -> io::Result<Vec<u8>> {
    fixed.validate(operator, app_uid)?;
    if signed_report.is_empty() || signed_report.len() > REPORT_BOUND {
        return Err(invalid("STOP signed report bound refused"));
    }
    private_dir(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("STOP completion parent absent"))?,
    )?;
    DirBuilder::new().mode(0o700).create(attempt_dir)?;
    let source = write_new(
        attempt_dir,
        "request.json",
        &serde_json::to_vec(&json!({
            "begin":hex(&evidence.begin), "claimIngress":hex(&evidence.claim_ingress),
            "signedReport":hex(signed_report),
        }))?,
    )?;
    let request = operator.tool(
        "author",
        "application-lifecycle-launch-completion-request",
        &source,
        &attempt_dir.join("request.bin"),
    )?;
    let request_view: Value = serde_json::from_slice(&operator.tool(
        "inspect",
        "application-lifecycle-launch-completion-request",
        &attempt_dir.join("request.bin"),
        &attempt_dir.join("request-inspection.json"),
    )?)?;
    for (name, expected) in [
        (
            "type",
            "application-lifecycle-launch-completion-request-v1".to_owned(),
        ),
        ("canonicalRequestHex", hex(&request)),
        ("originalBeginHex", hex(&evidence.begin)),
        ("originalClaimHex", hex(&evidence.claim_ingress)),
        ("signedReportHex", hex(signed_report)),
        ("app", fixed.selector.app.clone()),
        ("descriptorRoot", launch.descriptor().root.clone()),
        ("volumeIdHex", evidence.target.volume_id_hex().to_owned()),
    ] {
        if text(&request_view, name)? != expected {
            return Err(invalid("STOP completion request differs from source"));
        }
    }
    let active = serde_json::to_vec(&json!({
        "protocol":"mini-spk-stop-completion-prepare-requested-v1",
        "requestSha256":hex(&Sha256::digest(&request)),
        "originalBeginSha256":hex(&Sha256::digest(&evidence.begin)),
        "originalClaimSha256":hex(&Sha256::digest(&evidence.claim_ingress)),
        "signedReportSha256":hex(&Sha256::digest(signed_report)),
    }))?;
    write_new(attempt_dir, "op70-requested.json", &active)?;
    write_new(
        attempt_dir
            .parent()
            .ok_or_else(|| invalid("STOP completion parent absent"))?,
        "lifecycle-stop-completion-v2-active.json",
        &active,
    )?;
    let reply = operator.invoke(70, &fixed.selector.framed(&request)?)?;
    write_new(attempt_dir, "op70-frame.bin", &reply)?;
    let plan = framed_payload(&reply, 70, PLAN_TAG)?;
    let plan_path = write_new(attempt_dir, "plan.bin", plan)?;
    let view: Value = serde_json::from_slice(&operator.tool(
        "inspect",
        "application-lifecycle-launch-completion-plan",
        &plan_path,
        &attempt_dir.join("plan.json"),
    )?)?;
    for (name, expected) in [
        (
            "type",
            "application-lifecycle-launch-completion-plan-v1".to_owned(),
        ),
        ("canonicalPlanHex", hex(plan)),
        ("canonicalRequestHex", hex(&request)),
        ("originalBeginHex", hex(&evidence.begin)),
        ("originalClaimHex", hex(&evidence.claim_ingress)),
        ("signedReportHex", hex(signed_report)),
        ("app", fixed.selector.app.clone()),
        ("descriptorRoot", launch.descriptor().root.clone()),
        ("volumeIdHex", evidence.target.volume_id_hex().to_owned()),
    ] {
        if text(&view, name)? != expected {
            return Err(invalid("STOP completion plan differs from source"));
        }
    }
    for name in [
        "currentAppRoot",
        "currentPackageRoot",
        "worldRoot",
        "height",
    ] {
        if !decimal(text(&view, name)?) {
            return Err(invalid("STOP completion plan root malformed"));
        }
    }
    let slots = view
        .get("slots")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid("STOP completion signing slots absent"))?;
    if slots.len() > fixed.signers.len() {
        return Err(invalid("STOP completion slot count differs"));
    }
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
    Ok(ingress)
}

fn completion_ingress_retained(
    dir: &Path,
    evidence: &StopEvidence,
    signed_report: &[u8],
) -> io::Result<Vec<u8>> {
    private_dir(dir)?;
    let active = read_private(&dir.join("op70-requested.json"), MAX_CONFIG)?;
    if read_private(
        &dir.parent()
            .ok_or_else(|| invalid("STOP completion parent absent"))?
            .join("lifecycle-stop-completion-v2-active.json"),
        MAX_CONFIG,
    )? != active
    {
        return Err(invalid("STOP completion active marker differs"));
    }
    let marker: Value = serde_json::from_slice(&active)?;
    let request = read_private(&dir.join("request.bin"), MAX_FRAME)?;
    if text(&marker, "protocol")? != "mini-spk-stop-completion-prepare-requested-v1"
        || text(&marker, "requestSha256")? != hex(&Sha256::digest(&request))
        || text(&marker, "originalBeginSha256")? != hex(&Sha256::digest(&evidence.begin))
        || text(&marker, "originalClaimSha256")? != hex(&Sha256::digest(&evidence.claim_ingress))
        || text(&marker, "signedReportSha256")? != hex(&Sha256::digest(signed_report))
    {
        return Err(invalid("STOP retained completion marker differs"));
    }
    let request_view: Value = serde_json::from_slice(&read_private(
        &dir.join("request-inspection.json"),
        MAX_INSPECTION,
    )?)?;
    if text(&request_view, "canonicalRequestHex")? != hex(&request)
        || text(&request_view, "originalBeginHex")? != hex(&evidence.begin)
        || text(&request_view, "originalClaimHex")? != hex(&evidence.claim_ingress)
        || text(&request_view, "signedReportHex")? != hex(signed_report)
    {
        return Err(invalid("STOP retained completion request differs"));
    }
    let ingress = read_private(&dir.join("completion-v2.bin"), MAX_FRAME)?;
    let frame = read_private(&dir.join("op71-frame.bin"), MAX_FRAME)?;
    if framed_payload(&frame, 71, INGRESS_TAG)? != ingress {
        return Err(invalid("STOP retained completion assembly differs"));
    }
    Ok(ingress)
}

/// Pure op70/71 work can be replanned after a crash because no op38 marker
/// exists. Preserve each partial source attempt and descend into a bounded
/// private child; never replace its plan or signing headers in place.
fn completion_dir(base: &Path) -> io::Result<(PathBuf, bool)> {
    let mut current = base.to_path_buf();
    for _ in 0..8 {
        if absent(&current)? {
            return Ok((current, false));
        }
        private_dir(&current)?;
        if !absent(&current.join("op38-requested.json"))? {
            return Ok((current, true));
        }
        let next = current.join("replan");
        if !absent(&next)? {
            current = next;
            continue;
        }
        if fs::read_dir(&current)?.next().is_none() {
            fs::remove_dir(&current)?;
            return Ok((current, false));
        }
        // Even a complete detached assembly may have become stale if an
        // unrelated Mini event advanced the image before the op38 send. With
        // no durable send marker, preserve it and prepare at the new tip.
        return Ok((next, false));
    }
    Err(invalid(
        "STOP pre-submit completion replans exceed bounded depth",
    ))
}

fn outcome_receipt(view: &Value, kind: &str, prior: &ExactReceipt) -> io::Result<ExactReceipt> {
    if text(view, "type")? != "confirmed" || text(view, "confirmation")? != kind {
        return Err(invalid("STOP completion outcome confirmation refused"));
    }
    let result = receipt(view)?;
    if !crate::lifecycle_v3_claim_native::later_decimal(
        result.accepted_count(),
        prior.accepted_count(),
    ) {
        return Err(invalid("STOP completion count does not follow claim"));
    }
    Ok(result)
}

fn same_receipt(left: &ExactReceipt, right: &ExactReceipt) -> bool {
    left.transaction_id() == right.transaction_id()
        && left.event_id() == right.event_id()
        && left.accepted_count() == right.accepted_count()
        && left.world_root() == right.world_root()
}

fn receipt_json(value: &ExactReceipt) -> Value {
    json!({"transactionId":value.transaction_id(), "eventId":value.event_id(),
        "acceptedCount":value.accepted_count(), "worldRoot":value.world_root()})
}

/// The first definite op38 or recovered op39 receipt becomes the durable
/// anchor. A frame-only crash is parsed before any lookup and later lookups
/// must match all four fields.
fn retained_completion_anchor(
    operator: &PrivateOperator,
    dir: &Path,
    prior: &ExactReceipt,
) -> io::Result<Option<ExactReceipt>> {
    let anchor = dir.join("receipt-anchor.json");
    if !absent(&anchor)? {
        let view: Value = serde_json::from_slice(&read_private(&anchor, MAX_CONFIG)?)?;
        return Ok(Some(receipt(&view)?));
    }
    let frame = dir.join("op38-frame.bin");
    if absent(&frame)? {
        return Ok(None);
    }
    let bytes = read_private(&frame, MAX_FRAME)?;
    // The response may have been truncated after the durable pre-submit
    // marker. It is not evidence; exact op39 on the original ingress recovers
    // the receipt. A complete but wrong-family frame remains a hard refusal.
    if bytes.len() < 4 {
        return Ok(None);
    }
    let advertised = u32::from_le_bytes(bytes[..4].try_into().unwrap()) as usize;
    if advertised
        .checked_add(4)
        .is_some_and(|full| full > bytes.len())
    {
        return Ok(None);
    }
    let payload = framed_payload(&bytes, 38, OUTCOME_TAG)?;
    let probe = fresh_probe(dir, "frame-recovery")?;
    DirBuilder::new().mode(0o700).create(&probe)?;
    let input = write_new(&probe, "outcome.bin", payload)?;
    let inspected = operator.tool("inspect", "outcome", &input, &probe.join("outcome.json"))?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let recovered = outcome_receipt(&view, "installed", prior)?;
    write_new(
        dir,
        "receipt-anchor.json",
        &serde_json::to_vec(&receipt_json(&recovered))?,
    )?;
    Ok(Some(recovered))
}

fn complete_once_or_lookup(
    operator: &PrivateOperator,
    dir: &Path,
    evidence: &StopEvidence,
    ingress: &[u8],
    journal: &Journal,
    volume: &VolumeWitness,
) -> io::Result<()> {
    private_dir(dir)?;
    let marker_path = dir.join("op38-requested.json");
    if absent(&marker_path)? {
        // An op38 may be sent only once, after the stopped journal and volume
        // have been re-audited. The marker is durable before that send.
        journal.audit_stopped_manager_checked(&evidence.target.stop_identity(), || {
            evidence.target.recheck_volume(volume)
        })?;
        let marker = json!({"protocol":"mini-spk-stop-completion-submit-requested-v1",
            "ingressSha256":hex(&Sha256::digest(ingress)),
            "claimSha256":hex(&Sha256::digest(&evidence.committed))});
        write_new(dir, "op38-requested.json", &serde_json::to_vec(&marker)?)?;
        let frame = operator.invoke(38, ingress)?;
        write_new(dir, "op38-frame.bin", &frame)?;
        let payload = framed_payload(&frame, 38, OUTCOME_TAG)?;
        let input = write_new(dir, "op38-outcome.bin", payload)?;
        let inspected =
            operator.tool("inspect", "outcome", &input, &dir.join("op38-outcome.json"))?;
        let view: Value = serde_json::from_slice(&inspected)?;
        let receipt = outcome_receipt(&view, "installed", &evidence.claim_receipt)?;
        write_new(
            dir,
            "receipt-anchor.json",
            &serde_json::to_vec(&receipt_json(&receipt))?,
        )?;
        return Ok(());
    }
    let marker: Value = serde_json::from_slice(&read_private(&marker_path, MAX_CONFIG)?)?;
    if text(&marker, "protocol")? != "mini-spk-stop-completion-submit-requested-v1"
        || text(&marker, "ingressSha256")? != hex(&Sha256::digest(ingress))
        || text(&marker, "claimSha256")? != hex(&Sha256::digest(&evidence.committed))
    {
        return Err(invalid("STOP original op38 marker differs"));
    }
    let anchor = retained_completion_anchor(operator, dir, &evidence.claim_receipt)?;
    let probe = fresh_probe(dir, "op39-lookup")?;
    DirBuilder::new().mode(0o700).create(&probe)?;
    let frame = operator.invoke(39, ingress)?;
    let payload = framed_payload(&frame, 39, OUTCOME_TAG)?;
    let input = write_new(&probe, "outcome.bin", payload)?;
    let inspected = operator.tool("inspect", "outcome", &input, &probe.join("outcome.json"))?;
    let view: Value = serde_json::from_slice(&inspected)?;
    let historical = outcome_receipt(&view, "replayed", &evidence.claim_receipt)?;
    if let Some(anchor) = anchor {
        if !same_receipt(&anchor, &historical) {
            return Err(invalid("STOP historical completion receipt drift"));
        }
    } else {
        write_new(
            dir,
            "receipt-anchor.json",
            &serde_json::to_vec(&receipt_json(&historical))?,
        )?;
    }
    Ok(())
}

/// Callable operator entry for one resident STOP. The supervisor intentionally
/// has no API for choosing the old running unit, source event, or volume.
/// Those come from the current verifier-selected STOP plan and exact journal.
/// A STOP BEGIN attempt that only authored its op66 plan changed nothing in
/// Mini: no signatures were assembled (op67) and nothing was submitted (op22).
/// Set it and its matching active marker aside so a new STOP may begin. Any
/// later marker, a differing active marker or other attempt keeps the audit.
fn set_aside_pure_begin(config: &StopConfig, journal_dir: &Path) -> io::Result<()> {
    let attempt = &config.begin_attempt_dir;
    let active = journal_dir.join("lifecycle-stop-begin-v3-active.json");
    if absent(attempt)? {
        return Ok(());
    }
    private_dir(attempt)?;
    for later in ["op67-requested.bin", "op22-requested.json", "begin-v3.bin"] {
        if !absent(&attempt.join(later))? {
            return Ok(());
        }
    }
    for other in [
        &config.claim_author_attempt_dir,
        &config.claim_attempt_dir,
        &config.report_attempt_dir,
        &config.completion_attempt_dir,
        &journal_dir.join("lifecycle-stop-claim-v3-active.json"),
    ] {
        if !absent(other)? {
            return Ok(());
        }
    }
    let requested = attempt.join("op66-requested.json");
    if absent(&requested)? {
        return Ok(());
    }
    let marker = read_private(&requested, MAX_CONFIG)?;
    if !absent(&active)? && read_private(&active, MAX_CONFIG)? != marker {
        return Ok(());
    }
    let mut random = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut random)?;
    let aside = journal_dir.join(format!("stop-begin-plan-only-{}", hex(&random)));
    fs::rename(attempt, &aside)?;
    File::open(journal_dir)?.sync_all()?;
    if !absent(&active)? {
        fs::rename(&active, aside.join("active-marker.json"))?;
        File::open(&aside)?.sync_all()?;
        File::open(journal_dir)?.sync_all()?;
    }
    Ok(())
}

pub fn run(config_path: &Path) -> io::Result<()> {
    let (config, pins) = load_config(config_path)?;
    private_dir(&pins.journal_dir)?;
    let _run_lock = acquire_run_lock(&pins.journal_dir)?;
    let operator = PrivateOperator {
        host: pins.mini_host.clone(),
        config: pins.mini_config.clone(),
        socket: pins.mini_operator_socket.clone(),
        host_sha256: pins.mini_host_sha256.clone(),
        config_sha256: pins.mini_config_sha256.clone(),
    };
    let _ = operator.pinned_config()?;
    let package = verify_installed_spk(&pins.image_dir, pins.app_uid)?;
    if package.raw_sha256 != pins.expected_raw_sha256 {
        return Err(invalid(
            "STOP verified signed package differs from resident pin",
        ));
    }
    let launch = SourceBoundLaunch::load_retained(
        &operator,
        &package,
        &pins.descriptor_attempt_dir,
        &fresh_probe(&pins.journal_dir, "stop-descriptor-inspect")?,
    )?;
    match_qualification(&pins, &launch)?;
    let volume = read_attested_volume(
        &VolumeSite::new(&pins.grains_root, &pins.store)?,
        pins.volume_resource,
        pins.app_uid,
        pins.persistent_var_max_bytes,
        &pins.deployment_id,
        &pins.host_id,
        &pins.expected_volume_id,
    )?;
    if volume.mount != pins.persistent_var || volume.resource != pins.volume_resource {
        return Err(invalid("STOP attested mount differs from resident pin"));
    }
    volume.recheck_handoff()?;
    preflight_custodian(
        &operator,
        &pins.completion_custodian_seed,
        &pins.completion_semantics,
    )?;
    let journal = Journal::open(&pins.journal_dir)?
        .with_broker_endpoint(&pins.grains_root, pins.broker_socket.as_deref())?;
    let phase = journal
        .read()?
        .ok_or_else(|| invalid("STOP prior running journal absent"))?
        .phase;
    let audit = match phase {
        Phase::Running => {
            set_aside_pure_begin(&config, &pins.journal_dir)?;
            // Any prior source or physical marker makes this run an uncertain
            // attempt. It cannot be converted into a second fresh op26.
            for path in [
                &config.begin_attempt_dir,
                &config.claim_author_attempt_dir,
                &config.claim_attempt_dir,
                &config.report_attempt_dir,
                &config.completion_attempt_dir,
                &pins.journal_dir.join("lifecycle-stop-begin-v3-active.json"),
                &pins.journal_dir.join("lifecycle-stop-claim-v3-active.json"),
            ] {
                if !absent(path)? {
                    return Err(invalid(
                        "STOP prior attempt on Running journal requires audit",
                    ));
                }
            }
            let begin_signers: FixedStopBeginSigners =
                serde_json::from_slice(&read_private(&pins.begin_management_custody, MAX_CONFIG)?)?;
            let claim_signers: FixedStopClaimSigners =
                serde_json::from_slice(&read_private(&pins.claim_management_custody, MAX_CONFIG)?)?;
            let begin = lifecycle_v3_stop_begin_native::submit_once(
                &operator,
                &begin_signers,
                pins.app_uid,
                &launch,
                &pins.begin_operation_ledger,
                &config.begin_attempt_dir,
            )?;
            if begin.volume_id_hex() != volume.volume_id {
                return Err(invalid("STOP BEGIN volume differs from root attestation"));
            }
            let assembled = lifecycle_v3_stop_assembly_native::assemble_once(
                &operator,
                &claim_signers,
                pins.app_uid,
                begin,
                &launch,
                &pins.claim_nonce_ledger,
                &config.claim_author_attempt_dir,
            )?;
            let fresh = lifecycle_v3_stop_assembly_native::submit_fresh_once(
                &operator,
                &config.claim_attempt_dir,
                assembled,
            )?;
            lifecycle_v3_stop_native::fence_exact(
                &fresh,
                &journal,
                &volume,
                &config.claim_attempt_dir,
            )?
        }
        Phase::Fenced => lifecycle_v3_stop_native::resume_fenced_exact(
            &operator,
            &config.claim_attempt_dir,
            &fresh_probe(&pins.journal_dir, "stop-fenced-reinspect")?,
            &journal,
            &volume,
        )?,
        Phase::Stopped => {
            let evidence = inspect_original(
                &operator,
                &config.claim_attempt_dir,
                &fresh_probe(&pins.journal_dir, "stop-stopped-reinspect")?,
            )?;
            journal.audit_stopped_manager_checked(&evidence.target.stop_identity(), || {
                evidence.target.recheck_volume(&volume)
            })?
        }
        _ => {
            return Err(invalid(
                "STOP journal is not a completed running incarnation",
            ))
        }
    };
    let evidence = inspect_original(
        &operator,
        &config.claim_attempt_dir,
        &fresh_probe(&pins.journal_dir, "stop-report-reinspect")?,
    )?;
    if evidence.target.volume_id_hex() != volume.volume_id
        || evidence.target.operation_generation() == 0
    {
        return Err(invalid("STOP inspected operation or volume differs"));
    }
    let checked = journal
        .audit_stopped_manager_checked(&evidence.target.stop_identity(), || {
            evidence.target.recheck_volume(&volume)
        })?;
    if checked.source_stop_audit(&evidence.target.stop_identity())?
        != audit.source_stop_audit(&evidence.target.stop_identity())?
    {
        return Err(invalid("STOP post-fence audit changed"));
    }
    let signed_report = if report_needs_fresh(&config.report_attempt_dir)? {
        prepare_report(
            &operator,
            &evidence,
            &checked,
            &journal,
            &volume,
            ReportCustody {
                seed: &pins.completion_custodian_seed,
                semantics: &pins.completion_semantics,
            },
            &config.report_attempt_dir,
        )?
    } else {
        signed_report_retained(
            &operator,
            &evidence,
            &checked,
            &volume,
            &pins.completion_custodian_seed,
            &config.report_attempt_dir,
            &fresh_probe(&pins.journal_dir, "stop-report-retained")?,
        )?
    };
    let completion_signers: StopCompletionSigners = serde_json::from_slice(&read_private(
        &pins.completion_management_custody,
        MAX_CONFIG,
    )?)?;
    let (completion_dir, retained) = completion_dir(&config.completion_attempt_dir)?;
    let ingress = if retained {
        completion_signers.validate(&operator, pins.app_uid)?;
        completion_ingress_retained(&completion_dir, &evidence, &signed_report)?
    } else {
        assemble_completion(
            &operator,
            &completion_signers,
            pins.app_uid,
            &evidence,
            &launch,
            &signed_report,
            &completion_dir,
        )?
    };
    complete_once_or_lookup(
        &operator,
        &completion_dir,
        &evidence,
        &ingress,
        &journal,
        &volume,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch() -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "mini-stop-service-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    #[test]
    fn concurrent_stop_supervisor_refuses_second_owner_until_first_exits() {
        let dir = scratch();
        let first = acquire_run_lock(&dir).unwrap();
        let contender_dir = dir.clone();
        let refused = thread::spawn(move || acquire_run_lock(&contender_dir))
            .join()
            .unwrap()
            .unwrap_err();
        assert_eq!(refused.kind(), io::ErrorKind::AlreadyExists);
        // The same lock also excludes a new invocation after its first
        // operator command has started; no partial directory is consulted.
        write_new(&dir, "completion-partial", b"unsent").unwrap();
        assert_eq!(
            acquire_run_lock(&dir).unwrap_err().kind(),
            io::ErrorKind::AlreadyExists
        );
        drop(first);
        let recovered_dir = dir.clone();
        let recovered = thread::spawn(move || acquire_run_lock(&recovered_dir))
            .join()
            .unwrap()
            .unwrap();
        drop(recovered);
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn truncated_first_completion_frame_never_becomes_receipt_anchor() {
        let dir = scratch();
        let mut truncated = 100u32.to_le_bytes().to_vec();
        truncated.extend_from_slice(b"partial");
        write_new(&dir, "op38-frame.bin", &truncated).unwrap();
        let operator = PrivateOperator {
            host: PathBuf::new(),
            config: PathBuf::new(),
            socket: PathBuf::new(),
            host_sha256: String::new(),
            config_sha256: String::new(),
        };
        let prior = ExactReceipt::new("1", "2", "3", "4").unwrap();
        assert!(retained_completion_anchor(&operator, &dir, &prior)
            .unwrap()
            .is_none());
        assert!(absent(&dir.join("receipt-anchor.json")).unwrap());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn recovered_receipt_anchor_compares_all_four_large_fields() {
        let huge = "340282366920938463463374607431768211456";
        let first = ExactReceipt::new(huge, "2", "3", "4").unwrap();
        assert!(!same_receipt(
            &first,
            &ExactReceipt::new("1", "2", "3", "4").unwrap()
        ));
        assert!(!same_receipt(
            &first,
            &ExactReceipt::new(huge, "5", "3", "4").unwrap()
        ));
        assert!(!same_receipt(
            &first,
            &ExactReceipt::new(huge, "2", "6", "4").unwrap()
        ));
        assert!(!same_receipt(
            &first,
            &ExactReceipt::new(huge, "2", "3", "7").unwrap()
        ));
    }

    #[test]
    fn report_mkdir_and_partial_source_reopen_without_changing_first_bytes() {
        let root = scratch();
        let report = root.join("report");
        DirBuilder::new().mode(0o700).create(&report).unwrap();
        assert!(report_needs_fresh(&report).unwrap());
        assert!(absent(&report).unwrap());
        DirBuilder::new().mode(0o700).create(&report).unwrap();
        write_new(&report, "report-source.json", b"original source").unwrap();
        assert!(!report_needs_fresh(&report).unwrap());
        assert_eq!(
            read_private(&report.join("report-source.json"), MAX_CONFIG).unwrap(),
            b"original source"
        );
        ensure_artifact(&report, "report.bin", b"derived report", MAX_FRAME).unwrap();
        assert!(ensure_artifact(&report, "report.bin", b"changed report", MAX_FRAME).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn completion_pre_submit_replans_but_op38_marker_never_does() {
        let root = scratch();
        let base = root.join("completion");
        DirBuilder::new().mode(0o700).create(&base).unwrap();
        assert_eq!(completion_dir(&base).unwrap(), (base.clone(), false));
        DirBuilder::new().mode(0o700).create(&base).unwrap();
        write_new(&base, "op70-requested.json", b"original marker").unwrap();
        let replan = base.join("replan");
        assert_eq!(completion_dir(&base).unwrap(), (replan.clone(), false));
        assert_eq!(
            read_private(&base.join("op70-requested.json"), MAX_CONFIG).unwrap(),
            b"original marker"
        );
        write_new(&base, "completion-v2.bin", b"unsubmitted assembly").unwrap();
        assert_eq!(completion_dir(&base).unwrap(), (replan.clone(), false));
        DirBuilder::new().mode(0o700).create(&replan).unwrap();
        write_new(&replan, "op38-requested.json", b"sent once").unwrap();
        assert_eq!(completion_dir(&base).unwrap(), (replan.clone(), true));
        fs::remove_dir_all(root).unwrap();
    }
}
