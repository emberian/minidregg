//! Launch-bound INSTALL in two physical phases. Historical v1 attempts stay
//! in their own namespace and never supply a v2 launch root.

use super::{invalid, InstallConfig, MAX_CONFIG, MAX_SPK};
use crate::completion_native::preflight_custodian;
use crate::dispatch_native::{write_new, PrivateOperator};
use crate::hostd::VerifiedBegin;
use crate::launch_descriptor_native::SourceLaunchDescriptor;
use crate::lifecycle_v3_claim_native::{
    assemble_once as assemble_claim_once, submit_fresh_once as submit_claim_once,
    CommittedLaunchClaim, FixedLaunchClaimSigners,
};
use crate::lifecycle_v3_completion_native::{
    assemble_once as assemble_completion_once, load_retained as load_completion_retained,
    recover_receipt_only, submit_fresh_once as submit_completion_once, CompletionInput,
    FixedLaunchCompletionSigners,
};
use crate::lifecycle_v3_native::{
    submit_once as submit_begin_once, AcceptedLaunchBegin, FixedLaunchBeginSigners,
    LaunchBeginAction,
};
use crate::lifecycle_v3_report_native::{
    prepare_once as prepare_report_once, PhysicalMode, ReportInput,
};
use crate::materialize::{qualify_bridge_spk, verify_installed_spk, InstalledPackage};
use crate::resident_launch::SourceBoundLaunch;
use crate::sandbox::open_protected_directory;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, OpenOptions};
use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::Path;

const MAX_QUALIFICATION: u64 = 16 * 1024;

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

impl QualifiedLaunch {
    fn read(config: &InstallConfig) -> io::Result<Self> {
        let path = config
            .launch_qualification
            .as_ref()
            .ok_or_else(|| invalid("v2 launch qualification absent"))?;
        let qualification: Self =
            serde_json::from_slice(&super::private_file(path, MAX_QUALIFICATION)?)?;
        if qualification.protocol != "mini-spk-launch-qualified-v2"
            || qualification.raw_sha256 != config.expected_raw_sha256
            || !super::hex64(&qualification.launch_canonical_sha256)
            || qualification.create_digests.is_empty()
            || qualification.create_digests.len() > 64
            || qualification.create_count != qualification.create_digests.len().to_string()
        {
            return Err(invalid("v2 launch qualification differs from INSTALL pins"));
        }
        Ok(qualification)
    }

    fn matches(&self, launch: &SourceLaunchDescriptor, raw_sha256: &str) -> io::Result<()> {
        if self.raw_sha256 != raw_sha256
            || self.package_root != launch.package.root
            || self.launch_root != launch.root
            || self.launch_canonical_sha256 != super::hex(&Sha256::digest(&launch.canonical))
            || self.create_digests != launch.create_digests
            || self.continue_digest != launch.continue_digest
            || self.create_count != launch.create_digests.len().to_string()
        {
            return Err(invalid(
                "verified SPK differs from retained v2 launch qualification",
            ));
        }
        Ok(())
    }
}

/// The only v3 INSTALL descriptor entrance. One signature-verified SPK parse
/// supplies v1 identity and all ordered commands; Mini authors both canonical
/// descriptors, and the protected qualifier must match the complete result.
/// A future v3 BEGIN may use `launch.canonical` only after this returns.
fn author_qualified_launch<'a>(
    config: &InstallConfig,
    operator: &PrivateOperator,
    package: &'a InstalledPackage,
    qualification: &QualifiedLaunch,
    attempt_dir: &Path,
) -> io::Result<SourceBoundLaunch<'a>> {
    let launch = SourceBoundLaunch::author(operator, package, attempt_dir)?;
    qualification.matches(launch.descriptor(), &package.raw_sha256)?;
    // Reopen the private qualifier after source authoring so an in-place
    // replacement cannot silently change the retained authority comparison.
    QualifiedLaunch::read(config)?.matches(launch.descriptor(), &package.raw_sha256)?;
    Ok(launch)
}

const V3_ARTIFACTS: &[&str] = &[
    "launch-descriptor",
    "lifecycle-begin-v3-active.json",
    "begin-v3",
    "claim-v3-author",
    "claim-v3",
    "lifecycle-claim-v3-active.json",
    "install-prepared-v2.json",
    "materialized-verify-v2",
    "materialized-report-v2",
    "completion-v2-author",
    "lifecycle-completion-v2-active.json",
    "install-completed-v2.json",
];

fn retained_marker_bytes(path: &Path) -> io::Result<Vec<u8>> {
    crate::dispatch_native::private_dir(
        path.parent()
            .ok_or_else(|| invalid("v3 INSTALL marker parent absent"))?,
    )?;
    let metadata = fs::symlink_metadata(path)?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.nlink() != 1
        || metadata.uid() != unsafe { libc::geteuid() }
        || metadata.permissions().mode() & 0o777 != 0o600
        || metadata.len() == 0
        || metadata.len() > MAX_QUALIFICATION
    {
        return Err(invalid("v3 INSTALL marker identity refused"));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let opened = file.metadata()?;
    if opened.dev() != metadata.dev() || opened.ino() != metadata.ino() {
        return Err(invalid("v3 INSTALL marker changed"));
    }
    let mut bytes = Vec::with_capacity(metadata.len() as usize);
    file.by_ref()
        .take(MAX_QUALIFICATION + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != metadata.len() {
        return Err(invalid("v3 INSTALL marker length changed"));
    }
    Ok(bytes)
}

fn checked_retirement(config: &InstallConfig, active: &str, attempt: &str) -> io::Result<bool> {
    let active_path = config.artifact(active);
    let metadata = match fs::symlink_metadata(&active_path) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(error) => return Err(error),
    };
    if !metadata.is_file() || metadata.file_type().is_symlink() || metadata.nlink() != 1 {
        return Err(invalid("v3 INSTALL success marker identity refused"));
    }
    if retained_marker_bytes(&active_path)? != retained_marker_bytes(&config.artifact(attempt))? {
        return Err(invalid(
            "v3 INSTALL active marker differs from retained attempt",
        ));
    }
    Ok(true)
}

fn retire_success_markers(config: &InstallConfig) -> io::Result<()> {
    let markers = [
        (
            "lifecycle-completion-v2-active.json",
            "completion-v2-author/op70-requested.json",
        ),
        (
            "lifecycle-claim-v3-active.json",
            "claim-v3-author/op68-requested.json",
        ),
        (
            "lifecycle-begin-v3-active.json",
            "begin-v3/op66-requested.json",
        ),
    ];
    let selected = markers
        .iter()
        .map(|(active, attempt)| checked_retirement(config, active, attempt))
        .collect::<io::Result<Vec<_>>>()?;
    for ((active, _), present) in markers.iter().zip(selected) {
        if present {
            fs::remove_file(config.artifact(active))?;
        }
    }
    fs::File::open(&config.journal_dir)?.sync_all()?;
    Ok(())
}

fn archive_pure_attempt(
    config: &InstallConfig,
    name: &str,
) -> io::Result<Option<std::path::PathBuf>> {
    let path = config.artifact(name);
    match fs::symlink_metadata(&path) {
        Ok(meta) if meta.is_dir() && !meta.file_type().is_symlink() => {}
        Ok(_) => return Err(invalid("v3 INSTALL pure attempt identity refused")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error),
    }
    crate::dispatch_native::private_dir(&path)?;
    let mut bytes = [0u8; 16];
    fs::File::open("/dev/urandom")?.read_exact(&mut bytes)?;
    let archive = config.artifact(&format!("{name}-aborted-pre-op38-{}", super::hex(&bytes)));
    fs::rename(&path, &archive)?;
    fs::File::open(&config.journal_dir)?.sync_all()?;
    Ok(Some(archive))
}

fn archive_incomplete_completion_attempt(config: &InstallConfig) -> io::Result<()> {
    let active_path = config.artifact("lifecycle-completion-v2-active.json");
    let embedded_path = config.artifact("completion-v2-author/active-marker.json");
    let active = match fs::symlink_metadata(&active_path) {
        Ok(_) => Some(retained_marker_bytes(&active_path)?),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(error),
    };
    let embedded = match fs::symlink_metadata(&embedded_path) {
        Ok(_) => Some(retained_marker_bytes(&embedded_path)?),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(error),
    };
    if active.is_some() && embedded.is_some() {
        return Err(invalid("v3 INSTALL duplicate incomplete op70 marker"));
    }
    if let Some(marker) = active.as_ref().or(embedded.as_ref()) {
        if *marker
            != retained_marker_bytes(&config.artifact("completion-v2-author/op70-requested.json"))?
        {
            return Err(invalid("v3 INSTALL incomplete op70 marker differs"));
        }
    }
    if active.is_some() {
        // This ordering makes a crash at either rename boundary recoverable.
        fs::rename(&active_path, &embedded_path)?;
        fs::File::open(config.artifact("completion-v2-author"))?.sync_all()?;
        fs::File::open(&config.journal_dir)?.sync_all()?;
    }
    archive_pure_attempt(config, "completion-v2-author")?
        .ok_or_else(|| invalid("v3 INSTALL incomplete completion attempt absent"))?;
    Ok(())
}

fn preflight_prepare_artifacts(config: &InstallConfig) -> io::Result<()> {
    // A journal is one attempt. Reject both namespaces so an old v1 attempt
    // cannot accidentally be presented as a fresh v3 operation, or vice versa.
    config.preflight_artifacts()?;
    for name in V3_ARTIFACTS {
        match fs::symlink_metadata(config.artifact(name)) {
            Ok(_) => return Err(invalid("launch-bound INSTALL attempt already exists")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    Ok(())
}

pub(super) fn preflight_prepare(config: &InstallConfig) -> io::Result<()> {
    config.preflight_operator_paths()?;
    preflight_prepare_artifacts(config)?;
    let qualification = QualifiedLaunch::read(config)?;
    open_protected_directory(
        config
            .source_spk
            .parent()
            .ok_or_else(|| invalid("SPK parent absent"))?,
        config.app_uid,
        false,
    )?;
    let source = super::private_file(&config.source_spk, MAX_SPK)?;
    if super::hex(&Sha256::digest(&source)) != config.expected_raw_sha256 {
        return Err(invalid("v3 INSTALL source SPK differs from pinned raw SHA"));
    }
    drop(source);
    let (package, _) = qualify_bridge_spk(&config.source_spk)?;
    if package.raw_sha256 != config.expected_raw_sha256 {
        return Err(invalid("v3 INSTALL signed source SPK changed"));
    }
    let operator = config.operator();
    preflight_custodian(
        &operator,
        &config.completion_custodian_seed,
        &config.completion_semantics,
    )?;
    let begin_signers: FixedLaunchBeginSigners = serde_json::from_slice(&super::private_file(
        &config.begin_management_custody,
        MAX_CONFIG,
    )?)?;
    let claim_signers: FixedLaunchClaimSigners = serde_json::from_slice(&super::private_file(
        &config.claim_management_custody,
        MAX_CONFIG,
    )?)?;
    begin_signers.validate(&operator, config.app_uid)?;
    claim_signers.validate(&operator, config.app_uid)?;
    let launch = author_qualified_launch(
        config,
        &operator,
        &package,
        &qualification,
        &config.artifact("launch-descriptor"),
    )?;
    let begin = submit_begin_once(
        &operator,
        &begin_signers,
        config.app_uid,
        &launch,
        LaunchBeginAction::Install,
        &config.artifact("begin-v3-operation-ledger"),
        &config.artifact("begin-v3"),
    )?;
    let assembled = assemble_claim_once(
        &operator,
        &claim_signers,
        config.app_uid,
        &begin,
        &launch,
        &config.artifact("claim-v3-nonce-ledger"),
        &config.artifact("claim-v3-author"),
    )?;
    let claim = submit_claim_once(&operator, assembled, &begin, &launch, &claim_signers)?;
    if claim.physical_begin.package_sha256 != config.expected_raw_sha256 {
        return Err(invalid("v3 INSTALL claim differs from signed SPK"));
    }
    let stage = json!({
        "protocol":"mini-spk-install-prepared-v2",
        "rawSha256":package.raw_sha256,
        "launchRoot":launch.descriptor().root,
        "launchCanonicalSha256":super::hex(&Sha256::digest(&launch.descriptor().canonical)),
        "beginSha256":super::hex(&Sha256::digest(&begin.ingress)),
        "claimIngressSha256":super::hex(&Sha256::digest(&claim.claim_ingress)),
        "committedClaimSha256":super::hex(&Sha256::digest(&claim.committed)),
        "begin":{
            "clientOperationId":begin.client_operation_id,
            "authorizationOperationId":begin.authorization_operation_id,
            "volumeIdHex":begin.volume_id_hex,
            "snapshotManifest":begin.snapshot_manifest,
            "processGeneration":begin.process_generation,
            "processIdentityHex":begin.process_identity_hex,
            "transactionId":begin.transaction_id,
            "eventId":begin.event_id,
            "acceptedCount":begin.accepted_count,
            "worldRoot":begin.world_root,
        },
        "claim":{
            "physicalBegin":claim.physical_begin,
            "transactionId":claim.transaction_id,
            "eventId":claim.event_id,
            "acceptedCount":claim.accepted_count,
            "worldRoot":claim.world_root,
        },
    });
    write_new(
        &config.journal_dir,
        "install-prepared-v2.json",
        &serde_json::to_vec(&stage)?,
    )?;
    Ok(())
}

pub(super) fn preflight_complete(config: &InstallConfig) -> io::Result<()> {
    config.preflight_operator_paths()?;
    crate::dispatch_native::private_dir(&config.journal_dir)?;
    let lock = fs::File::open(&config.journal_dir)?;
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(invalid("v3 INSTALL completion already in progress"));
    }
    let completed_marker_exists =
        match fs::symlink_metadata(config.artifact("install-completed-v2.json")) {
            Ok(_) => true,
            Err(error) if error.kind() == io::ErrorKind::NotFound => false,
            Err(error) => return Err(error),
        };
    let qualification = QualifiedLaunch::read(config)?;
    let stage: Value = serde_json::from_slice(&super::private_file(
        &config.artifact("install-prepared-v2.json"),
        MAX_QUALIFICATION,
    )?)?;
    let stage_field = |name: &str| -> io::Result<&str> {
        stage
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("v3 INSTALL retained preparation field absent"))
    };
    if stage_field("protocol")? != "mini-spk-install-prepared-v2"
        || stage_field("rawSha256")? != config.expected_raw_sha256
        || stage_field("launchRoot")? != qualification.launch_root
        || stage_field("launchCanonicalSha256")? != qualification.launch_canonical_sha256
    {
        return Err(invalid("v3 INSTALL retained preparation differs"));
    }
    let package = verify_installed_spk(&config.image_dir, config.app_uid)?;
    if package.raw_sha256 != config.expected_raw_sha256 {
        return Err(invalid(
            "v3 INSTALL protected image differs from source SPK",
        ));
    }
    let begin_ingress =
        super::private_file(&config.artifact("begin-v3/begin-v3.bin"), super::MAX_CLAIM)?;
    let claim_ingress = super::private_file(
        &config.artifact("claim-v3-author/claim-v3.bin"),
        super::MAX_CLAIM,
    )?;
    let committed = super::private_file(
        &config.artifact("claim-v3-author/committed-v3.bin"),
        super::MAX_CLAIM,
    )?;
    if stage_field("beginSha256")? != super::hex(&Sha256::digest(&begin_ingress))
        || stage_field("claimIngressSha256")? != super::hex(&Sha256::digest(&claim_ingress))
        || stage_field("committedClaimSha256")? != super::hex(&Sha256::digest(&committed))
    {
        return Err(invalid("v3 INSTALL retained native artifacts changed"));
    }
    let field = |object: &Value, name: &str| -> io::Result<String> {
        let value = object
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("v3 INSTALL retained lifecycle field absent"))?;
        if !crate::lifecycle_v3_native::decimal(value) {
            return Err(invalid("v3 INSTALL retained lifecycle field noncanonical"));
        }
        Ok(value.to_owned())
    };
    let saved_begin = stage
        .get("begin")
        .ok_or_else(|| invalid("v3 INSTALL retained BEGIN absent"))?;
    let begin = AcceptedLaunchBegin {
        ingress: begin_ingress,
        action: LaunchBeginAction::Install,
        prior_create: None,
        client_operation_id: field(saved_begin, "clientOperationId")?,
        authorization_operation_id: field(saved_begin, "authorizationOperationId")?,
        volume_id_hex: saved_begin
            .get("volumeIdHex")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("v3 INSTALL retained volume absent"))?
            .to_owned(),
        snapshot_manifest: field(saved_begin, "snapshotManifest")?,
        process_generation: field(saved_begin, "processGeneration")?,
        process_identity_hex: saved_begin
            .get("processIdentityHex")
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("v3 INSTALL retained process identity absent"))?
            .to_owned(),
        transaction_id: field(saved_begin, "transactionId")?,
        event_id: field(saved_begin, "eventId")?,
        accepted_count: field(saved_begin, "acceptedCount")?,
        world_root: field(saved_begin, "worldRoot")?,
    };
    let saved_claim = stage
        .get("claim")
        .ok_or_else(|| invalid("v3 INSTALL retained claim absent"))?;
    let physical_begin: VerifiedBegin = serde_json::from_value(
        saved_claim
            .get("physicalBegin")
            .cloned()
            .ok_or_else(|| invalid("v3 INSTALL retained physical BEGIN absent"))?,
    )?;
    let claim = CommittedLaunchClaim {
        committed,
        inspection: Vec::new(),
        claim_ingress,
        physical_begin,
        transaction_id: field(saved_claim, "transactionId")?,
        event_id: field(saved_claim, "eventId")?,
        accepted_count: field(saved_claim, "acceptedCount")?,
        world_root: field(saved_claim, "worldRoot")?,
    };
    if claim.physical_begin.operation_id != begin.authorization_operation_id
        || claim.physical_begin.transaction_id != claim.transaction_id
        || claim.physical_begin.event_id != claim.event_id
        || claim.physical_begin.package_sha256 != config.expected_raw_sha256
        || begin.volume_id_hex.len() != 64
        || !begin
            .volume_id_hex
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid("v3 INSTALL retained claim identity differs"));
    }
    let inspected: Value = serde_json::from_slice(&super::private_file(
        &config.artifact("claim-v3-author/committed-v3.json"),
        8 * super::MAX_CLAIM,
    )?)?;
    let inspected_field = |name: &str| -> io::Result<&str> {
        inspected
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("v3 INSTALL source claim inspection field absent"))
    };
    let receipt = inspected
        .get("receipt")
        .ok_or_else(|| invalid("v3 INSTALL source claim receipt absent"))?;
    if inspected_field("type")? != "application-lifecycle-claim-committed-v3"
        || inspected_field("frameHex")? != super::hex(&claim.committed)
        || inspected_field("originalClaimHex")? != super::hex(&claim.claim_ingress)
        || inspected_field("originalBeginHex")? != super::hex(&begin.ingress)
        || inspected_field("kind")? != "install"
        || inspected.get("binding") != Some(&Value::Null)
        || inspected_field("descriptorRoot")? != qualification.launch_root
        || inspected_field("volumeIdHex")? != begin.volume_id_hex
        || inspected_field("authorizationOperationId")? != begin.authorization_operation_id
        || inspected_field("processGeneration")? != begin.process_generation
        || inspected_field("processIdentityHex")? != begin.process_identity_hex
        || inspected_field("imageIdentityHex")? != claim.physical_begin.image_identity
        || inspected_field("app")? != claim.physical_begin.app.to_string()
        || receipt.get("transactionId").and_then(Value::as_str)
            != Some(claim.transaction_id.as_str())
        || receipt.get("eventId").and_then(Value::as_str) != Some(claim.event_id.as_str())
        || receipt.get("acceptedCount").and_then(Value::as_str)
            != Some(claim.accepted_count.as_str())
        || receipt.get("worldRoot").and_then(Value::as_str)
            != Some(claim.world_root.as_str())
    {
        return Err(invalid(
            "v3 INSTALL retained source claim inspection differs",
        ));
    }
    if completed_marker_exists {
        let completed: Value = serde_json::from_slice(&super::private_file(
            &config.artifact("install-completed-v2.json"),
            MAX_QUALIFICATION,
        )?)?;
        let completion = completed
            .get("completionReceipt")
            .ok_or_else(|| invalid("v3 INSTALL completed receipt absent"))?;
        if completed.get("protocol").and_then(Value::as_str)
            != Some("mini-spk-install-completed-v2")
            || completed.get("rawSha256").and_then(Value::as_str)
                != Some(config.expected_raw_sha256.as_str())
            || completed.get("launchRoot").and_then(Value::as_str)
                != Some(qualification.launch_root.as_str())
            || completed.get("originalBeginSha256").and_then(Value::as_str)
                != Some(super::hex(&Sha256::digest(&begin.ingress)).as_str())
            || completed
                .get("committedClaimSha256")
                .and_then(Value::as_str)
                != Some(super::hex(&Sha256::digest(&claim.committed)).as_str())
            || !completion
                .get("acceptedCount")
                .and_then(Value::as_str)
                .is_some_and(|count| {
                    crate::lifecycle_v3_claim_native::later_decimal(count, &claim.accepted_count)
                })
        {
            return Err(invalid(
                "v3 INSTALL completed marker differs from retained lifecycle",
            ));
        }
        retire_success_markers(config)?;
        return Ok(());
    }
    let operator = config.operator();
    preflight_custodian(
        &operator,
        &config.completion_custodian_seed,
        &config.completion_semantics,
    )?;
    let mut completion_attempt_exists =
        match fs::symlink_metadata(config.artifact("completion-v2-author")) {
            Ok(_) => true,
            Err(error) if error.kind() == io::ErrorKind::NotFound => false,
            Err(error) => return Err(error),
        };
    let op38_started =
        match fs::symlink_metadata(config.artifact("completion-v2-author/op38-requested.json")) {
            Ok(_) => true,
            Err(error) if error.kind() == io::ErrorKind::NotFound => false,
            Err(error) => return Err(error),
        };
    let ingress_saved =
        match fs::symlink_metadata(config.artifact("completion-v2-author/completion-v2.bin")) {
            Ok(_) => true,
            Err(error) if error.kind() == io::ErrorKind::NotFound => false,
            Err(error) => return Err(error),
        };
    if op38_started && !ingress_saved {
        return Err(invalid(
            "v3 INSTALL submit marker lacks original completion ingress",
        ));
    }
    if !ingress_saved {
        if completion_attempt_exists {
            archive_incomplete_completion_attempt(config)?;
        } else if fs::symlink_metadata(config.artifact("lifecycle-completion-v2-active.json"))
            .is_ok()
        {
            return Err(invalid("v3 INSTALL completion marker has no attempt"));
        }
        // Op70/71 are current-image author/assembly only; without an op38
        // marker they have not submitted event25 or caused a physical effect.
        // Keep each interrupted subattempt intact and reprepare from the same
        // protected image/BEGIN/claim under the exclusive journal lock.
        archive_pure_attempt(config, "materialized-report-v2")?;
        archive_pure_attempt(config, "materialized-verify-v2")?;
        completion_attempt_exists = false;
    }
    let completed = if completion_attempt_exists {
        let signed_report = super::private_file(
            &config.artifact("materialized-report-v2/signed-report.bin"),
            super::MAX_CLAIM,
        )?;
        let assembled = load_completion_retained(
            &config.artifact("completion-v2-author"),
            &begin,
            &claim,
            &signed_report,
        )?;
        match fs::symlink_metadata(config.artifact("completion-v2-author/op38-requested.json")) {
            Ok(_) => {
                recover_receipt_only(&operator, &assembled, &begin, &claim, &signed_report)?.receipt
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                submit_completion_once(&operator, &assembled, &begin, &claim, &signed_report, None)?
            }
            Err(error) => return Err(error),
        }
    } else {
        let launch = author_qualified_launch(
            config,
            &operator,
            &package,
            &qualification,
            &config.artifact("materialized-verify-v2"),
        )?;
        if launch.descriptor().root != stage_field("launchRoot")? {
            return Err(invalid("v3 INSTALL published image launch root differs"));
        }
        let report = prepare_report_once(
            &operator,
            ReportInput {
                begin: &begin,
                claim: &claim,
                launch: &launch,
                mode: PhysicalMode::Materialized,
            },
            &config.completion_custodian_seed,
            &config.completion_semantics,
            &config.artifact("materialized-report-v2"),
        )?;
        let signers: FixedLaunchCompletionSigners = serde_json::from_slice(&super::private_file(
            &config.completion_management_custody,
            MAX_CONFIG,
        )?)?;
        let assembled = assemble_completion_once(
            &operator,
            &signers,
            config.app_uid,
            CompletionInput {
                begin: &begin,
                claim: &claim,
                launch: &launch,
                signed_report: &report.signed_report,
            },
            &config.artifact("completion-v2-author"),
        )?;
        submit_completion_once(
            &operator,
            &assembled,
            &begin,
            &claim,
            &report.signed_report,
            None,
        )?
    };
    write_new(
        &config.journal_dir,
        "install-completed-v2.json",
        &serde_json::to_vec(&json!({
            "protocol":"mini-spk-install-completed-v2",
            "rawSha256":config.expected_raw_sha256,
            "launchRoot":qualification.launch_root,
            "originalBeginSha256":super::hex(&Sha256::digest(&begin.ingress)),
            "committedClaimSha256":super::hex(&Sha256::digest(&claim.committed)),
            "completionReceipt":{
                "transactionId":completed.transaction_id,
                "eventId":completed.event_id,
                "acceptedCount":completed.accepted_count,
                "worldRoot":completed.world_root,
            }
        }))?,
    )?;
    retire_success_markers(config)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_native::SourceDescriptor;
    use crate::dispatch_native::write_new;
    use std::os::unix::fs::DirBuilderExt;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn config(journal_dir: PathBuf) -> InstallConfig {
        InstallConfig {
            protocol: "mini-spk-resident-install-v2".into(),
            journal_dir,
            source_spk: PathBuf::from("/nonexistent/source.spk"),
            image_dir: PathBuf::from("/nonexistent/image"),
            expected_raw_sha256: "a".repeat(64),
            app_uid: 12345,
            deployment_id: Some("d".repeat(64)),
            host_id: Some("e".repeat(64)),
            launch_qualification: Some(PathBuf::from("/private/qualification.json")),
            mini_host: PathBuf::from("/nonexistent/host"),
            mini_host_sha256: "b".repeat(64),
            mini_config: PathBuf::from("/nonexistent/config"),
            mini_config_sha256: "c".repeat(64),
            mini_operator_socket: PathBuf::from("/nonexistent/socket"),
            begin_management_custody: PathBuf::from("/nonexistent/begin"),
            claim_management_custody: PathBuf::from("/nonexistent/claim"),
            completion_management_custody: PathBuf::from("/nonexistent/completion"),
            completion_custodian_seed: PathBuf::from("/nonexistent/seed"),
            completion_semantics: "1".into(),
        }
    }

    #[test]
    fn v3_artifact_namespace_refuses_v1_or_v3_attempt() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "spk-install-v3-artifacts-{}-{stamp}",
            std::process::id()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let config = config(dir.clone());
        preflight_prepare_artifacts(&config).unwrap();
        for artifact in ["descriptor", "begin-v3", "install-prepared-v2.json"] {
            let path = write_new(&dir, artifact, b"held").unwrap();
            assert!(preflight_prepare_artifacts(&config).is_err());
            assert!(std::fs::symlink_metadata(&path).is_ok());
            std::fs::remove_file(path).unwrap();
        }
        std::fs::remove_dir(dir).unwrap();
    }

    #[test]
    fn confirmed_install_retires_only_exact_lifecycle_markers() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "spk-install-v3-retire-{}-{stamp}",
            std::process::id()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let config = config(dir.clone());
        for (active, attempt_dir, requested) in [
            (
                "lifecycle-begin-v3-active.json",
                "begin-v3",
                "op66-requested.json",
            ),
            (
                "lifecycle-claim-v3-active.json",
                "claim-v3-author",
                "op68-requested.json",
            ),
            (
                "lifecycle-completion-v2-active.json",
                "completion-v2-author",
                "op70-requested.json",
            ),
        ] {
            std::fs::DirBuilder::new()
                .mode(0o700)
                .create(dir.join(attempt_dir))
                .unwrap();
            write_new(&dir.join(attempt_dir), requested, b"exact marker").unwrap();
            write_new(&dir, active, b"exact marker").unwrap();
        }
        std::fs::write(
            dir.join("lifecycle-begin-v3-active.json"),
            b"different marker",
        )
        .unwrap();
        assert!(retire_success_markers(&config).is_err());
        assert!(dir.join("lifecycle-begin-v3-active.json").exists());
        assert!(dir.join("lifecycle-claim-v3-active.json").exists());
        assert!(dir.join("lifecycle-completion-v2-active.json").exists());
        assert!(dir.join("begin-v3/op66-requested.json").exists());
        std::fs::write(dir.join("lifecycle-begin-v3-active.json"), b"exact marker").unwrap();
        retire_success_markers(&config).unwrap();
        retire_success_markers(&config).unwrap();
        assert!(!dir.join("lifecycle-begin-v3-active.json").exists());
        assert!(!dir.join("lifecycle-claim-v3-active.json").exists());
        assert!(!dir.join("lifecycle-completion-v2-active.json").exists());
        assert!(dir.join("begin-v3/op66-requested.json").exists());
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn incomplete_op70_archive_recovers_each_rename_boundary() {
        let stamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "spk-install-v3-archive-{}-{stamp}",
            std::process::id()
        ));
        std::fs::DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let config = config(dir.clone());
        let attempt = dir.join("completion-v2-author");
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&attempt)
            .unwrap();
        write_new(&attempt, "op70-requested.json", b"exact").unwrap();
        write_new(&dir, "lifecycle-completion-v2-active.json", b"exact").unwrap();
        archive_incomplete_completion_attempt(&config).unwrap();
        assert!(!attempt.exists());
        assert!(!dir.join("lifecycle-completion-v2-active.json").exists());
        let archived = std::fs::read_dir(&dir)
            .unwrap()
            .filter_map(Result::ok)
            .find(|entry| {
                entry
                    .file_name()
                    .to_string_lossy()
                    .starts_with("completion-v2-author-aborted-pre-op38-")
            })
            .unwrap()
            .path();
        assert_eq!(
            std::fs::read(archived.join("active-marker.json")).unwrap(),
            b"exact"
        );
        // Simulate a crash after the parent marker moved inside the still-named attempt.
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(&attempt)
            .unwrap();
        write_new(&attempt, "op70-requested.json", b"second").unwrap();
        write_new(&attempt, "active-marker.json", b"second").unwrap();
        archive_incomplete_completion_attempt(&config).unwrap();
        assert!(!attempt.exists());
        assert_eq!(
            std::fs::read(archived.join("active-marker.json")).unwrap(),
            b"exact"
        );
        std::fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn deployment_and_host_pins_are_required_only_for_v2_install() {
        let mut config = config(PathBuf::from("/private/install"));
        assert!(config.valid_host_identity());
        config.host_id = None;
        assert!(!config.valid_host_identity());
        config.host_id = Some("F".repeat(64));
        assert!(!config.valid_host_identity());
        config.host_id = Some("e".repeat(64));
        config.launch_qualification = None;
        assert!(!config.valid_host_identity());
        config.launch_qualification = Some(PathBuf::from("/private/qualification.json"));
        config.protocol = "mini-spk-resident-install-v1".into();
        assert!(!config.valid_host_identity());
        config.deployment_id = None;
        config.host_id = None;
        config.launch_qualification = None;
        assert!(config.valid_host_identity());
    }

    #[test]
    fn retained_qualifier_must_equal_entire_source_authored_launch() {
        let launch = SourceLaunchDescriptor {
            package: SourceDescriptor {
                canonical: b"package".to_vec(),
                root: "11".into(),
                image_identity: b"image".to_vec(),
                api_path: None,
            },
            canonical: b"launch".to_vec(),
            root: "22".into(),
            create_digests: vec!["33".into(), "44".into()],
            continue_digest: "55".into(),
        };
        let qualification = QualifiedLaunch {
            protocol: "mini-spk-launch-qualified-v2".into(),
            raw_sha256: "a".repeat(64),
            package_root: "11".into(),
            launch_root: "22".into(),
            launch_canonical_sha256: super::super::hex(&Sha256::digest(&launch.canonical)),
            create_count: "2".into(),
            create_digests: vec!["33".into(), "44".into()],
            continue_digest: "55".into(),
        };
        qualification.matches(&launch, &"a".repeat(64)).unwrap();
        let mut wrong = qualification;
        wrong.create_digests.swap(0, 1);
        assert!(wrong.matches(&launch, &"a".repeat(64)).is_err());
        wrong.create_digests.swap(0, 1);
        wrong.launch_canonical_sha256 = "b".repeat(64);
        assert!(wrong.matches(&launch, &"a".repeat(64)).is_err());
        wrong.launch_canonical_sha256 = super::super::hex(&Sha256::digest(&launch.canonical));
        wrong.package_root = "12".into();
        assert!(wrong.matches(&launch, &"a".repeat(64)).is_err());
    }
}
