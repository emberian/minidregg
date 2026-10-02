//! One operator-owned systemd MainPID holds the verified app and its fd3 RPC.
//! START consumes current-image BEGIN/claim plans once, launches the one fd3
//! owner, and opens HTTP only after fresh native physical completion. INSTALL
//! materialization and stopped wake remain separate lifecycle operations.
#![allow(dead_code)] // Enabled only after root reviews the exact native cut.

use crate::agent_api_custody::AgentCustody;
use crate::agent_api_lifetime_custody_v3::LifetimeCustodyV3;
use crate::agent_api_lifetime_reverse_v3::LifetimeReverseClient;
use crate::agent_api_lifetime_server_v3::{self, ResidentLifetimeAgent};
use crate::agent_api_native::ReverseCustodyClient;
use crate::agent_api_server::{AgentApiListener, ResidentAgent};
use crate::completion_native::preflight_custodian;
use crate::dispatch_author::FixedAuthoring;
use crate::dispatch_delivery::{ResidentHuman, UpgradeRequest};
use crate::dispatch_inspection::{HttpProjection, Route};
use crate::dispatch_native::{private_dir, write_new, PrivateOperator};
use crate::hostd::{Journal, PriorUnitState, VerifiedBegin};
use crate::http_entrance::{CustodianPolicy, EntranceKind, PrivateHttpEntrance, ReceivedRequest};
use crate::lifecycle_v3_claim_native::{
    assemble_once as assemble_v3_claim, submit_fresh_once as submit_v3_claim, CommittedLaunchClaim,
    FixedLaunchClaimSigners,
};
use crate::lifecycle_v3_completion_native::{
    assemble_once as assemble_v3_completion, checked_receipt as checked_v3_completion_receipt,
    load_retained as load_v3_completion, recover_receipt_only as recover_v3_completion,
    submit_fresh_once as submit_v3_completion, CompletionInput, ConfirmedLaunchCompletion,
    FixedLaunchCompletionSigners,
};
use crate::lifecycle_v3_native::{
    submit_once as submit_v3_begin, AcceptedLaunchBegin, CreatedWitness, FixedLaunchBeginSigners,
};
use crate::lifecycle_v3_report_native::{
    prepare_once as prepare_v3_running_report, PhysicalMode, ReportInput,
};
use crate::materialize::verify_installed_spk;
use crate::resident_launch::PreparedResident;
use crate::resident_launch::SourceBoundLaunch;
use crate::resident_route_control::{self, RouteControl, RouteRegistrationReply};
use crate::sandbox::{open_protected_directory, SandboxSpec};
use crate::volume_custody::{read_attested_volume, VolumeSite};
use minidregg_spk_rpc::decode_bridge_config;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::Duration;

const MAX_CONFIG: u64 = 16 * 1024;
// Retained routes must remain loadable after the live registry grows. Keep
// individual custody bounds small while bounding the whole resident config.
const MAX_RESIDENT_CONFIG: u64 = MAX_CONFIG * (resident_route_control::MAX_ROUTES as u64 + 1);
const MAX_LIFECYCLE: u64 = 12_102_759;

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn private_file(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    let parent = path
        .parent()
        .ok_or_else(|| invalid("private file parent absent"))?;
    private_dir(parent)?;
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !path.is_absolute()
        || !meta.is_file()
        || meta.nlink() != 1
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.permissions().mode() & 0o777 != 0o600
        || meta.len() == 0
        || meta.len() > max
    {
        return Err(invalid("operator private file identity or size refused"));
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    file.take(max + 1).read_to_end(&mut bytes)?;
    if bytes.len() as u64 != meta.len() || bytes.len() as u64 > max {
        return Err(invalid("operator private file changed while reading"));
    }
    Ok(bytes)
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedEntranceConfig {
    directory: PathBuf,
    dispatch_custody: PathBuf,
    display_name: String,
    preferred_handle: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct FixedAgentConfig {
    #[serde(default)]
    protocol: Option<String>,
    #[serde(default)]
    reverse_timeout_seconds: Option<u64>,
    #[serde(default)]
    controller_worker_wall_seconds: Option<u64>,
    socket: PathBuf,
    controller_uid: u32,
    custody: PathBuf,
    reverse_socket: PathBuf,
    route_name: String,
    attempt_dir: PathBuf,
    display_name: String,
    preferred_handle: String,
}

enum PreparedAgent {
    V2(Box<AgentCustody>, ReverseCustodyClient),
    V3(Box<LifetimeCustodyV3>, LifetimeReverseClient),
}

impl PreparedAgent {
    fn coordinates(&self) -> (&str, &str, &str, &str) {
        match self {
            Self::V2(custody, _) => (
                &custody.session,
                &custody.ticket_resource,
                &custody.parent_task,
                &custody.purse_task,
            ),
            Self::V3(custody, _) => (
                &custody.lineage.session_resource,
                &custody.lineage.ticket_resource,
                &custody.lineage.parent_task,
                &custody.lineage.purse_task,
            ),
        }
    }
}

fn default_stream_lease_seconds() -> u64 {
    crate::web_socket::DEFAULT_LEASE_SECONDS
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ResidentConfig {
    protocol: String,
    journal_dir: PathBuf,
    image_dir: PathBuf,
    expected_raw_sha256: String,
    launch_qualification: PathBuf,
    start_action: StartAction,
    volume_resource: u64,
    expected_volume_id: String,
    persistent_var: PathBuf,
    persistent_var_max_bytes: u64,
    /// The app's size class (S, M or L): its WebSocket caps come from here.
    size_class: String,
    #[serde(default = "default_stream_lease_seconds")]
    ws_authority_lease_seconds: u64,
    grains_root: PathBuf,
    store: String,
    deployment_id: String,
    host_id: String,
    bwrap: PathBuf,
    bwrap_sha256: String,
    app_uid: u32,
    app_gid: u32,
    unit: String,
    mini_host: PathBuf,
    mini_host_sha256: String,
    mini_config: PathBuf,
    mini_config_sha256: String,
    mini_operator_socket: PathBuf,
    begin_management_custody: PathBuf,
    claim_management_custody: PathBuf,
    begin_operation_ledger: PathBuf,
    claim_nonce_ledger: PathBuf,
    descriptor_attempt_dir: PathBuf,
    begin_attempt_dir: PathBuf,
    claim_author_attempt_dir: PathBuf,
    claim_attempt_dir: PathBuf,
    completion_attempt_dir: PathBuf,
    completion_sign_attempt_dir: PathBuf,
    completion_submit_attempt_dir: PathBuf,
    completion_custodian_seed: PathBuf,
    completion_management_custody: PathBuf,
    completion_semantics: String,
    entrances: Vec<FixedEntranceConfig>,
    #[serde(default)]
    agents: Vec<FixedAgentConfig>,
}

#[derive(Deserialize, Serialize, PartialEq, Eq)]
#[serde(
    tag = "kind",
    rename_all = "lowercase",
    rename_all_fields = "camelCase",
    deny_unknown_fields
)]
enum StartAction {
    Create { index: usize },
    Continue { created_index: String },
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SavedCreatedWitness {
    receipt_hex: String,
    custody_hex: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SavedStartBegin {
    client_operation_id: String,
    authorization_operation_id: String,
    volume_id_hex: String,
    snapshot_manifest: String,
    process_generation: String,
    process_identity_hex: String,
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    world_root: String,
    prior_create: Option<SavedCreatedWitness>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SavedStartClaim {
    physical_begin: VerifiedBegin,
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    world_root: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct SavedStartStage {
    protocol: String,
    raw_sha256: String,
    launch_root: String,
    start_action: StartAction,
    begin_sha256: String,
    claim_ingress_sha256: String,
    committed_claim_sha256: String,
    claim_inspection_sha256: String,
    begin: SavedStartBegin,
    claim: SavedStartClaim,
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

impl QualifiedLaunch {
    fn matches(config: &ResidentConfig, launch: &SourceBoundLaunch<'_>) -> io::Result<()> {
        let qualified: Self =
            serde_json::from_slice(&private_file(&config.launch_qualification, MAX_CONFIG)?)?;
        let descriptor = launch.descriptor();
        if qualified.protocol != "mini-spk-launch-qualified-v2"
            || qualified.raw_sha256 != config.expected_raw_sha256
            || qualified.raw_sha256 != launch.signed_package_sha256()
            || qualified.package_root != descriptor.package.root
            || qualified.launch_root != descriptor.root
            || qualified.launch_canonical_sha256
                != format!("{:x}", Sha256::digest(&descriptor.canonical))
            || qualified.create_count != descriptor.create_digests.len().to_string()
            || qualified.create_digests != descriptor.create_digests
            || qualified.continue_digest != descriptor.continue_digest
        {
            return Err(invalid(
                "signed START launch differs from retained qualifier",
            ));
        }
        Ok(())
    }
}

impl StartAction {
    fn native(&self) -> io::Result<crate::lifecycle_v3_native::LaunchBeginAction> {
        use crate::lifecycle_v3_native::LaunchBeginAction;
        match self {
            Self::Create { index } => Ok(LaunchBeginAction::Create(*index)),
            Self::Continue { created_index }
                if crate::lifecycle_v3_native::decimal(created_index) =>
            {
                Ok(LaunchBeginAction::Continue {
                    created_index: created_index.clone(),
                })
            }
            Self::Continue { .. } => Err(invalid("START created index noncanonical")),
        }
    }
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn agent_socket_parent_overlap(earlier: &[FixedAgentConfig], socket: &Path) -> bool {
    let Some(parent) = socket.parent() else {
        return true;
    };
    earlier.iter().any(|prior| {
        let Some(prior_parent) = prior.socket.parent() else {
            return true;
        };
        parent.starts_with(prior_parent) || prior_parent.starts_with(parent)
    })
}

fn retire_start_markers(
    config: &ResidentConfig,
    _completion: &ConfirmedLaunchCompletion,
) -> io::Result<()> {
    let mut present = Vec::new();
    for (active, retained, retained_name) in [
        (
            "lifecycle-completion-v2-active.json",
            &config.completion_sign_attempt_dir,
            "op70-requested.json",
        ),
        (
            "lifecycle-claim-v3-active.json",
            &config.claim_author_attempt_dir,
            "op68-requested.json",
        ),
        (
            "lifecycle-begin-v3-active.json",
            &config.begin_attempt_dir,
            "op66-requested.json",
        ),
    ] {
        let active_path = config.journal_dir.join(active);
        match fs::symlink_metadata(&active_path) {
            Ok(metadata) if metadata.is_file() && !metadata.file_type().is_symlink() => {
                if private_file(&active_path, MAX_CONFIG)?
                    != private_file(&retained.join(retained_name), MAX_CONFIG)?
                {
                    return Err(invalid(
                        "START success marker differs from retained attempt",
                    ));
                }
                present.push(active_path);
            }
            Ok(_) => return Err(invalid("START success marker identity refused")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    for path in present {
        fs::remove_file(path)?;
    }
    File::open(&config.journal_dir)?.sync_all()
}

fn load_retained_start(
    config: &ResidentConfig,
) -> io::Result<(Vec<u8>, AcceptedLaunchBegin, CommittedLaunchClaim)> {
    let admitted_bytes = private_file(
        &config.journal_dir.join("start-admitted-v3.json"),
        MAX_CONFIG,
    )?;
    let stage: SavedStartStage = serde_json::from_slice(&admitted_bytes)?;
    let qualification: QualifiedLaunch =
        serde_json::from_slice(&private_file(&config.launch_qualification, MAX_CONFIG)?)?;
    let begin_ingress = private_file(
        &config.begin_attempt_dir.join("begin-v3.bin"),
        MAX_LIFECYCLE,
    )?;
    let claim_ingress = private_file(
        &config.claim_author_attempt_dir.join("claim-v3.bin"),
        MAX_LIFECYCLE,
    )?;
    let committed = private_file(
        &config.claim_author_attempt_dir.join("committed-v3.bin"),
        MAX_LIFECYCLE,
    )?;
    let sha = |bytes: &[u8]| format!("{:x}", Sha256::digest(bytes));
    if stage.protocol != "mini-spk-resident-start-admitted-v3"
        || stage.raw_sha256 != config.expected_raw_sha256
        || stage.launch_root != qualification.launch_root
        || stage.start_action != config.start_action
        || stage.begin_sha256 != sha(&begin_ingress)
        || stage.claim_ingress_sha256 != sha(&claim_ingress)
        || stage.committed_claim_sha256 != sha(&committed)
    {
        return Err(invalid(
            "retained START stage differs from exact native artifacts",
        ));
    }
    let saved = stage.begin;
    let original_fields = [
        &saved.client_operation_id,
        &saved.authorization_operation_id,
        &saved.snapshot_manifest,
        &saved.process_generation,
        &saved.transaction_id,
        &saved.event_id,
        &saved.accepted_count,
        &saved.world_root,
    ];
    if original_fields
        .iter()
        .any(|field| !crate::lifecycle_v3_native::decimal(field))
        || saved.volume_id_hex != config.expected_volume_id
        || !hex64(&saved.volume_id_hex)
        || saved.process_identity_hex.is_empty()
        || !crate::lifecycle_v3_native::lowercase_hex(&saved.process_identity_hex)
    {
        return Err(invalid("retained START BEGIN identity malformed"));
    }
    let action = stage.start_action.native()?;
    let prior_create = saved.prior_create.map(|witness| CreatedWitness {
        receipt_hex: witness.receipt_hex,
        custody_hex: witness.custody_hex,
    });
    if matches!(
        action,
        crate::lifecycle_v3_native::LaunchBeginAction::Create(_)
    ) != prior_create.is_none()
    {
        return Err(invalid("retained START prior create witness shape differs"));
    }
    let begin = AcceptedLaunchBegin {
        ingress: begin_ingress,
        action,
        prior_create,
        client_operation_id: saved.client_operation_id,
        authorization_operation_id: saved.authorization_operation_id,
        volume_id_hex: saved.volume_id_hex,
        snapshot_manifest: saved.snapshot_manifest,
        process_generation: saved.process_generation,
        process_identity_hex: saved.process_identity_hex,
        transaction_id: saved.transaction_id,
        event_id: saved.event_id,
        accepted_count: saved.accepted_count,
        world_root: saved.world_root,
    };
    let saved_claim = stage.claim;
    if saved_claim.physical_begin.operation_id != begin.authorization_operation_id
        || saved_claim.physical_begin.package_sha256 != config.expected_raw_sha256
        || saved_claim.physical_begin.app != config.volume_resource
        || saved_claim.physical_begin.unit != config.unit
        || saved_claim.physical_begin.transaction_id != saved_claim.transaction_id
        || saved_claim.physical_begin.event_id != saved_claim.event_id
        || begin.process_identity_hex
            != crate::lifecycle_v3_native::hex(saved_claim.physical_begin.unit.as_bytes())
        || !crate::lifecycle_v3_claim_native::later_decimal(
            &saved_claim.accepted_count,
            &begin.accepted_count,
        )
    {
        return Err(invalid("retained START claim differs from BEGIN or unit"));
    }
    let inspection = private_file(
        &config.claim_author_attempt_dir.join("committed-v3.json"),
        8 * MAX_LIFECYCLE,
    )?;
    if stage.claim_inspection_sha256 != sha(&inspection) {
        return Err(invalid("retained START source inspection hash changed"));
    }
    let source: Value = serde_json::from_slice(&inspection)?;
    let source_field = |name| -> io::Result<&str> {
        source
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("retained START source claim field absent"))
    };
    let receipt = source
        .get("receipt")
        .ok_or_else(|| invalid("retained START source claim receipt absent"))?;
    if source_field("type")? != "application-lifecycle-claim-committed-v3"
        || source_field("frameHex")? != crate::lifecycle_v3_native::hex(&committed)
        || source_field("originalClaimHex")? != crate::lifecycle_v3_native::hex(&claim_ingress)
        || source_field("originalBeginHex")? != crate::lifecycle_v3_native::hex(&begin.ingress)
        || source_field("descriptorRoot")? != stage.launch_root
        || source_field("volumeIdHex")? != begin.volume_id_hex
        || source_field("authorizationOperationId")? != begin.authorization_operation_id
        || source_field("processIdentityHex")? != begin.process_identity_hex
        || source_field("imageIdentityHex")? != saved_claim.physical_begin.image_identity
        || receipt.get("transactionId").and_then(Value::as_str)
            != Some(saved_claim.transaction_id.as_str())
        || receipt.get("eventId").and_then(Value::as_str) != Some(saved_claim.event_id.as_str())
        || receipt.get("acceptedCount").and_then(Value::as_str)
            != Some(saved_claim.accepted_count.as_str())
        || receipt.get("worldRoot").and_then(Value::as_str) != Some(saved_claim.world_root.as_str())
    {
        return Err(invalid("retained START source inspection differs"));
    }
    let claim = CommittedLaunchClaim {
        committed,
        inspection,
        claim_ingress,
        physical_begin: saved_claim.physical_begin,
        transaction_id: saved_claim.transaction_id,
        event_id: saved_claim.event_id,
        accepted_count: saved_claim.accepted_count,
        world_root: saved_claim.world_root,
    };
    Ok((admitted_bytes, begin, claim))
}

fn checked_completion_evidence(
    attempt_dir: &Path,
    saved: &Value,
    prior_accepted_count: &str,
) -> io::Result<ConfirmedLaunchCompletion> {
    let field = |object: &Value, name: &str| -> io::Result<String> {
        let value = object
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| invalid("retained START completion field absent"))?;
        if !crate::lifecycle_v3_native::decimal(value) {
            return Err(invalid("retained START completion receipt noncanonical"));
        }
        Ok(value.to_owned())
    };
    let receipt = saved
        .get("completionReceipt")
        .ok_or_else(|| invalid("retained START completion receipt absent"))?;
    let completed = ConfirmedLaunchCompletion {
        transaction_id: field(receipt, "transactionId")?,
        event_id: field(receipt, "eventId")?,
        accepted_count: field(receipt, "acceptedCount")?,
        world_root: field(receipt, "worldRoot")?,
    };
    if !crate::lifecycle_v3_claim_native::later_decimal(
        &completed.accepted_count,
        prior_accepted_count,
    ) {
        return Err(invalid("retained START completion does not follow claim"));
    }
    let evidence_name = saved
        .get("evidenceName")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("retained START completion evidence name absent"))?;
    let confirmation = if evidence_name == "op38-outcome.json" {
        "installed"
    } else if let Some(suffix) = evidence_name.strip_prefix("op39-lookup-") {
        let nonce = suffix
            .strip_suffix("/outcome.json")
            .ok_or_else(|| invalid("retained START lookup evidence path malformed"))?;
        if nonce.len() != 32
            || !nonce
                .bytes()
                .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
        {
            return Err(invalid("retained START lookup evidence nonce malformed"));
        }
        "replayed"
    } else {
        return Err(invalid("retained START completion evidence path refused"));
    };
    let evidence = private_file(&attempt_dir.join(evidence_name), MAX_CONFIG)?;
    if saved.get("evidenceSha256").and_then(Value::as_str)
        != Some(format!("{:x}", Sha256::digest(&evidence)).as_str())
    {
        return Err(invalid("retained START completion evidence hash changed"));
    }
    let source: Value = serde_json::from_slice(&evidence)?;
    let source_receipt =
        checked_v3_completion_receipt(&source, confirmation, prior_accepted_count)?;
    if source_receipt.transaction_id != completed.transaction_id
        || source_receipt.event_id != completed.event_id
        || source_receipt.accepted_count != completed.accepted_count
        || source_receipt.world_root != completed.world_root
    {
        return Err(invalid(
            "retained START completion differs from source receipt",
        ));
    }
    Ok(completed)
}

fn read_completed_start(
    config: &ResidentConfig,
    admitted_bytes: &[u8],
    claim: &CommittedLaunchClaim,
) -> io::Result<ConfirmedLaunchCompletion> {
    let saved: Value = serde_json::from_slice(&private_file(
        &config.journal_dir.join("start-completed-v3.json"),
        MAX_CONFIG,
    )?)?;
    if saved.get("protocol").and_then(Value::as_str) != Some("mini-spk-resident-start-completed-v3")
        || saved.get("admittedSha256").and_then(Value::as_str)
            != Some(format!("{:x}", Sha256::digest(admitted_bytes)).as_str())
    {
        return Err(invalid(
            "retained START completion differs from admitted claim",
        ));
    }
    checked_completion_evidence(
        &config.completion_sign_attempt_dir,
        &saved,
        &claim.accepted_count,
    )
}

fn reconcile_prior_start(
    config: &ResidentConfig,
    operator: &PrivateOperator,
    journal: &Journal,
) -> io::Result<()> {
    let (admitted_bytes, begin, claim) = load_retained_start(config)?;
    let record = journal
        .read()?
        .ok_or_else(|| invalid("prior START journal absent"))?;
    if record.app() != claim.physical_begin.app
        || record.generation() != claim.physical_begin.generation
        || record.unit() != claim.physical_begin.unit
        || record.operation_id() != claim.physical_begin.operation_id
        || record.transaction_id() != claim.physical_begin.transaction_id
        || record.event_id() != claim.physical_begin.event_id
        || record.image_identity() != claim.physical_begin.image_identity
    {
        return Err(invalid(
            "prior START journal differs from retained fresh claim",
        ));
    }
    let op38_marker = config
        .completion_sign_attempt_dir
        .join("op38-requested.json");
    let submitted = match fs::symlink_metadata(&op38_marker) {
        Ok(meta) if meta.is_file() && !meta.file_type().is_symlink() => true,
        Ok(_) => return Err(invalid("retained START op38 marker identity refused")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => false,
        Err(error) => return Err(error),
    };
    let completed_marker = config.journal_dir.join("start-completed-v3.json");
    let completed = match fs::symlink_metadata(&completed_marker) {
        Ok(meta) if meta.is_file() && !meta.file_type().is_symlink() => {
            if !submitted {
                return Err(invalid(
                    "START completion has no original op38 submit marker",
                ));
            }
            Some(read_completed_start(config, &admitted_bytes, &claim)?)
        }
        Ok(_) => return Err(invalid("START completion marker identity refused")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => None,
        Err(error) => return Err(error),
    };
    let completed = if submitted && completed.is_none() {
        let signed_report = private_file(
            &config.completion_attempt_dir.join("signed-report.bin"),
            MAX_LIFECYCLE,
        )?;
        let assembled = load_v3_completion(
            &config.completion_sign_attempt_dir,
            &begin,
            &claim,
            &signed_report,
        )?;
        let recovered =
            recover_v3_completion(operator, &assembled, &begin, &claim, &signed_report)?;
        write_new(
            &config.journal_dir,
            "start-completed-v3.json",
            &serde_json::to_vec(&json!({
                "protocol":"mini-spk-resident-start-completed-v3",
                "admittedSha256":format!("{:x}", Sha256::digest(&admitted_bytes)),
                "evidenceName":recovered.inspection_name,
                "evidenceSha256":recovered.inspection_sha256,
                "completionReceipt":{
                    "transactionId":recovered.receipt.transaction_id,
                    "eventId":recovered.receipt.event_id,
                    "acceptedCount":recovered.receipt.accepted_count,
                    "worldRoot":recovered.receipt.world_root,
                },
            }))?,
        )?;
        Some(recovered.receipt)
    } else {
        completed
    };
    if let Some(receipt) = &completed {
        retire_start_markers(config, receipt)?;
    }
    let physical = journal.audit_prior_running(&claim.physical_begin)?;
    let physical_label = match physical {
        PriorUnitState::RunningExact => "running-exact-without-fd3-owner",
        PriorUnitState::StoppedExact => "stopped-exact-needs-source-stop",
        PriorUnitState::Uncertain => "uncertain-unit-incarnation",
    };
    let mut random = [0u8; 16];
    File::open("/dev/urandom")?.read_exact(&mut random)?;
    write_new(
        &config.journal_dir,
        &format!(
            "start-reconciliation-{}.json",
            crate::lifecycle_v3_native::hex(&random)
        ),
        &serde_json::to_vec(&json!({
            "protocol":"mini-spk-resident-start-reconciliation-v3",
            "admittedSha256":format!("{:x}", Sha256::digest(&admitted_bytes)),
            "completion":completed.as_ref().map(|receipt| json!({
                "transactionId":receipt.transaction_id,
                "eventId":receipt.event_id,
                "acceptedCount":receipt.accepted_count,
                "worldRoot":receipt.world_root,
            })),
            "physicalState":physical_label,
            "noRelaunch":true,
        }))?,
    )?;
    Err(invalid(
        "prior START reconciled without fd3; source STOP is required",
    ))
}

impl ResidentConfig {
    fn load(path: &Path) -> io::Result<Self> {
        let bytes = private_file(path, MAX_RESIDENT_CONFIG)?;
        let config: Self = serde_json::from_slice(&bytes)?;
        if config.protocol != "mini-spk-resident-start-v3"
            || path.parent() != Some(config.journal_dir.as_path())
            || config.descriptor_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.begin_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.claim_author_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.claim_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.begin_operation_ledger.parent() != Some(config.journal_dir.as_path())
            || config.claim_nonce_ledger.parent() != Some(config.journal_dir.as_path())
            || config.begin_operation_ledger == config.claim_nonce_ledger
            || config.completion_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_sign_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || config.completion_submit_attempt_dir.parent() != Some(config.journal_dir.as_path())
            || !hex64(&config.expected_raw_sha256)
            || !config.launch_qualification.is_absolute()
            || config.volume_resource == 0
            || !hex64(&config.expected_volume_id)
            || config.start_action.native().is_err()
            || !hex64(&config.bwrap_sha256)
            || !hex64(&config.mini_host_sha256)
            || !hex64(&config.mini_config_sha256)
            || !hex64(&config.deployment_id)
            || !hex64(&config.host_id)
            || config.app_uid == 0
            || config.app_gid == 0
            || config.entrances.is_empty()
            || config.entrances.len() > resident_route_control::MAX_ROUTES
            || config.agents.len() > 8
            || config.persistent_var_max_bytes == 0
            || crate::broker::class(&config.size_class).is_err()
            || crate::web_socket::StreamLease::begin(Duration::from_secs(
                config.ws_authority_lease_seconds,
            ))
            .is_err()
            || !config
                .completion_semantics
                .bytes()
                .all(|byte| byte.is_ascii_digit())
            || config.completion_semantics.is_empty()
            || ![
                &config.image_dir,
                &config.launch_qualification,
                &config.persistent_var,
                &config.bwrap,
                &config.mini_host,
                &config.mini_config,
                &config.mini_operator_socket,
                &config.begin_management_custody,
                &config.claim_management_custody,
                &config.completion_custodian_seed,
                &config.completion_management_custody,
            ]
            .iter()
            .all(|path| path.is_absolute())
        {
            return Err(invalid("resident start config refused"));
        }
        for (index, entry) in config.entrances.iter().enumerate() {
            if !entry.directory.is_absolute()
                || !entry.dispatch_custody.is_absolute()
                || entry.dispatch_custody.parent() != Some(entry.directory.as_path())
                || entry.directory == config.journal_dir
                || entry.display_name.is_empty()
                || entry.display_name.len() > 256
                || entry.preferred_handle.is_empty()
                || entry.preferred_handle.len() > 256
                || config.entrances[..index]
                    .iter()
                    .any(|prior| prior.directory == entry.directory)
            {
                return Err(invalid("resident entrance config refused"));
            }
        }
        for (index, agent) in config.agents.iter().enumerate() {
            if !matches!(
                agent.protocol.as_deref(),
                None | Some("mini-spk-agent-api-v3")
            ) || match agent.protocol.as_deref() {
                None => agent.reverse_timeout_seconds.is_some(),
                Some("mini-spk-agent-api-v3") => !matches!(
                    (agent.reverse_timeout_seconds, agent.controller_worker_wall_seconds),
                    (Some(timeout), Some(wall))
                        if (60..=1740).contains(&timeout)
                            && (120..=1800).contains(&wall)
                            && timeout <= wall - 60
                ),
                _ => true,
            } || (agent.protocol.is_none() && agent.controller_worker_wall_seconds.is_some())
                || !agent.socket.is_absolute()
                || agent.controller_uid == 0
                || agent.controller_uid == config.app_uid
                || !agent.custody.is_absolute()
                || !agent.reverse_socket.is_absolute()
                || agent.attempt_dir.parent() != Some(config.journal_dir.as_path())
                || agent.socket.parent().is_some_and(|parent| {
                    parent.starts_with(&config.journal_dir)
                        || parent.starts_with(&agent.attempt_dir)
                })
                || agent.display_name.is_empty()
                || agent.display_name.len() > 256
                || agent.preferred_handle.is_empty()
                || agent.preferred_handle.len() > 256
                || config
                    .entrances
                    .iter()
                    .any(|entry| agent.socket.starts_with(&entry.directory))
                || config.agents[..index].iter().any(|prior| {
                    prior.socket == agent.socket
                        || prior.controller_uid == agent.controller_uid
                        || prior.custody == agent.custody
                        || prior.reverse_socket == agent.reverse_socket
                        || prior.attempt_dir == agent.attempt_dir
                })
                || agent_socket_parent_overlap(&config.agents[..index], &agent.socket)
            {
                return Err(invalid("resident agent config refused"));
            }
        }
        Ok(config)
    }
}

/// This is the systemd ExecStart body for a fresh native START claim. The
/// stopped unit is installed from operator-reviewed pins; HTTP has no path to
/// choose a package, task UID, Mini signer, command, or app generation.
/// The resident never runs as root. Its unit (rendered by the root broker)
/// names the app UID/GID, grains root and Store; the setid bound is installed
/// before the operator-written config is read, and the config must agree.
struct ResidentBound {
    app_uid: u32,
    app_gid: u32,
    grains_root: PathBuf,
    store: String,
}

impl ResidentBound {
    fn from_unit_environment() -> io::Result<Self> {
        if unsafe { libc::geteuid() } == 0 {
            return Err(invalid(
                "resident refuses root: it runs as the Store operator under mini-spk-broker",
            ));
        }
        let var = |name: &str| {
            std::env::var(name).map_err(|_| invalid("resident unit environment incomplete"))
        };
        let id = |name: &str| -> io::Result<u32> {
            var(name)?
                .parse::<u32>()
                .ok()
                .filter(|value| *value != 0)
                .ok_or_else(|| invalid("resident unit app id refused"))
        };
        Ok(Self {
            app_uid: id("MINI_SPK_APP_UID")?,
            app_gid: id("MINI_SPK_APP_GID")?,
            grains_root: PathBuf::from(var("MINI_SPK_GRAINS_ROOT")?),
            store: var("MINI_SPK_STORE")?,
        })
    }
}

/// A retained directory is a transport route, not a unique Mini selector.
/// Regrant can retain the same origin/session/ticket in a new directory. On
/// START each route still obtains current Mini admission for every request.
fn load_fixed_entrances(
    entries: &[FixedEntranceConfig],
    app_uid: u32,
) -> io::Result<(Vec<FixedAuthoring>, Vec<CustodianPolicy>)> {
    let mut custodies = Vec::with_capacity(entries.len());
    let mut policies = Vec::with_capacity(entries.len());
    for entry in entries {
        open_protected_directory(&entry.directory, app_uid, false)?;
        let custody: FixedAuthoring =
            serde_json::from_slice(&private_file(&entry.dispatch_custody, MAX_CONFIG)?)?;
        custody.validate()?;
        let policy = CustodianPolicy::load(&entry.directory)?;
        if policy.fixed_app != custody.app
            || policy.fixed_subject != custody.subject
            || policy.fixed_session != custody.session
            || policy.fixed_ticket != custody.ticket_resource
            || !matches!(
                (policy.fixed_session_kind, custody.session_kind.as_str()),
                (EntranceKind::Browser, "web") | (EntranceKind::Api, "api")
            )
        {
            return Err(invalid("HTTP transport differs from fixed Mini custody"));
        }
        policies.push(policy);
        custodies.push(custody);
    }
    Ok((custodies, policies))
}

pub fn run(config_path: &Path) -> io::Result<()> {
    let bound = ResidentBound::from_unit_environment()?;
    crate::setid_bound::install(bound.app_uid, bound.app_gid)?;
    let mut config = ResidentConfig::load(config_path)?;
    if config.app_uid != bound.app_uid
        || config.app_gid != bound.app_gid
        || config.grains_root != bound.grains_root
        || config.store != bound.store
    {
        return Err(invalid(
            "resident config differs from the broker-rendered unit's app identity",
        ));
    }
    let journal = Journal::open(&config.journal_dir)?;
    let operator = PrivateOperator {
        host: config.mini_host.clone(),
        config: config.mini_config.clone(),
        socket: config.mini_operator_socket.clone(),
        host_sha256: config.mini_host_sha256.clone(),
        config_sha256: config.mini_config_sha256.clone(),
    };
    if journal.read()?.is_some() {
        return reconcile_prior_start(&config, &operator, &journal);
    }
    Journal::preflight_current_unit(&config.unit)?;
    match std::fs::symlink_metadata(config.journal_dir.join("lifecycle-begin-v3-active.json")) {
        Ok(_) => return Err(invalid("resident launch BEGIN attempt already active")),
        Err(error) if error.kind() == io::ErrorKind::NotFound => {}
        Err(error) => return Err(error),
    }
    // An old one-shot attempt is an uncertainty or recovery record, not a
    // fresh destination. Check every later phase before consuming BEGIN.
    for path in [
        &config.descriptor_attempt_dir,
        &config.begin_attempt_dir,
        &config.claim_author_attempt_dir,
        &config.claim_attempt_dir,
        &config.completion_attempt_dir,
        &config.completion_sign_attempt_dir,
        &config.completion_submit_attempt_dir,
        &config.journal_dir.join("start-admitted-v3.json"),
        &config.journal_dir.join("start-completed-v3.json"),
    ] {
        match std::fs::symlink_metadata(path) {
            Ok(_) => return Err(invalid("resident lifecycle attempt already exists")),
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(error),
        }
    }
    let package = verify_installed_spk(&config.image_dir, config.app_uid)?;
    // The operator Host/config/socket and signer live outside the worker mount
    // and below ancestors the app UID cannot rename or rewrite.
    for path in [
        &config.mini_host,
        &config.mini_config,
        &config.mini_operator_socket,
        &config.completion_custodian_seed,
    ] {
        open_protected_directory(
            path.parent()
                .ok_or_else(|| invalid("operator artifact parent absent"))?,
            config.app_uid,
            false,
        )?;
    }
    if package.raw_sha256 != config.expected_raw_sha256 {
        return Err(invalid("resident signed package pin drift"));
    }
    preflight_custodian(
        &operator,
        &config.completion_custodian_seed,
        &config.completion_semantics,
    )?;
    let signers: FixedLaunchCompletionSigners = serde_json::from_slice(&private_file(
        &config.completion_management_custody,
        MAX_CONFIG,
    )?)?;
    signers.validate(&operator, config.app_uid)?;
    // Read every separately fixed transport/custody pair before consuming the
    // one-shot claim. No HTTP socket is bound until START completion.
    let mut route_bindings = vec![None; config.entrances.len()];
    let (mut custodies, policies) = load_fixed_entrances(&config.entrances, config.app_uid)?;
    let mut agent_preflights = Vec::with_capacity(config.agents.len());
    for agent in &config.agents {
        open_protected_directory(
            agent
                .socket
                .parent()
                .ok_or_else(|| invalid("agent socket parent"))?,
            config.app_uid,
            false,
        )?;
        AgentApiListener::preflight_parent(&agent.socket, agent.controller_uid)?;
        open_protected_directory(
            agent
                .reverse_socket
                .parent()
                .ok_or_else(|| invalid("reverse custody parent"))?,
            config.app_uid,
            false,
        )?;
        let bytes = private_file(&agent.custody, MAX_CONFIG)?;
        let prepared = match agent.protocol.as_deref() {
            None => {
                let custody: AgentCustody = serde_json::from_slice(&bytes)?;
                custody.validate()?;
                let reverse = ReverseCustodyClient::new(
                    agent.reverse_socket.clone(),
                    agent.controller_uid,
                    agent.route_name.clone(),
                )?;
                PreparedAgent::V2(Box::new(custody), reverse)
            }
            Some("mini-spk-agent-api-v3") => {
                let custody: LifetimeCustodyV3 = serde_json::from_slice(&bytes)?;
                custody.validate()?;
                let reverse = ReverseCustodyClient::new(
                    agent.reverse_socket.clone(),
                    agent.controller_uid,
                    agent.route_name.clone(),
                )?;
                PreparedAgent::V3(Box::new(custody), LifetimeReverseClient::new(reverse))
            }
            _ => return Err(invalid("resident agent protocol refused")),
        };
        let (session, ticket, parent, purse) = prepared.coordinates();
        if agent_preflights.iter().any(|prior: &PreparedAgent| {
            let (s, t, p, q) = prior.coordinates();
            s == session || t == ticket || p == parent || q == purse
        }) || custodies
            .iter()
            .any(|human| human.session == session || human.ticket_resource == ticket)
        {
            return Err(invalid("resident agent authority route duplicated"));
        }
        private_dir(&agent.attempt_dir)?;
        agent_preflights.push(prepared);
    }
    let launch = SourceBoundLaunch::author(&operator, &package, &config.descriptor_attempt_dir)?;
    QualifiedLaunch::matches(&config, &launch)?;
    let descriptor = launch.descriptor();
    let bridge = decode_bridge_config(
        package
            .signed_bridge_config
            .as_deref()
            .ok_or_else(|| invalid("signed START bridge absent"))?,
    )
    .map_err(io::Error::other)?;
    if bridge.api_path != descriptor.package.api_path {
        return Err(invalid("signed START bridge differs from Mini descriptor"));
    }
    if (!config.agents.is_empty()
        || policies
            .iter()
            .any(|policy| policy.fixed_session_kind == EntranceKind::Api))
        && descriptor.package.api_path.is_none()
    {
        return Err(invalid("signed package has no configured API interface"));
    }
    let begin_signers: FixedLaunchBeginSigners =
        serde_json::from_slice(&private_file(&config.begin_management_custody, MAX_CONFIG)?)?;
    let claim_signers: FixedLaunchClaimSigners =
        serde_json::from_slice(&private_file(&config.claim_management_custody, MAX_CONFIG)?)?;
    begin_signers.validate(&operator, config.app_uid)?;
    claim_signers.validate(&operator, config.app_uid)?;
    // The volume registration is a root-published physical witness, not a
    // source permit. Preflight it before consuming the one-shot BEGIN, then
    // require its volume ID to equal Mini's exact source projection.
    let volume = read_attested_volume(
        &VolumeSite::new(&config.grains_root, &config.store)?,
        config.volume_resource,
        config.app_uid,
        config.persistent_var_max_bytes,
        &config.deployment_id,
        &config.host_id,
        &config.expected_volume_id,
    )?;
    if volume.mount != config.persistent_var {
        return Err(invalid("START mount differs from root volume registration"));
    }
    volume.recheck_handoff()?;
    let begin = submit_v3_begin(
        &operator,
        &begin_signers,
        config.app_uid,
        &launch,
        config.start_action.native()?,
        &config.begin_operation_ledger,
        &config.begin_attempt_dir,
    )?;
    if begin.volume_id_hex != volume.volume_id {
        return Err(invalid("root volume differs from source BEGIN volume ID"));
    }
    let command = match &begin.action {
        crate::lifecycle_v3_native::LaunchBeginAction::Create(index) => {
            let digest = descriptor
                .create_digests
                .get(*index)
                .ok_or_else(|| invalid("source create digest absent"))?;
            launch.source_selected_create(*index, digest)?
        }
        crate::lifecycle_v3_native::LaunchBeginAction::Continue { .. } => {
            launch.source_selected_continue(&descriptor.continue_digest)?
        }
        crate::lifecycle_v3_native::LaunchBeginAction::Install => {
            return Err(invalid("INSTALL action cannot enter resident START"));
        }
    };
    let generation: u64 = begin
        .process_generation
        .parse()
        .map_err(|_| invalid("source BEGIN process generation is not decimal"))?;
    let spec = SandboxSpec {
        bwrap: config.bwrap.clone(),
        image_root: package.directory.join("root"),
        persistent_var: config.persistent_var.clone(),
        persistent_var_max_bytes: config.persistent_var_max_bytes,
        argv: command.argv.clone(),
        environ: command.environ.clone(),
        // Root-private journal directory, one new file per app generation.
        app_output: config.journal_dir.join(format!(
            "app-output-r{}-g{generation}.log",
            config.volume_resource
        )),
    };
    let prepared =
        PreparedResident::prepare(&spec, config.app_uid, config.app_gid, &config.bwrap_sha256)?;
    let assembled = assemble_v3_claim(
        &operator,
        &claim_signers,
        config.app_uid,
        &begin,
        &launch,
        &config.claim_nonce_ledger,
        &config.claim_author_attempt_dir,
    )?;
    let claim = submit_v3_claim(&operator, assembled, &begin, &launch, &claim_signers)?;
    if claim.physical_begin.unit != config.unit
        || claim.physical_begin.app != config.volume_resource
        || claim.physical_begin.image_identity
            != crate::lifecycle_v3_native::hex(&descriptor.package.image_identity)
    {
        return Err(invalid(
            "source lifecycle unit differs from installed service",
        ));
    }
    if policies
        .iter()
        .any(|policy| policy.fixed_session_kind == EntranceKind::Api)
        && bridge.api_path.is_none()
    {
        return Err(invalid("signed package has no configured API interface"));
    }
    if custodies
        .iter()
        .any(|custody| custody.app != claim.physical_begin.app.to_string())
    {
        return Err(invalid(
            "fixed participant custody differs from claimed shared app",
        ));
    }
    for prepared in &agent_preflights {
        let matches_app = match prepared {
            PreparedAgent::V2(custody, _) => {
                custody.app == claim.physical_begin.app.to_string()
                    && custody.app_generation == claim.physical_begin.generation.to_string()
            }
            PreparedAgent::V3(custody, _) => {
                custody.lineage.app_resource == claim.physical_begin.app.to_string()
            }
        };
        if !matches_app || bridge.api_path.is_none() {
            return Err(invalid("agent custody differs from claimed shared app"));
        }
    }
    let admitted = json!({
        "protocol":"mini-spk-resident-start-admitted-v3",
        "rawSha256":package.raw_sha256,
        "launchRoot":descriptor.root,
        "startAction":config.start_action,
        "beginSha256":format!("{:x}", Sha256::digest(&begin.ingress)),
        "claimIngressSha256":format!("{:x}", Sha256::digest(&claim.claim_ingress)),
        "committedClaimSha256":format!("{:x}", Sha256::digest(&claim.committed)),
        "claimInspectionSha256":format!("{:x}", Sha256::digest(&claim.inspection)),
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
            "priorCreate":begin.prior_create.as_ref().map(|prior| json!({
                "receiptHex":prior.receipt_hex,
                "custodyHex":prior.custody_hex,
            })),
        },
        "claim":{
            "physicalBegin":claim.physical_begin,
            "transactionId":claim.transaction_id,
            "eventId":claim.event_id,
            "acceptedCount":claim.accepted_count,
            "worldRoot":claim.world_root,
        },
    });
    // After this fsync a restarted supervisor can look up only the retained
    // completion ingress. It cannot convert these old bytes into another
    // physical launch or ask Mini for a second fresh claim.
    let admitted_bytes = serde_json::to_vec(&admitted)?;
    write_new(
        &config.journal_dir,
        "start-admitted-v3.json",
        &admitted_bytes,
    )?;
    journal.arm(claim.physical_begin.clone())?;
    journal.request_launch(&claim.physical_begin)?;
    let mut resident = prepared.start(&journal, &claim.physical_begin)?;
    // The RPC driver bounds every call (MAX_CALL_TIME, 30 s); a longer
    // request is refused before it is sent, after the claim is committed.
    let view = resident.rpc.get_view_info(Duration::from_secs(30))?;
    if view != bridge.view_info {
        return Err(invalid(
            "running app ViewInfo differs from signed bridge schema",
        ));
    }
    let report = prepare_v3_running_report(
        &operator,
        ReportInput {
            begin: &begin,
            claim: &claim,
            launch: &launch,
            mode: PhysicalMode::Running {
                journal: &journal,
                volume: &volume,
            },
        },
        &config.completion_custodian_seed,
        &config.completion_semantics,
        &config.completion_attempt_dir,
    )?;
    let completion_ingress = assemble_v3_completion(
        &operator,
        &signers,
        config.app_uid,
        CompletionInput {
            begin: &begin,
            claim: &claim,
            launch: &launch,
            signed_report: &report.signed_report,
        },
        &config.completion_sign_attempt_dir,
    )?;
    let _receipt = submit_v3_completion(
        &operator,
        &completion_ingress,
        &begin,
        &claim,
        &report.signed_report,
        Some(&journal),
    )?;
    let outcome_inspection = private_file(
        &config.completion_sign_attempt_dir.join("op38-outcome.json"),
        MAX_CONFIG,
    )?;
    write_new(
        &config.journal_dir,
        "start-completed-v3.json",
        &serde_json::to_vec(&json!({
            "protocol":"mini-spk-resident-start-completed-v3",
            "admittedSha256":format!("{:x}", Sha256::digest(&admitted_bytes)),
            "evidenceName":"op38-outcome.json",
            "evidenceSha256":format!("{:x}", Sha256::digest(&outcome_inspection)),
            "completionReceipt":{
                "transactionId":_receipt.transaction_id,
                "eventId":_receipt.event_id,
                "acceptedCount":_receipt.accepted_count,
                "worldRoot":_receipt.world_root,
            },
        }))?,
    )?;
    retire_start_markers(&config, &_receipt)?;
    // A START completion is the first state that may expose transport. Native
    // admission remains decisive for every later HTTP request as well.
    let entrances = config
        .entrances
        .iter()
        .map(|entry| PrivateHttpEntrance::bind(&entry.directory))
        .collect::<io::Result<Vec<_>>>()?;
    let api_path = bridge.api_path;
    let mut agent_routes = config
        .agents
        .iter()
        .zip(agent_preflights)
        .map(|(agent, prepared)| {
            AgentApiListener::bind(&agent.socket, agent.controller_uid)
                .map(|listener| (listener, prepared, agent))
        })
        .collect::<io::Result<Vec<_>>>()?;
    // The app's exit ends this generation: the resident exits with an error,
    // the unit fails, and its OnFailure supervisor STOPs this generation and
    // continues a new one. A generation is never relaunched in place.
    let app_exit = {
        let fd =
            unsafe { libc::syscall(libc::SYS_pidfd_open, resident.child_pid() as libc::pid_t, 0) };
        if fd < 0 {
            return Err(io::Error::last_os_error());
        }
        unsafe { <std::os::fd::OwnedFd as std::os::fd::FromRawFd>::from_raw_fd(fd as libc::c_int) }
    };
    let mut route_control = RouteControl::bind(&config.journal_dir)?;
    let mut agent_fds: Vec<_> = agent_routes
        .iter()
        .map(|(listener, _, _)| listener.as_raw_fd())
        .collect();
    let app_exit_index = agent_fds.len();
    agent_fds.push(std::os::fd::AsRawFd::as_raw_fd(&app_exit));
    let route_control_index = agent_fds.len();
    agent_fds.push(route_control.as_raw_fd());
    // One count for the generation: every participant's sockets share the
    // grain's class cap.
    let ws_limits = crate::web_socket::Limits::from(crate::broker::class(&config.size_class)?);
    let ws_open = crate::web_socket::OpenSockets::default();
    let continuity_namespace = operator.continuity_namespace(&config.journal_dir)?;
    PrivateHttpEntrance::serve_dynamic_with_aux(entrances, &agent_fds, |event, entrances| {
        if let Ok((index, request, kind, policy)) = event {
            let entry = &config.entrances[index];
            let mut human = ResidentHuman {
                operator: &operator,
                custody: &custodies[index],
                journal: &journal,
                rpc: &mut resident.rpc,
                display_name: &entry.display_name,
                preferred_handle: &entry.preferred_handle,
                sockets: &ws_open,
                limits: ws_limits,
                stream_lease_lifetime: Duration::from_secs(config.ws_authority_lease_seconds),
                continuity_namespace: &continuity_namespace,
                route_binding: route_bindings[index].as_ref(),
            };
            return deliver_request(
                &mut human,
                request,
                kind,
                policy,
                api_path.as_deref(),
                &config.journal_dir,
            )
            .map(Some);
        }
        let index = match event {
            Err(index) => index,
            Ok(_) => unreachable!("HTTP branch returned above"),
        };
        if index == app_exit_index {
            return Err(invalid("app process exited; this generation ends"));
        }
        if index == route_control_index {
            route_control.poll_once(|request| {
                if entrances.len() >= resident_route_control::MAX_ROUTES {
                    return Err(invalid("resident route limit reached"));
                }
                let (custody, policy) = resident_route_control::prepare(
                    request,
                    &claim.physical_begin.app.to_string(),
                    &claim.physical_begin.generation.to_string(),
                )?;
                if policy.fixed_session_kind == EntranceKind::Api && api_path.is_none() {
                    return Err(invalid("signed package has no configured API interface"));
                }
                open_protected_directory(&request.directory, config.app_uid, false)?;
                if entrances
                    .iter()
                    .any(|prior| prior.occupies_directory(&request.directory))
                    || agent_routes.iter().any(|(_, prior, _)| {
                        let (session, ticket, _, _) = prior.coordinates();
                        session == custody.session || ticket == custody.ticket_resource
                    })
                {
                    return Err(invalid("resident route custody or directory duplicated"));
                }
                let admitted = operator.admit_resident_route(
                    &custody,
                    &request.expected_app_generation,
                    &request.expected_session_generation,
                    &request.registration_nonce_hex,
                    &config.journal_dir,
                )?;
                let binding = admitted.binding();
                if route_bindings
                    .iter()
                    .flatten()
                    .any(|prior| prior == binding)
                {
                    return Err(invalid("resident route source binding duplicated"));
                }
                if binding.app != custody.app
                    || binding.app_generation != request.expected_app_generation
                    || binding.session != custody.session
                    || binding.session_generation != request.expected_session_generation
                    || binding.subject != custody.subject
                    || binding.ticket_resource != custody.ticket_resource
                    || admitted.registration_nonce_hex() != request.registration_nonce_hex
                    || admitted.session_kind() != custody.session_kind
                {
                    return Err(invalid("source route admission differs from fixed custody"));
                }
                let entrance = PrivateHttpEntrance::bind_fixed(&request.directory, policy)?;
                let reply = RouteRegistrationReply {
                    protocol: "mini-spk-route-register-v1".into(),
                    registration_nonce_hex: request.registration_nonce_hex.clone(),
                    route_index: entrances.len(),
                    app: binding.app.clone(),
                    app_generation: binding.app_generation.clone(),
                    session: binding.session.clone(),
                    session_generation: binding.session_generation.clone(),
                    subject: binding.subject.clone(),
                    ticket_resource: binding.ticket_resource.clone(),
                    session_fingerprint_hex: hex_bytes(&binding.session_fingerprint),
                    admitted_height: admitted.tip().height.clone(),
                    admitted_world_root: admitted.tip().world_root.clone(),
                };
                // All fallible work precedes these append-only mutations. Existing
                // custody and lease objects are never replaced or renewed here.
                config.entrances.push(FixedEntranceConfig {
                    directory: request.directory.clone(),
                    dispatch_custody: request.dispatch_custody.clone(),
                    display_name: request.display_name.clone(),
                    preferred_handle: request.preferred_handle.clone(),
                });
                custodies.push(custody);
                route_bindings.push(Some(binding.clone()));
                entrances.push(entrance);
                Ok(reply)
            })?;
            return Ok(None);
        }
        let (listener, prepared, agent) = agent_routes
            .get_mut(index)
            .ok_or_else(|| invalid("resident agent poll index drift"))?;
        let signed_api_path = api_path
            .as_deref()
            .ok_or_else(|| invalid("signed API path absent"))?;
        match prepared {
            PreparedAgent::V2(custody, reverse) => {
                let mut context = ResidentAgent {
                    operator: &operator,
                    custody,
                    journal: &journal,
                    rpc: &mut resident.rpc,
                    reverse_reserve: reverse,
                    signed_api_path,
                    display_name: &agent.display_name,
                    preferred_handle: &agent.preferred_handle,
                    attempt_parent: &agent.attempt_dir,
                };
                listener.poll_once(&mut context)?;
            }
            PreparedAgent::V3(custody, reverse) => {
                let mut context = ResidentLifetimeAgent {
                    operator: &operator,
                    custody,
                    journal: &journal,
                    rpc: &mut resident.rpc,
                    reverse,
                    signed_api_path,
                    display_name: &agent.display_name,
                    preferred_handle: &agent.preferred_handle,
                    attempt_parent: &agent.attempt_dir,
                    reverse_timeout: Duration::from_secs(
                        agent
                            .reverse_timeout_seconds
                            .ok_or_else(|| invalid("lifetime reverse timeout absent"))?,
                    ),
                    controller_worker_wall_seconds: agent
                        .controller_worker_wall_seconds
                        .ok_or_else(|| invalid("lifetime worker wall pin absent"))?,
                };
                agent_api_lifetime_server_v3::poll_once(listener, &mut context)?;
            }
        }
        Ok(None)
    })
}

fn hex_bytes(bytes: &[u8]) -> String {
    use std::fmt::Write as _;
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(out, "{byte:02x}").expect("writing to String");
    }
    out
}

fn deliver_request(
    human: &mut ResidentHuman<'_>,
    mut request: ReceivedRequest,
    kind: EntranceKind,
    policy: &CustodianPolicy,
    api_path: Option<&str>,
    attempt_parent: &Path,
) -> io::Result<Vec<u8>> {
    let upgrade = match (request.websocket.take(), request.upgrade_stream.take()) {
        (None, None) => None,
        (Some(handshake), Some(client)) => Some(UpgradeRequest {
            client,
            accept: handshake.accept,
        }),
        _ => return Err(invalid("WebSocket handshake and stream disagree")),
    };
    let http = project_request(&request, kind, api_path)?;
    human.deliver_once(policy, &http, attempt_parent, upgrade)
}

fn project_request<'a>(
    request: &'a ReceivedRequest,
    kind: EntranceKind,
    api_path: Option<&'a str>,
) -> io::Result<HttpProjection<'a>> {
    // The HTTP parser has already removed exactly one leading slash. Keep
    // that canonical relative form, including the empty API-root path.
    if request.path_and_query.starts_with('/') {
        return Err(invalid("HTTP target is not canonical relative form"));
    }
    let relative = request.path_and_query.as_str();
    let route = match kind {
        EntranceKind::Browser => Route::Browser,
        EntranceKind::Api => Route::Api {
            signed_path: api_path.ok_or_else(|| invalid("signed SPK lacks API interface"))?,
        },
    };
    Ok(HttpProjection {
        method: request.method.as_str(),
        path_and_query: relative,
        ordered_headers: &request.ordinary_headers,
        body: &request.body,
        route,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dispatch_inspection::app_route_path;
    use crate::http_entrance::read_request;
    use serde_json::json;
    use std::fs::{self, DirBuilder};
    use std::io::Write;
    use std::os::unix::fs::DirBuilderExt;
    use std::os::unix::net::UnixStream;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn retained_completion_requires_exact_source_evidence_after_restart() {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "mini-spk-start-evidence-{}-{nonce}",
            std::process::id()
        ));
        DirBuilder::new().mode(0o700).create(&dir).unwrap();
        let evidence = serde_json::to_vec(&json!({
            "type":"confirmed", "confirmation":"installed",
            "transactionId":"7", "eventId":"8", "acceptedCount":"10",
            "worldRoot":"11",
        }))
        .unwrap();
        write_new(&dir, "op38-outcome.json", &evidence).unwrap();
        let mut saved = json!({
            "evidenceName":"op38-outcome.json",
            "evidenceSha256":format!("{:x}", Sha256::digest(&evidence)),
            "completionReceipt":{
                "transactionId":"7", "eventId":"8",
                "acceptedCount":"10", "worldRoot":"11",
            },
        });
        assert_eq!(
            checked_completion_evidence(&dir, &saved, "9")
                .unwrap()
                .accepted_count,
            "10"
        );
        saved["completionReceipt"]["eventId"] = json!("9");
        assert!(checked_completion_evidence(&dir, &saved, "9").is_err());
        saved["completionReceipt"]["eventId"] = json!("8");
        saved["evidenceName"] = json!("../op38-outcome.json");
        assert!(checked_completion_evidence(&dir, &saved, "9").is_err());
        saved["evidenceName"] = json!("op38-outcome.json");
        saved["evidenceSha256"] = json!("0".repeat(64));
        assert!(checked_completion_evidence(&dir, &saved, "9").is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn distinct_agent_uids_need_disjoint_socket_parent_acl_scopes() {
        let first = FixedAgentConfig {
            protocol: None,
            reverse_timeout_seconds: None,
            controller_worker_wall_seconds: None,
            socket: PathBuf::from("/run/mini-spk/agent-a/api.sock"),
            controller_uid: 1001,
            custody: PathBuf::from("/var/lib/mini-spk/a-custody.json"),
            reverse_socket: PathBuf::from("/run/mini-spk/reverse-a.sock"),
            route_name: "a".into(),
            attempt_dir: PathBuf::from("/var/lib/mini-spk/a-attempt"),
            display_name: "A".into(),
            preferred_handle: "a".into(),
        };
        assert!(agent_socket_parent_overlap(
            std::slice::from_ref(&first),
            Path::new("/run/mini-spk/agent-a/other.sock")
        ));
        assert!(agent_socket_parent_overlap(
            std::slice::from_ref(&first),
            Path::new("/run/mini-spk/agent-a/nested/api.sock")
        ));
        assert!(!agent_socket_parent_overlap(
            &[first],
            Path::new("/run/mini-spk/agent-b/api.sock")
        ));
    }

    fn resident_config_fixture() -> (PathBuf, PathBuf, Value) {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let journal =
            std::env::temp_dir().join(format!("mini-spk-config-{}-{unique}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&journal).unwrap();
        let path = journal.join("resident.json");
        let agent = |name: &str, uid: u32| {
            json!({
                "socket": format!("/run/mini-spk/{name}/api.sock"),
                "controllerUid": uid,
                "custody": format!("/var/lib/mini-spk/{name}-custody.json"),
                "reverseSocket": format!("/run/mini-spk/{name}-reverse.sock"),
                "routeName": name,
                "attemptDir": journal.join(format!("{name}-attempt")),
                "displayName": name,
                "preferredHandle": name
            })
        };
        let mut config = json!({
            "protocol": "mini-spk-resident-start-v3",
            "journalDir": journal.clone(),
            "imageDir": "/var/lib/mini-spk/image",
            "expectedRawSha256": "a".repeat(64),
            "persistentVar": "/var/lib/mini-spk/var",
            "persistentVarMaxBytes": 1048576,
            "deploymentId": "e".repeat(64),
            "hostId": "f".repeat(64),
            "grainsRoot": "/var/lib/mini/grains",
            "store": "0123456789abcdef",
            "bwrap": "/usr/bin/bwrap",
            "bwrapSha256": "b".repeat(64),
            "appUid": 1000,
            "appGid": 1000,
            "unit": "mini-spk-a8401-g1.service",
            "miniHost": "/opt/mini/host",
            "miniHostSha256": "c".repeat(64),
            "miniConfig": "/etc/mini/host.json",
            "miniConfigSha256": "d".repeat(64),
            "miniOperatorSocket": "/run/mini/operator.sock",
            "beginManagementCustody": "/etc/mini/begin.json",
            "claimManagementCustody": "/etc/mini/claim.json",
            "beginOperationLedger": journal.join("begin-ledger"),
            "claimNonceLedger": journal.join("claim-ledger"),
            "descriptorAttemptDir": journal.join("descriptor-attempt"),
            "beginAttemptDir": journal.join("begin-attempt"),
            "claimAuthorAttemptDir": journal.join("claim-author-attempt"),
            "claimAttemptDir": journal.join("claim-attempt"),
            "completionAttemptDir": journal.join("completion-attempt"),
            "completionSignAttemptDir": journal.join("completion-sign-attempt"),
            "completionSubmitAttemptDir": journal.join("completion-submit-attempt"),
            "completionCustodianSeed": "/etc/mini/completion.seed",
            "completionManagementCustody": "/etc/mini/completion.json",
            "completionSemantics": "1",
            "entrances": [{
                "directory": "/run/mini-spk/human",
                "dispatchCustody": "/run/mini-spk/human/dispatch.json",
                "displayName": "human",
                "preferredHandle": "human"
            }],
            "agents": [agent("agent-a", 1001), agent("agent-b", 1002)]
        });
        config["sizeClass"] = json!("S");
        config["launchQualification"] =
            json!("/var/lib/mini-spk/launch-qualified/qualification.json");
        config["startAction"] = json!({"kind":"create","index":0});
        config["volumeResource"] = json!(8401);
        config["expectedVolumeId"] = json!("9".repeat(64));
        (journal, path, config)
    }

    #[test]
    fn resident_config_refuses_two_agent_sockets_under_one_acl_parent() {
        let (journal, path, mut config) = resident_config_fixture();
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        file.write_all(&serde_json::to_vec(&config).unwrap())
            .unwrap();
        file.sync_all().unwrap();
        assert_eq!(
            ResidentConfig::load(&path)
                .unwrap()
                .ws_authority_lease_seconds,
            60
        );
        let mut lease_config = config.clone();
        lease_config["wsAuthorityLeaseSeconds"] = json!(300);
        fs::write(&path, serde_json::to_vec(&lease_config).unwrap()).unwrap();
        assert_eq!(
            ResidentConfig::load(&path)
                .unwrap()
                .ws_authority_lease_seconds,
            300
        );
        lease_config["wsAuthorityLeaseSeconds"] = json!(0);
        fs::write(&path, serde_json::to_vec(&lease_config).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_err());
        fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        assert_eq!(fs::read_dir(&journal).unwrap().count(), 1);
        let mut mixed = config.clone();
        mixed["entrances"].as_array_mut().unwrap().push(json!({
            "directory":"/run/mini-spk/human-b",
            "dispatchCustody":"/run/mini-spk/human-b/dispatch.json",
            "displayName":"human-b",
            "preferredHandle":"human-b"
        }));
        for agent in mixed["agents"].as_array_mut().unwrap() {
            agent["protocol"] = json!("mini-spk-agent-api-v3");
            agent["controllerWorkerWallSeconds"] = json!(1500);
            agent["reverseTimeoutSeconds"] = json!(1440);
        }
        fs::write(&path, serde_json::to_vec(&mixed).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_ok());
        mixed["agents"][0]["reverseTimeoutSeconds"] = json!(1441);
        fs::write(&path, serde_json::to_vec(&mixed).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_err());
        config["agents"][1]["socket"] = json!("/run/mini-spk/agent-a/other.sock");
        fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_err());
        config["agents"][1]["socket"] = json!("/run/mini-spk/agent-a/nested/api.sock");
        fs::write(&path, serde_json::to_vec(&config).unwrap()).unwrap();
        assert!(ResidentConfig::load(&path).is_err());
        fs::remove_dir_all(&journal).unwrap();
    }

    #[test]
    fn restart_config_accepts_live_route_limit_and_refuses_one_more() {
        let (journal, path, mut config) = resident_config_fixture();
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(&path)
            .unwrap();
        file.write_all(&serde_json::to_vec(&config).unwrap())
            .unwrap();
        drop(file);
        for count in [
            9,
            resident_route_control::MAX_ROUTES,
            resident_route_control::MAX_ROUTES + 1,
        ] {
            config["entrances"] = Value::Array((0..count).map(|index| json!({
                "directory": format!("/run/mini-spk/retained-route-{index}"),
                "dispatchCustody": format!("/run/mini-spk/retained-route-{index}/dispatch.json"),
                "displayName": "Member".repeat(32), "preferredHandle": format!("member-{index}"),
            })).collect());
            let bytes = serde_json::to_vec(&config).unwrap();
            if count == resident_route_control::MAX_ROUTES {
                assert!(bytes.len() as u64 > MAX_CONFIG);
            }
            fs::write(&path, bytes).unwrap();
            if count <= resident_route_control::MAX_ROUTES {
                assert_eq!(ResidentConfig::load(&path).unwrap().entrances.len(), count);
            } else {
                assert!(ResidentConfig::load(&path).is_err());
            }
        }
        fs::remove_dir_all(&journal).unwrap();
    }

    #[test]
    fn restart_retains_distinct_routes_with_same_origin_session_and_ticket() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = PathBuf::from(std::env::var_os("XDG_RUNTIME_DIR").unwrap())
            .join(format!("restart-routes-{}-{unique}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let mut custody = json!({
            "protocol":"mini-spk-human-dispatch-custody-v1","app":"17","subject":"8","session":"27","sessionKind":"web",
            "issueIndex":"1","ticketResource":"37","packageManifest":"40","snapshotManifest":"41","sessionObserveCapability":"42",
            "manifestObserveCapability":"43","enrollmentObserveCapability":"44","signers":[{"role":"0","index":"0","keyId":"9","keyEpoch":"0","publicKeyHex":"00".repeat(32),"seedPath":root.join("seed")}]
        });
        let entries: Vec<_> = ["old-epoch", "new-epoch"]
            .into_iter()
            .map(|name| {
                let directory = root.join(name);
                crate::http_entrance::initialize_custodian(
                    &directory,
                    "app.example.test",
                    "17",
                    "8",
                    "27",
                    "37",
                    "web",
                )
                .unwrap();
                let dispatch_custody = write_new(
                    &directory,
                    "dispatch.json",
                    &serde_json::to_vec(&custody).unwrap(),
                )
                .unwrap();
                FixedEntranceConfig {
                    directory,
                    dispatch_custody,
                    display_name: name.into(),
                    preferred_handle: name.into(),
                }
            })
            .collect();
        let app_uid = unsafe { libc::geteuid() }.wrapping_add(1000);
        let (custodies, policies) = load_fixed_entrances(&entries, app_uid).unwrap();
        assert_eq!(custodies.len(), 2);
        assert_eq!(policies[0].expected_host, policies[1].expected_host);
        assert_eq!(custodies[0].session, custodies[1].session);
        assert_eq!(custodies[0].ticket_resource, custodies[1].ticket_resource);
        // Allowing duplicate selectors does not relax each route identity check.
        custody["subject"] = json!("9");
        fs::write(
            &entries[1].dispatch_custody,
            serde_json::to_vec(&custody).unwrap(),
        )
        .unwrap();
        assert!(load_fixed_entrances(&entries, app_uid).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn parsed_api_root_and_discovery_keep_one_canonical_prefix() {
        for (target, expected) in [
            ("/", ("repo.git/", "")),
            (
                "/info/refs?service=git-upload-pack",
                ("repo.git/info/refs", "service=git-upload-pack"),
            ),
        ] {
            let (mut writer, mut reader) = UnixStream::pair().unwrap();
            write!(
                writer,
                "GET {target} HTTP/1.1\r\nHost: app.example.test\r\n\r\n"
            )
            .unwrap();
            let request = read_request(&mut reader).unwrap();
            let projected =
                project_request(&request, EntranceKind::Api, Some("/repo.git/")).unwrap();
            assert_eq!(
                app_route_path(&projected).unwrap(),
                (expected.0.to_owned(), expected.1.to_owned())
            );
        }
    }
}
