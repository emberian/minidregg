//! Operator audit of one legacy Mini client profile that returned from custody
//! before retaining a call. This is not a native prepare refusal: that client
//! did not retain the op-255 frame. The operator asserts the reviewed local
//! durability/process model, and the controller checks its exact artifacts,
//! signed held state, and physical worker fence before recording that audit.
use serde::Deserialize;
use serde_json::{json, Value};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::{next_retry_json, sha256_bytes, sha256_file, Authority, Result, Runtime};

const LEGACY_CLIENT_SHA: &str = "128bd81cb5876f2cf0071767b8022b5d961ce94956cfd2d550e7d34fc54e7703";
const LEGACY_CLIENT_SOURCE_SHA: &str =
    "2499411bc00d262f5013bcbced161713a5baa79a332eedfd17523647003ed2a2";
const LEGACY_RUNTIME_SHA: &str = "e17ad58b73b43c611bdb6fa22d5fe42a56f75720889fb0901c81337d11eb763f";
const LEGACY_RUNTIME_SOURCE_SHA: &str =
    "279758c553abf4723fdd6deedda0fb1aff9cfae49d80051ddb77c59b2054a2d5";
const LEGACY_HOST_SHA: &str = "4bb72e1e984de413ee0065d7d229dbe0217bf980b4563ba26dc85ee38ed59c65";
const LEGACY_SOURCE_SHA: &str = "071856b1536050c249491eb1177e03b96d9efd66e0ebb85bb885b8970ac7662e";
const LEGACY_RESERVE_OUTCOME_SHA: &str =
    "cf1b642be9b8bda3a808b719fc4df1f906aae29fa54ea7236ad662c0fb3a43af";
const LEGACY_RESERVE_BOUNDARY: &str =
    "68743037989298246820551563739845355993238042545007743375114387610743556038516";
const LEGACY_ATTEMPT_MANIFEST_SHA: &str =
    "3b29e46b11ba1ea0bb536d27ab4fde41db972f33f8d3bb1bf2a882822d52eb3b";
const LEGACY_CONFIG_SHA: &str = "9ee6274296b27ebd8024fad83100e73bcb1d9ba2ed072f9b43baf7f8e17771f4";
const LEGACY_CHALLENGE_BIN_SHA: &str =
    "d9d0bbdd56ab3efccb83d32713fb76ed35949cec46fa5bd00e12003bd7f90918";
const LEGACY_CHALLENGE_JSON_SHA: &str =
    "ba16cc35a164c457832f2b507e0b77f96f31ab8c43a16da4bfcb0fd5a76f9885";
const LEGACY_SIGNED_OBSERVATION_SHA: &str =
    "d701e3814bf3ce7da50e8fdba3af226fa81ba6e738ae36a4170b037d7e19abdf";

/// Exact values supplied by the journal and fresh signed native tool query.
/// The private audit manifest is independent operator input, never generated
/// from absent files or inferred from the current target root.
pub struct Input<'a> {
    pub audit: &'a Path,
    pub state_dir: &'a Path,
    pub attempt: &'a Path,
    pub source: &'a Path,
    pub mini: &'a Path,
    pub host: &'a Path,
    pub host_config: &'a Path,
    pub host_socket: &'a Path,
    pub parent_task: &'a str,
    pub tool_task: &'a str,
    pub tool_subject: &'a str,
    pub operation_id: u64,
    pub prompt_operation_id: u64,
    pub source_sha256: &'a str,
    pub reserve_attempt: &'a Path,
    pub reserve_boundary: &'a str,
    pub held_reserve: &'a str,
    pub held_before_generation: &'a str,
    pub signed_tool: &'a Value,
    pub signed_tool_query_id: u64,
    /// Exact product of the fresh `mini query` in the runtime, not an
    /// operator-supplied JSON projection.
    pub signed_tool_observation: &'a Path,
    pub custody_returned_uncertain: bool,
    pub no_live_child: bool,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AuditManifest {
    r#type: String,
    operation_id: String,
    prompt_operation_id: String,
    operator_audited_no_dispatch: bool,
    custody_child_exited: bool,
    worker_physical_stop_audited: bool,
    legacy_client_source: PathBuf,
    legacy_runtime_source: PathBuf,
    legacy_runtime_binary: PathBuf,
    source_sha256: String,
    intent_sha256: String,
    attempt_manifest_sha256: String,
    copied_config_sha256: String,
    challenge_bin_sha256: String,
    challenge_json_sha256: String,
    signed_observation_sha256: String,
    reserve_outcome_sha256: String,
}

fn bounded_owned(path: &Path, uid: u32, max: u64) -> Result<Vec<u8>> {
    let named = fs::symlink_metadata(path).map_err(|e| format!("audit file stat: {e}"))?;
    if !named.file_type().is_file()
        || named.uid() != uid
        || named.permissions().mode() & 0o777 != 0o600
        || named.len() == 0
        || named.len() > max
    {
        return Err("audit artifact is not a bounded owned 0600 regular file".into());
    }
    let mut file = File::open(path).map_err(|e| format!("audit file open: {e}"))?;
    let opened = file
        .metadata()
        .map_err(|e| format!("audit file metadata: {e}"))?;
    if (named.dev(), named.ino()) != (opened.dev(), opened.ino()) {
        return Err("audit artifact changed during open".into());
    }
    let mut bytes = Vec::new();
    file.by_ref()
        .take(max + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("audit file read: {e}"))?;
    if bytes.is_empty() || bytes.len() as u64 > max {
        return Err("audit artifact changed or exceeded byte bound".into());
    }
    Ok(bytes)
}

fn pinned(path: &Path, digest: &str) -> Result<()> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("legacy pin stat: {e}"))?;
    if !meta.file_type().is_file() || meta.len() == 0 {
        return Err("legacy pin is not a regular file".into());
    }
    if digest.len() != 64
        || !digest
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        || sha256_file(path)? != digest
    {
        return Err(format!("legacy audit SHA-256 mismatch: {}", path.display()));
    }
    Ok(())
}

fn absent_after_prepare(attempt: &Path) -> Result<()> {
    for name in [
        "plan.bin",
        "plan.json",
        "transaction-signatures.bin",
        "transaction-signatures.json",
        "call.bin",
        "outcome.bin",
        "outcome.json",
        "pre-submit-refusal.frame",
        "pre-submit-refusal.json",
    ] {
        match fs::symlink_metadata(attempt.join(name)) {
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(format!(
                    "legacy attempt contains later-stage or fabricated marker: {name}"
                ))
            }
            Err(e) => return Err(format!("legacy attempt inventory: {e}")),
        }
    }
    for entry in fs::read_dir(attempt).map_err(|e| format!("legacy attempt inventory: {e}"))? {
        let entry = entry.map_err(|e| format!("legacy attempt entry: {e}"))?;
        if entry.file_name().to_string_lossy().starts_with("retry-") {
            return Err("legacy attempt already has a retry artifact".into());
        }
    }
    Ok(())
}

fn stopped_unit(
    state_dir: &Path,
    parent_task: &str,
    prompt_id: u64,
) -> Result<(String, String, String)> {
    if parent_task.is_empty()
        || parent_task.starts_with('0') && parent_task != "0"
        || !parent_task.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("legacy parent task is not canonical decimal".into());
    }
    let unit = format!("mini-grain-t{parent_task}-o{prompt_id}");
    let gate = state_dir.join(format!("{unit}.gate"));
    if String::from_utf8(bounded_owned(&gate, unsafe { libc::geteuid() }, 4096)?)
        .map_err(|e| format!("legacy worker gate: {e}"))?
        .trim()
        != "fenced"
    {
        return Err("legacy worker gate is not fenced".into());
    }
    let output = Command::new("/usr/bin/systemctl")
        .args([
            "--user",
            "show",
            &format!("{unit}.service"),
            "-p",
            "Id",
            "-p",
            "ActiveState",
            "-p",
            "MainPID",
            "-p",
            "ControlGroup",
        ])
        .output()
        .map_err(|e| format!("legacy worker unit audit: {e}"))?;
    if !output.status.success() {
        return Err("legacy worker unit audit did not complete".into());
    }
    let status = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let field = |name: &str| -> Result<&str> {
        status
            .lines()
            .find_map(|line| line.strip_prefix(&format!("{name}=")))
            .ok_or_else(|| format!("legacy worker unit missing {name}"))
    };
    if field("Id")? != format!("{unit}.service")
        || field("ActiveState")? != "inactive"
        || field("MainPID")? != "0"
        || !field("ControlGroup")?.is_empty()
    {
        return Err("legacy worker unit is not inactive with an empty cgroup".into());
    }
    Ok((unit, sha256_file(&gate)?, sha256_bytes(status.as_bytes())?))
}

/// The retired client put the exact attempt path in its `--dir` argument.
/// This procfs inventory is a contemporaneous local observation, not a proof
/// that a different process could never have dispatched a call in the past.
fn no_owned_custody_process(attempt: &Path, uid: u32) -> Result<(usize, String)> {
    let needle = attempt
        .to_str()
        .ok_or("legacy attempt path UTF-8")?
        .as_bytes();
    let mut observed = Vec::new();
    let mut owned = 0usize;
    for entry in fs::read_dir("/proc").map_err(|e| format!("legacy procfs: {e}"))? {
        let entry = entry.map_err(|e| format!("legacy procfs entry: {e}"))?;
        let Some(pid) = entry
            .file_name()
            .to_str()
            .and_then(|s| s.parse::<u32>().ok())
        else {
            continue;
        };
        let path = entry.path();
        let meta = match fs::metadata(&path) {
            Ok(meta) => meta,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(format!("legacy process inventory metadata: {error}")),
        };
        if meta.uid() != uid {
            continue;
        }
        owned += 1;
        let cmdline = match fs::read(path.join("cmdline")) {
            Ok(cmdline) => cmdline,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
            Err(error) => return Err(format!("legacy process inventory command line: {error}")),
        };
        if cmdline.len() > 65_536 {
            return Err("owned process command line exceeds audit bound".into());
        }
        if cmdline.split(|b| *b == 0).any(|arg| arg == needle) {
            return Err(format!(
                "legacy custody attempt still appears in owned process {pid}"
            ));
        }
        observed.push(format!("{pid}:{}", sha256_bytes(&cmdline)?));
    }
    observed.sort();
    Ok((owned, sha256_bytes(observed.join("\n").as_bytes())?))
}

/// Checks the narrow legacy profile and returns a journal-ready statement of
/// *operator-audited no dispatch*. It never calls Mini submit, changes state,
/// or describes the missing original prepare reply as a native refusal.
pub fn inspect(input: &Input<'_>) -> Result<Value> {
    let uid = unsafe { libc::geteuid() };
    if input.audit != input.state_dir.join("legacy-b44-audit.json")
        || input.attempt
            != input
                .state_dir
                .join(format!("attempt-{:016}", input.operation_id))
        || input.source
            != input
                .state_dir
                .join(format!("source-{:016}.json", input.operation_id))
        || !input.custody_returned_uncertain
        || !input.no_live_child
        || input.operation_id != 44
        || input.prompt_operation_id != 36
        || input.parent_task != "7803"
        || input.tool_task != "7804"
        || input.tool_subject != "10"
        || input.source_sha256 != LEGACY_SOURCE_SHA
        || input.reserve_attempt != input.state_dir.join("attempt-0000000000000042")
        || input.reserve_boundary != LEGACY_RESERVE_BOUNDARY
        || input.held_reserve != "2"
        || input.held_before_generation != "3"
    {
        return Err("legacy audit does not match a returned exact pending attempt".into());
    }
    let audit_bytes = bounded_owned(input.audit, uid, 65_536)?;
    let audit: AuditManifest =
        serde_json::from_slice(&audit_bytes).map_err(|e| format!("legacy audit manifest: {e}"))?;
    if audit.r#type != "minidregg-legacy-custody-no-dispatch-audit-v1"
        || audit.operation_id != input.operation_id.to_string()
        || audit.prompt_operation_id != input.prompt_operation_id.to_string()
        || !audit.operator_audited_no_dispatch
        || !audit.custody_child_exited
        || !audit.worker_physical_stop_audited
        || audit.source_sha256 != input.source_sha256
        || audit.reserve_outcome_sha256 != LEGACY_RESERVE_OUTCOME_SHA
        || audit.attempt_manifest_sha256 != LEGACY_ATTEMPT_MANIFEST_SHA
        || audit.copied_config_sha256 != LEGACY_CONFIG_SHA
        || audit.challenge_bin_sha256 != LEGACY_CHALLENGE_BIN_SHA
        || audit.challenge_json_sha256 != LEGACY_CHALLENGE_JSON_SHA
        || audit.signed_observation_sha256 != LEGACY_SIGNED_OBSERVATION_SHA
    {
        return Err("legacy audit operator assertion or operation identity differs".into());
    }
    pinned(input.mini, LEGACY_CLIENT_SHA)?;
    pinned(&audit.legacy_client_source, LEGACY_CLIENT_SOURCE_SHA)?;
    pinned(&audit.legacy_runtime_binary, LEGACY_RUNTIME_SHA)?;
    pinned(&audit.legacy_runtime_source, LEGACY_RUNTIME_SOURCE_SHA)?;
    pinned(input.host, LEGACY_HOST_SHA)?;
    pinned(input.source, &audit.source_sha256)?;
    pinned(&input.attempt.join("intent.json"), &audit.intent_sha256)?;
    if audit.source_sha256 != audit.intent_sha256 {
        return Err("legacy copied intent differs from journaled source".into());
    }
    pinned(
        &input.attempt.join("attempt.json"),
        &audit.attempt_manifest_sha256,
    )?;
    pinned(
        &input.attempt.join("config.json"),
        &audit.copied_config_sha256,
    )?;
    pinned(input.host_config, &audit.copied_config_sha256)?;
    pinned(
        &input.attempt.join("challenge.bin"),
        &audit.challenge_bin_sha256,
    )?;
    pinned(
        &input.attempt.join("challenge.json"),
        &audit.challenge_json_sha256,
    )?;
    pinned(
        &input.attempt.join("signed-observation.bin"),
        &audit.signed_observation_sha256,
    )?;
    let manifest: Value = serde_json::from_slice(&bounded_owned(
        &input.attempt.join("attempt.json"),
        uid,
        65_536,
    )?)
    .map_err(|e| format!("legacy attempt manifest: {e}"))?;
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["host"].as_str() != input.host.to_str()
        || manifest["config"].as_str() != input.attempt.join("config.json").to_str()
        || manifest["socket"].as_str() != input.host_socket.to_str()
    {
        return Err("legacy attempt manifest differs from the selected Host/socket".into());
    }
    let source: Value = serde_json::from_slice(&bounded_owned(input.source, uid, 65_536)?)
        .map_err(|e| format!("legacy source: {e}"))?;
    let grain = &source["grain"];
    let observed = &input.signed_tool["grain"];
    let signed_path = input.signed_tool_observation;
    if signed_path
        != input.state_dir.join(format!(
            "query-{:016}/attempt/signed-observation.bin",
            input.signed_tool_query_id
        ))
    {
        return Err("fresh signed tool observation is outside a runtime query attempt".into());
    }
    bounded_owned(signed_path, uid, 12_102_760)?;
    let operation_id = input.operation_id.to_string();
    if grain["task"] != input.tool_task
        || grain["subject"] != input.tool_subject
        || grain["context"]["operationId"].as_str() != Some(operation_id.as_str())
        || grain["operation"]["type"] != "settle"
        || grain["before"]["generation"] != observed["generation"]
        || grain["before"]["status"] != observed["status"]
        || grain["before"]["remaining"] != observed["remaining"]
        || grain["before"]["reserved"] != observed["reserved"]
        || grain["before"]["generation"] != input.held_before_generation
        || grain["before"]["reserved"] != input.held_reserve
        || grain["expectedTargetRoot"] != input.signed_tool["targetRoot"]
        || observed["status"] != "3"
        || source["grants"].as_array().is_none_or(Vec::is_empty)
        || grain["publications"].as_array().is_none_or(Vec::is_empty)
    {
        return Err("legacy pending source differs from signed reserved tool state".into());
    }
    let challenge: Value = serde_json::from_slice(&bounded_owned(
        &input.attempt.join("challenge.json"),
        uid,
        65_536,
    )?)
    .map_err(|e| format!("legacy challenge: {e}"))?;
    if challenge["intent"]["subject"] != input.tool_subject
        || challenge["intent"]["nonce"].as_str() != Some(operation_id.as_str())
        || challenge["intent"]["purpose"]["type"] != "prepare"
        || challenge["intent"]["grants"] != source["grants"]
        || challenge["worldRoot"] != input.reserve_boundary
    {
        return Err("legacy signed prepare challenge differs from pending source/origin".into());
    }
    let reserve_outcome = input.reserve_attempt.join("outcome.json");
    pinned(&reserve_outcome, &audit.reserve_outcome_sha256)?;
    let reserve: Value = serde_json::from_slice(&bounded_owned(&reserve_outcome, uid, 65_536)?)
        .map_err(|e| format!("legacy reserve receipt: {e}"))?;
    if reserve["type"] != "confirmed" || reserve["worldRoot"] != input.reserve_boundary {
        return Err("legacy reserve origin is not the confirmed exact attempt".into());
    }
    absent_after_prepare(input.attempt)?;
    let (unit, gate_sha, unit_observation_sha) = stopped_unit(
        input.state_dir,
        input.parent_task,
        input.prompt_operation_id,
    )?;
    let (owned_processes, proc_observation_sha) = no_owned_custody_process(input.attempt, uid)?;
    Ok(json!({
        "action":"operator-audited-legacy-no-dispatch",
        "stage":"validated-before-pending-clear",
        "nativePrepareRefusalProven":false,
        "operatorAudited":true,
        "operationId":input.operation_id.to_string(),
        "promptOperationId":input.prompt_operation_id.to_string(),
        "attempt":input.attempt,
        "auditManifestSha256":sha256_file(input.audit)?,
        "sourceSha256":audit.source_sha256,
        "attemptManifestSha256":audit.attempt_manifest_sha256,
        "signedObservationSha256":audit.signed_observation_sha256,
        "challengeBinSha256":audit.challenge_bin_sha256,
        "challengeJsonSha256":audit.challenge_json_sha256,
        "freshSignedToolObservationSha256":sha256_file(signed_path)?,
        "signedToolTargetRoot":input.signed_tool["targetRoot"],
        "signedToolGeneration":observed["generation"],
        "signedToolReserved":observed["reserved"],
        "reserveOutcomeSha256":audit.reserve_outcome_sha256,
        "workerUnit":unit,
        "workerGateFenced":true,
        "workerGateSha256":gate_sha,
        "unitObservationSha256":unit_observation_sha,
        "ownedProcessCount":owned_processes,
        "ownedProcessObservationSha256":proc_observation_sha,
        "custodyChildExit":"operator-audited old Command::output return"
    }))
}

const EXTERNAL_NOTE: &str =
    "tool legacy B44 operator no-dispatch audit awaits signed zero-charge settlement";

fn audit_record(rt: &Runtime, stage: &str) -> Option<Value> {
    rt.journal
        .reconciliation_log
        .iter()
        .rev()
        .find(|record| {
            record["action"] == "operator-audited-legacy-no-dispatch"
                && record["operationId"] == "44"
                && record["stage"] == stage
        })
        .cloned()
}

pub(super) fn zero_phase_active(rt: &Runtime) -> bool {
    audit_record(rt, "pending-cleared").is_some()
        && audit_record(rt, "zero-settlement-confirmed").is_none()
}

/// Admin-only first phase. A crash after the first save leaves the original
/// pending attempt intact; a retry rechecks the current signed state before
/// it may clear that exact pending entry.
pub(super) fn audit_b44(rt: &mut Runtime) -> Result<()> {
    if rt.journal.tool_pending.is_none() {
        return if audit_record(rt, "pending-cleared").is_some() {
            Ok(())
        } else {
            Err("B44 has no pending attempt or durable audit".into())
        };
    }
    let pending = rt
        .journal
        .tool_pending
        .clone()
        .ok_or("B44 pending absent")?;
    let publication = pending
        .publication
        .as_ref()
        .ok_or("B44 publication origin absent")?;
    if pending.operation_id != 44
        || pending.operation != "tool settle"
        || !pending.uncertain
        || publication.prompt_operation_id != 36
        || publication.source_sha256 != LEGACY_SOURCE_SHA
        || publication.targets != ["8001"]
        || rt.journal.pending.is_some()
        || rt.journal.provider_pending.is_some()
        || rt.journal.parent_hold.is_some()
        || rt.journal.provider_hold.is_some()
    {
        return Err("B44 durable journal origin differs from reviewed attempt".into());
    }
    let hold = rt
        .journal
        .tool_hold
        .clone()
        .ok_or("B44 held allowance absent")?;
    let reserve_attempt = hold
        .reserve_attempt
        .as_ref()
        .ok_or("B44 reserve attempt absent")?;
    let reserve_boundary = hold
        .reserve_boundary
        .as_deref()
        .ok_or("B44 reserve boundary absent")?;
    if !hold.reserve_confirmed || hold.reserve_refused || hold.charge != "1" {
        return Err("B44 confirmed reservation origin differs".into());
    }
    let tool = rt.tool()?;
    let query_id = rt.journal.next_operation_id;
    let signed_tool = rt.query_as(&tool)?;
    let audit = rt.config.state_dir.join("legacy-b44-audit.json");
    let source = rt.config.state_dir.join("source-0000000000000044.json");
    let signed_observation = rt.config.state_dir.join(format!(
        "query-{query_id:016}/attempt/signed-observation.bin"
    ));
    let record = inspect(&Input {
        audit: &audit,
        state_dir: &rt.config.state_dir,
        attempt: &pending.attempt,
        source: &source,
        mini: &rt.config.mini,
        host: &rt.config.host,
        host_config: &rt.config.host_config,
        host_socket: rt
            .config
            .host_socket
            .as_deref()
            .ok_or("B44 requires pinned host socket")?,
        parent_task: &rt.config.task,
        tool_task: &tool.task,
        tool_subject: &tool.subject,
        operation_id: pending.operation_id,
        prompt_operation_id: publication.prompt_operation_id,
        source_sha256: &publication.source_sha256,
        reserve_attempt,
        reserve_boundary,
        held_reserve: &hold.reserve,
        held_before_generation: &hold.before_generation,
        signed_tool: &signed_tool,
        signed_tool_query_id: query_id,
        signed_tool_observation: &signed_observation,
        custody_returned_uncertain: pending.uncertain,
        no_live_child: rt.child.is_none() && rt.journal.child.is_none(),
    })?;
    let audit_sha = record["auditManifestSha256"]
        .as_str()
        .ok_or("B44 validated audit digest absent")?
        .to_owned();
    let previously_validated = audit_record(rt, "validated-before-pending-clear");
    if let Some(prior) = &previously_validated {
        if prior["auditManifestSha256"] != record["auditManifestSha256"] {
            return Err("B44 audit manifest changed after durable validation".into());
        }
    } else {
        rt.journal.reconciliation_log.push(record.clone());
        rt.save()?;
    }
    // Revalidation is retained separately if the first validation survived a
    // crash, so the later pending clear still has a fresh physical observation.
    if previously_validated.is_some() {
        let mut rechecked = record;
        rechecked["stage"] = json!("revalidated-before-pending-clear");
        rt.journal.reconciliation_log.push(rechecked);
        rt.save()?;
    }
    if rt
        .journal
        .tool_pending
        .as_ref()
        .is_none_or(|current| current.operation_id != 44 || current.attempt != pending.attempt)
    {
        return Err("B44 pending changed before audited clear".into());
    }
    rt.journal.tool_pending = None;
    if !rt
        .journal
        .unresolved_external
        .iter()
        .any(|note| note == EXTERNAL_NOTE)
    {
        rt.journal.unresolved_external.push(EXTERNAL_NOTE.into());
    }
    rt.journal.reconciliation_log.push(json!({
        "action":"operator-audited-legacy-no-dispatch",
        "stage":"pending-cleared",
        "operationId":"44",
        "auditManifestSha256":audit_sha,
        "heldAllowanceReleased":false,
        "nativePrepareRefusalProven":false
    }));
    rt.save()
}

fn exact_zero_lookup(rt: &mut Runtime, tool: &Authority, settlement_id: u64) -> Result<Value> {
    let attempt = rt
        .config
        .state_dir
        .join(format!("attempt-{settlement_id:016}"));
    let source_path = rt
        .config
        .state_dir
        .join(format!("source-{settlement_id:016}.json"));
    let source: Value = serde_json::from_slice(&bounded_owned(
        &source_path,
        unsafe { libc::geteuid() },
        65_536,
    )?)
    .map_err(|e| format!("B44 zero source: {e}"))?;
    if source["grain"]["task"] != tool.task
        || source["grain"]["subject"] != tool.subject
        || source["grain"]["operation"] != json!({"type":"settle","charge":"0"})
        || source["grain"]["before"]["generation"] != "4"
        || source["grain"]["before"]["status"] != "5"
        || source["grain"]["before"]["reserved"] != "2"
        || source["grain"]["publications"] != json!([])
    {
        return Err("B44 zero-charge source differs from held signed settlement".into());
    }
    if !attempt.join("call.bin").is_file() {
        return Err("B44 zero-charge call is not retained".into());
    }
    let original: Value = serde_json::from_slice(&bounded_owned(
        &attempt.join("outcome.json"),
        unsafe { libc::geteuid() },
        65_536,
    )?)
    .map_err(|e| format!("B44 zero outcome: {e}"))?;
    if original["type"] != "confirmed" {
        return Err("B44 zero outcome was not confirmed".into());
    }
    let retry = next_retry_json(&attempt)?;
    let mut args = vec![
        "retry",
        "--attempt",
        attempt.to_str().ok_or("B44 attempt UTF-8")?,
        "--mode",
        "lookup",
    ];
    if let Some(socket) = &rt.config.host_socket {
        args.extend(["--socket", socket.to_str().ok_or("B44 socket UTF-8")?]);
    }
    rt.command_output(&rt.config.mini, &args)?;
    let replayed: Value =
        serde_json::from_slice(&bounded_owned(&retry, unsafe { libc::geteuid() }, 65_536)?)
            .map_err(|e| format!("B44 zero lookup: {e}"))?;
    for field in [
        "type",
        "transactionId",
        "eventId",
        "acceptedCount",
        "worldRoot",
    ] {
        if replayed[field] != original[field] {
            return Err(format!("B44 zero exact lookup differs: {field}"));
        }
    }
    let observed = rt.query_as(tool)?;
    if observed["grain"]["generation"] != "4"
        || observed["grain"]["status"] != "0"
        || observed["grain"]["reserved"] != "0"
    {
        return Err("B44 zero settlement did not produce signed paused grain".into());
    }
    Ok(json!({"operationId":settlement_id.to_string(),
        "sourceSha256":sha256_file(&source_path)?,
        "callSha256":sha256_file(&attempt.join("call.bin"))?,
        "outcomeSha256":sha256_file(&attempt.join("outcome.json"))?,
        "lookupSha256":sha256_file(&retry)?,
        "transactionId":original["transactionId"],
        "eventId":original["eventId"],
        "acceptedCount":original["acceptedCount"],
        "worldRoot":original["worldRoot"]}))
}

/// Admin-only second phase. A requested settlement records its predicted
/// attempt ID before transition_as; that transition persists its own pending
/// call before invoking Mini. After a crash, exact lookup resolves that call.
pub(super) fn settle_b44_zero(rt: &mut Runtime) -> Result<()> {
    if audit_record(rt, "pending-cleared").is_none() {
        return Err("B44 audit and pending clear are not durable".into());
    }
    if rt.child.is_some()
        || rt.journal.child.is_some()
        || rt.journal.pending.is_some()
        || rt.journal.tool_pending.is_some()
        || rt.journal.provider_pending.is_some()
    {
        return Err("B44 zero settlement needs stopped worker and resolved exact attempts".into());
    }
    let tool = rt.tool()?;
    if rt.journal.tool_hold.is_none() {
        if audit_record(rt, "zero-settlement-confirmed").is_some() {
            return Ok(());
        }
        let request = audit_record(rt, "zero-settlement-requested")
            .ok_or("B44 hold disappeared without a requested zero settlement")?;
        let id = request["settlementOperationId"]
            .as_str()
            .ok_or("B44 zero settlement ID absent")?
            .parse::<u64>()
            .map_err(|_| "B44 zero settlement ID invalid")?;
        let receipt = exact_zero_lookup(rt, &tool, id)?;
        rt.journal
            .reconciliation_log
            .push(json!({"action":"operator-audited-legacy-no-dispatch",
            "stage":"zero-settlement-confirmed", "operationId":"44", "receipt":receipt}));
        rt.journal
            .unresolved_external
            .retain(|note| note != EXTERNAL_NOTE);
        return rt.save();
    }
    let hold = rt.journal.tool_hold.clone().ok_or("B44 hold absent")?;
    if !hold.reserve_confirmed
        || hold.reserve_refused
        || hold.reserve != "2"
        || hold.charge != "1"
        || hold.before_generation != "3"
        || hold.reserve_boundary.as_deref() != Some(LEGACY_RESERVE_BOUNDARY)
        || hold.reserve_attempt.as_deref()
            != Some(
                rt.config
                    .state_dir
                    .join("attempt-0000000000000042")
                    .as_path(),
            )
    {
        return Err("B44 hold differs from audited exact reserve".into());
    }
    let observed = rt.query_as(&tool)?;
    let status = observed["grain"]["status"]
        .as_str()
        .ok_or("B44 signed status absent")?;
    if observed["grain"]["reserved"] != "2" {
        return Err("B44 signed reserve differs before zero settlement".into());
    }
    if status == "3" && observed["grain"]["generation"] == "3" {
        rt.transition_as(
            &tool,
            json!({"type":"disconnect"}),
            "reconcile fence",
            "operator fenced B44 legacy tool",
            vec![],
        )?;
    } else if status != "5" || observed["grain"]["generation"] != "4" {
        return Err("B44 signed tool is not at reviewed active or fenced generation".into());
    }
    let fenced = rt.query_as(&tool)?;
    if fenced["grain"]["status"] != "5"
        || fenced["grain"]["generation"] != "4"
        || fenced["grain"]["reserved"] != "2"
    {
        return Err("B44 signed tool fence is not held at generation 4".into());
    }
    let query_id = rt.journal.next_operation_id;
    let settle_id = query_id
        .checked_add(1)
        .ok_or("B44 operation IDs exhausted")?;
    rt.journal
        .reconciliation_log
        .push(json!({"action":"operator-audited-legacy-no-dispatch",
        "stage":"zero-settlement-requested", "operationId":"44",
        "settlementOperationId":settle_id.to_string(),
        "signedFencedTargetRoot":fenced["targetRoot"]}));
    rt.save()?;
    rt.transition_as(
        &tool,
        json!({"type":"settle","charge":"0"}),
        "reconcile settle",
        "operator-audited B44 zero-charge settlement",
        vec![],
    )?;
    let receipt = exact_zero_lookup(rt, &tool, settle_id)?;
    rt.journal
        .reconciliation_log
        .push(json!({"action":"operator-audited-legacy-no-dispatch",
        "stage":"zero-settlement-confirmed", "operationId":"44", "receipt":receipt}));
    rt.journal
        .unresolved_external
        .retain(|note| note != EXTERNAL_NOTE);
    rt.save()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn no_call_inventory_rejects_later_stage_and_fabricated_marker() {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir =
            std::env::temp_dir().join(format!("mini-legacy-audit-{}-{unique}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        assert!(absent_after_prepare(&dir).is_ok());
        fs::write(dir.join("call.bin"), b"call").unwrap();
        assert!(absent_after_prepare(&dir).is_err());
        fs::remove_file(dir.join("call.bin")).unwrap();
        fs::write(dir.join("pre-submit-refusal.json"), b"{}").unwrap();
        assert!(absent_after_prepare(&dir).is_err());
        fs::remove_dir_all(dir).unwrap();
    }
}
