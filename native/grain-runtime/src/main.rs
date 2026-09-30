//! Physical controller for one Mini agent-grain task. Semantic admission is
//! exclusively a signed call to the native Lean host through `mini`.
mod application_api_tools;
mod application_tools;
#[cfg(test)]
mod birth_lifecycle_tests;
mod control;
mod custody_gate;
mod dispatch_custody;
#[cfg(test)]
mod dispatch_runtime_tests;
mod gitweb_worker;
mod legacy_custody_audit;
mod mcp;
mod provider;
mod provider_profile;
#[cfg(test)]
mod publication_refusal_tests;
mod resource_tools;
mod shared_app_refs;
mod terminal;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitCode, Stdio};
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicU8, Ordering};
use std::sync::mpsc::{self, Receiver};
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Config {
    mini: PathBuf,
    host: PathBuf,
    host_config: PathBuf,
    #[serde(default)]
    host_socket: Option<PathBuf>,
    control_socket: PathBuf,
    custody_key: PathBuf,
    state_dir: PathBuf,
    cwd: PathBuf,
    task: String,
    subject: String,
    capability: String,
    query_capability: String,
    #[serde(default)]
    policy_control_capability: Option<String>,
    #[serde(default)]
    tool_task: Option<ToolTask>,
    /// Parent allowance for one model-free foreground tool invocation.
    /// The delegated tool task remains separately reserved and charged.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    foreground_tool: Option<ForegroundToolProfile>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    dispatch_task: Option<DispatchTask>,
    #[serde(default)]
    provider_task: Option<ProviderTask>,
    /// A command must be selected by its configured name. Its arguments are
    /// fixed by the operator, so a remote connection cannot inject paths or
    /// gain a new executable through this interface.
    commands: Vec<AllowedCommand>,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ToolTask {
    task: String,
    subject: String,
    capability: String,
    query_capability: String,
    custody_key: PathBuf,
    parent_capability: String,
    parent_observe_capability: String,
    reserve: String,
    charge: String,
    allowed_publications: Vec<PublicationGrant>,
    #[serde(default)]
    allowed_reads: Vec<resource_tools::AllowedResourceRead>,
    /// Controller-private workspace initialized for this tool's subject and
    /// custody key. Its named references are hints; Mini admits each use.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    resource_workspace: Option<PathBuf>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_birth_families: Vec<resource_tools::AllowedBirthFamily>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_application_families: Vec<application_tools::ApplicationFamily>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_session_families: Vec<application_tools::SessionFamily>,
    /// Operator-pinned foreign applications are names and evidence pointers,
    /// never locally born resources or imported owner grants.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    registered_shared_applications: Vec<shared_app_refs::SharedApplicationRef>,
    /// Fixed resident app-API endpoints. A route is a selector and transport
    /// pin; the event21 native permit remains mandatory for every dispatch.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_application_api_routes: Vec<application_api_tools::RoutePin>,
    /// Event26 routes carry immutable event22/event27 receipt identity.
    /// Current execution generations come from each source-inspected plan.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_application_lifetime_routes: Vec<application_api_tools::LifetimeRoutePin>,
    /// Only an explicitly certified Mini Host with the agent event21 route
    /// may enable the forward API tool. The SPK host still obtains and checks
    /// a fresh event21 permit for each request.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    agent_api_host_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    lifetime_api_host_sha256: Option<String>,
    /// Explicit operator enablement for the qualified current-author Host
    /// image. The family allowlists alone never enable op30/31 delivery.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    current_birth_host_sha256: Option<String>,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ForegroundToolProfile {
    reserve: String,
    charge: String,
}

/// A separate AgentGrain purse for app API attempts by this fixed agent
/// custodian. It must not share the MCP tool task or parent prompt allowance.
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DispatchTask {
    task: String,
    subject: String,
    capability: String,
    query_capability: String,
    custody_key: PathBuf,
    parent_capability: String,
    parent_observe_capability: String,
    reserve: String,
    charge: String,
    socket_path: PathBuf,
    host_uid: u32,
    /// Controller-private Mini operator socket for source-owned v2 reserve
    /// planning/assembly. The ordinary hostSocket remains public receipt IO.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    operator_socket: Option<PathBuf>,
    /// Pinned enrolled identity for the controller's private purse signer.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    reserve_signer: Option<DispatchSignerPin>,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DispatchSignerPin {
    role: String,
    index: String,
    public_key: String,
    key_id: String,
    key_epoch: String,
}

/// A one-target observed `NativeHost.prepareLoaded (.invoke ...)` has the
/// target, observation, and authority signing incidences in this order. They
/// all use the controller's pinned payer identity; the resident never gets
/// that key. V2's separate signing profile is unaffected.
fn lifetime_purse_signers(
    slots: &[Value],
    signer: &DispatchSignerPin,
    key_path: &Path,
) -> Result<Vec<Value>> {
    if !matches!(signer.role.as_str(), "4" | "8" | "1") || signer.index != "0" || slots.len() != 3 {
        return Err("lifetime purse requires exact target/observe/authority slots".into());
    }
    let mut approved = Vec::with_capacity(3);
    for (slot, role) in slots.iter().zip(["4", "8", "1"]) {
        let signing = slot
            .get("signing")
            .ok_or("lifetime purse signing header absent")?;
        if slot.get("role").and_then(Value::as_str) != Some(role)
            || slot.get("index").and_then(Value::as_str) != Some("0")
            || signing.get("decoded").and_then(Value::as_bool) != Some(true)
            || signing.get("keyId").and_then(Value::as_str) != Some(signer.key_id.as_str())
            || signing.get("keyEpoch").and_then(Value::as_str) != Some(signer.key_epoch.as_str())
            || signing.get("algorithm").and_then(Value::as_str) != Some("1")
        {
            return Err("lifetime purse slot differs from pinned enrolled signer".into());
        }
        let header = dispatch_custody::decode_hex(
            slot.get("headerHex")
                .and_then(Value::as_str)
                .ok_or("lifetime purse header hex absent")?,
        )?;
        approved.push(json!({"role":role,"index":"0",
            "keyId":signer.key_id,"keyEpoch":signer.key_epoch,
            "publicKey":signer.public_key,"headerSha256":sha256_bytes(&header)?,
            "keyPath":key_path}));
    }
    Ok(approved)
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProviderTask {
    task: String,
    subject: String,
    capability: String,
    query_capability: String,
    custody_key: PathBuf,
    parent_capability: String,
    parent_observe_capability: String,
    reserve: String,
    charge: String,
    /// Opt into source-owned, reported-usage settlement. The legacy fixed
    /// charge remains available only when this is absent or false.
    #[serde(default)]
    metering: bool,
    /// External provider/model accounting ceilings. They are an operator
    /// contract, not inferred from request byte length.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    max_input_tokens: Option<u32>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    max_output_tokens: Option<u32>,
    model: String,
    upstream_url: String,
    provider_key_file: PathBuf,
    gateway_bind: String,
    max_request_bytes: usize,
    max_response_bytes: usize,
    timeout_seconds: u64,
    /// Limit Hermes iterations for this provider-backed prompt; omitted keeps
    /// the established six-iteration profile.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    max_iterations: Option<u8>,
    /// Only deterministic local upstream fixtures may retain the older host
    /// network route. Real HTTPS provider prompts use a private Unix gateway.
    #[serde(default)]
    local_fixture_host_network: bool,
}

fn provider_max_iterations(configured: Option<u8>) -> Result<u8> {
    let iterations = configured.unwrap_or(6);
    if !(1..=6).contains(&iterations) {
        return Err("providerTask maxIterations must be between 1 and 6".into());
    }
    Ok(iterations)
}

fn select_provider_metering<'a>(profile: &'a Value, task: &str) -> Result<&'a Value> {
    if let Some(services) = profile.get("providerMeterings") {
        if profile.get("providerMetering").is_some() {
            return Err("Host profile mixes singular and multi-provider tariffs".into());
        }
        let services = services
            .as_array()
            .filter(|services| !services.is_empty() && services.len() <= 8)
            .ok_or("Host provider metering list is not bounded")?;
        let mut ids = std::collections::HashSet::new();
        for service in services {
            let id = service
                .get("providerResourceId")
                .and_then(Value::as_str)
                .ok_or("Host provider metering resource ID absent")?;
            decimal(id, "providerResourceId")?;
            if id == "0" || !ids.insert(id) {
                return Err("Host profile repeats or zeroes a provider metering ID".into());
            }
        }
        services
            .iter()
            .find(|service| service.get("providerResourceId").and_then(Value::as_str) == Some(task))
            .ok_or("pinned Host profile has no tariff for configured provider task".into())
    } else {
        profile
            .get("providerMetering")
            .ok_or("pinned Host profile has no provider metering tariff".into())
    }
}

fn provider_required_network(task: &ProviderTask) -> Result<&'static str> {
    if !task.local_fixture_host_network {
        return Ok("none");
    }
    if task.upstream_url.starts_with("http://127.0.0.1:")
        || task.upstream_url.starts_with("http://[::1]:")
    {
        Ok("host")
    } else {
        Err("localFixtureHostNetwork requires a loopback HTTP upstream".into())
    }
}

fn provider_command_route(command: &AllowedCommand, required_network: &str) -> bool {
    command.systemd_scope
        && command.wall_time_seconds.unwrap_or(600) >= 120
        && command.args.first().is_some_and(|arg| arg == "--workspace")
        && command
            .args
            .get(2)
            .is_some_and(|arg| arg == "--runtime-root")
        && command.args.get(4).is_some_and(|arg| arg == "--network")
        && command
            .args
            .get(5)
            .is_some_and(|arg| arg == required_network)
        && command.args.get(6).is_some_and(|arg| arg == "--")
        && command
            .args
            .get(7)
            .is_some_and(|arg| arg == "/agent/hermes-acp")
}

fn checked_lifetime_worker_wall(
    selected: &AllowedCommand,
    requested: u64,
    prompt_active: bool,
    child_alive: bool,
    child_program: Option<&Path>,
    foreground_active: bool,
) -> Result<u64> {
    let effective = selected.wall_time_seconds.unwrap_or(600);
    if !prompt_active
        || foreground_active
        || !child_alive
        || child_program != Some(selected.program.as_path())
        || requested != effective
    {
        return Err("lifetime reserve worker wall differs from active Hermes worker".into());
    }
    Ok(effective)
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PublicationGrant {
    kind: String,
    target: String,
    capability: String,
    observe_capability: String,
}

#[derive(Clone)]
struct Authority {
    task: String,
    subject: String,
    capability: String,
    query_capability: String,
    custody_key: PathBuf,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AllowedCommand {
    name: String,
    program: PathBuf,
    #[serde(default)]
    args: Vec<String>,
    #[serde(default)]
    systemd_scope: bool,
    /// Fixed scoped worker lifetime; omitted retains the launcher's 600s cap.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    wall_time_seconds: Option<u64>,
    /// Maximum amount to reserve, in AgentGrain permission micro-units.
    reserve: String,
    /// Amount reported after the command. This is an operator configured
    /// charge, not a cryptographic measurement of CPU or provider usage.
    charge: String,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Journal {
    format: String,
    binding: Value,
    next_operation_id: u64,
    connection: Connection,
    pending: Option<Pending>,
    #[serde(default)]
    tool_pending: Option<Pending>,
    #[serde(default)]
    provider_pending: Option<Pending>,
    #[serde(default)]
    hard_reconnect_pending: bool,
    child: Option<ChildRecord>,
    settlement_due: Option<String>,
    #[serde(default)]
    parent_hold: Option<HeldCharge>,
    #[serde(default)]
    tool_hold: Option<HeldCharge>,
    #[serde(default)]
    dispatch_pending: Option<Pending>,
    #[serde(default)]
    dispatch_hold: Option<HeldCharge>,
    #[serde(default)]
    dispatch_attempt: Option<DispatchAttempt>,
    #[serde(default)]
    application_api_attempt: Option<ApplicationApiAttempt>,
    #[serde(default)]
    application_api_history: Vec<ApplicationApiAttempt>,
    #[serde(default)]
    provider_hold: Option<HeldCharge>,
    #[serde(default)]
    provider_attempt: Option<ProviderAttempt>,
    #[serde(default)]
    provider_settlement: Option<ProviderSettlement>,
    /// Bounded exact-body replay for completed responses in the current ACP
    /// prompt. SDK retries receive these bytes without another upstream send.
    #[serde(default)]
    provider_replays: Vec<ProviderReplay>,
    #[serde(default)]
    foreground_attempt: Option<ForegroundAttempt>,
    #[serde(default)]
    foreground_history: Vec<ForegroundAttempt>,
    /// Confirmed native publication receipts retained independently of ACP
    /// tool-result delivery. Never synthesize a tool response from this list.
    #[serde(default)]
    publication_receipts: Vec<PublicationReceipt>,
    /// Ordinals are consumed before dispatch. A proven no-submit birth may
    /// return only its unoccupied tail after signed zero settlement; any
    /// possible native submit keeps the consumed ordinal.
    #[serde(default)]
    birth_next_ordinal: BTreeMap<String, u16>,
    #[serde(default)]
    birth_operation: Option<BirthOperation>,
    #[serde(default)]
    birth_pending: Option<BirthPending>,
    #[serde(default)]
    born_resources: Vec<BornResourceRecord>,
    #[serde(default)]
    workspace_proposals: Vec<WorkspaceProposal>,
    #[serde(default)]
    workspace_attempt: Option<WorkspaceAttempt>,
    #[serde(default)]
    workspace_birth: Option<WorkspaceBirth>,
    /// Terminal resolution of every workspace submission, newest last and
    /// bounded. `performed`, `refused` and `uncertain` are the only values;
    /// an uncertain record is never resubmitted, only re-looked-up.
    #[serde(default)]
    workspace_resolutions: Vec<WorkspaceResolution>,
    /// Worker generation of the last managed law this controller confirmed
    /// installing. Renewal recognizes exactly that law as its own after a
    /// fence advanced the grain generation past it.
    #[serde(default)]
    managed_law_generation: Option<String>,
    #[serde(default)]
    reconciliation_log: Vec<Value>,
    #[serde(default)]
    hermes_session: Option<HermesSession>,
    #[serde(default)]
    prior_hermes_sessions: Vec<HermesSession>,
    #[serde(default)]
    prompt_witness: Option<Value>,
    unresolved_external: Vec<String>,
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "snake_case")]
enum Connection {
    Detached,
    Hard,
    Soft,
    Fenced,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Pending {
    operation_id: u64,
    operation: String,
    attempt: PathBuf,
    /// Once any attempt is uncertain, no new work is admitted until exact
    /// lookup or a human investigates the durable attempt.
    uncertain: bool,
    #[serde(default)]
    publication: Option<PublicationPending>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WorkspaceProposal {
    id: u64,
    request_sha256: String,
    intent_sha256: String,
    submitted: bool,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WorkspaceAttempt {
    operation_id: u64,
    proposal_id: u64,
    intent_sha256: String,
    attempt: PathBuf,
    /// A retained marker exists before the first possible native submit.
    /// A definite outcome is kept until the delegated tool purse settles.
    #[serde(default)]
    definite: bool,
    #[serde(default)]
    no_submit: bool,
}

const MAX_WORKSPACE_RESOLUTIONS: usize = 256;

/// How a held allowance's signed reservation is shown to be the one this
/// controller confirmed before it is settled.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HoldProof {
    /// No Mini event since the reserve receipt.
    SameImage,
    /// An operator reviewed the exact retained attempts.
    OperatorAudited,
    /// Parent only: the installed law is this controller's exact managed
    /// worker law and no parent attempt is pending.
    OwnManagedLaw,
}

impl HoldProof {
    fn label(self) -> &'static str {
        match self {
            Self::SameImage => "same-image",
            Self::OperatorAudited => "operator-audited",
            Self::OwnManagedLaw => "own-managed-law",
        }
    }
}

/// Worker generations whose exact managed law a renewal accepts as its own.
/// A paused grain may carry the law for its current generation or, after an
/// interrupted renewal, the next one. A hard fence advances the generation
/// without a law change, so the generation this controller last confirmed
/// installing is also its own law. Nothing else is: a custom law, or any
/// other generation, still refuses.
fn managed_law_candidates(status: &str, desired: u64, own: Option<u64>) -> Result<Vec<u64>> {
    let mut candidates = if status == "0" {
        let paused = desired
            .checked_sub(1)
            .ok_or("paused generation has no prior value")?;
        vec![desired, paused]
    } else {
        vec![desired]
    };
    if let Some(own) = own {
        if own <= desired && !candidates.contains(&own) {
            candidates.push(own);
        }
    }
    Ok(candidates)
}

/// Unresolved-effect notes whose only possible effects, for a network-none
/// scoped worker with every Mini attempt resolved, are already accounted for.
fn derivable_effect_note(note: &str) -> bool {
    (note.starts_with("worker operation ")
        && note.ends_with(" stopped after controller restart; external effects need acknowledgement"))
        || note == "controller restarted with a held allowance but no retained worker completion; effects require acknowledgement"
        || note == "parent reserved operation may have external effects; explicit operator acknowledgement required"
        || note.starts_with("Hermes prompt ")
}

/// Startup proof that no process of an earlier run of this controller's
/// unit survives: this process is the unit's active MainPID and the unit
/// cgroup lists only this process.
fn prove_prior_run_stopped(task: &str) -> Result<()> {
    prove_controller_unit(task)?;
    let cgroup = fs::read_to_string("/proc/self/cgroup")
        .map_err(|e| format!("controller cgroup: {e}"))?;
    let path = cgroup
        .lines()
        .find_map(|line| line.strip_prefix("0::"))
        .ok_or("controller is not in a unified cgroup")?;
    if !path.ends_with(&format!("/mini-grain-controller@{task}.service")) || path.contains("..") {
        return Err("controller cgroup is not its unit".into());
    }
    let procs = fs::read_to_string(format!("/sys/fs/cgroup{path}/cgroup.procs"))
        .map_err(|e| format!("controller cgroup members: {e}"))?;
    let members: Vec<&str> = procs.split_whitespace().collect();
    if members != [std::process::id().to_string().as_str()] {
        return Err(format!(
            "controller unit cgroup holds other processes: {}",
            members.join(",")
        ));
    }
    Ok(())
}

/// The retained terminal state of one workspace submission. `basis` names
/// the evidence that decided it; `outcome` is the exact native record (or
/// a marker when no native record exists).
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WorkspaceResolution {
    operation_id: u64,
    proposal_id: u64,
    intent_sha256: String,
    attempt: PathBuf,
    resolution: String,
    basis: String,
    outcome: Value,
    tool_charge: String,
    resolved_by: String,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WorkspaceBirth {
    operation_id: u64,
    name: String,
    storage: String,
    predicate_path: PathBuf,
    predicate_sha256: String,
    attempt: PathBuf,
    #[serde(default)]
    no_submit: bool,
    #[serde(default)]
    definite: bool,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PublicationPending {
    prompt_operation_id: u64,
    session_id: String,
    /// Explicit for foreground calls; absent in retained pre-foreground journals.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    work_origin: Option<WorkOrigin>,
    source_sha256: String,
    targets: Vec<String>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PublicationReceipt {
    prompt_operation_id: u64,
    session_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    work_origin: Option<WorkOrigin>,
    operation_id: u64,
    attempt: PathBuf,
    source_sha256: String,
    call_sha256: String,
    outcome_path: PathBuf,
    outcome_sha256: String,
    targets: Vec<String>,
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    image_boundary: String,
    /// Set only after a later ACP prompt has completed with a verified report.
    reported: bool,
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BirthPending {
    operation_id: u64,
    family: String,
    ordinal: u16,
    source_sha256: String,
    born: resource_tools::BornResource,
    /// Legacy records omit these fields and remain one-resource births. A
    /// multi-resource birth retains its ordered complete source-derived set
    /// under one exact operation, call and native receipt.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    route: Option<ApplicationBirthRoute>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    born_bundle: Vec<resource_tools::BornResource>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    selected_application: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    selected_shared: Option<shared_app_refs::CurrentSharedApplication>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    authored_intent_sha256: Option<String>,
    tool_view: Value,
    parent_view: Value,
    prompt_operation_id: u64,
    session_id: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    work_origin: Option<WorkOrigin>,
}

/// A foreground invocation is its own work identity. Historical journals
/// omit this field and retain the original Hermes session identity.
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "kebab-case", deny_unknown_fields)]
enum WorkOrigin {
    ForegroundTool { operation_id: u64 },
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ForegroundAttempt {
    request_id: String,
    operation_id: u64,
    name: String,
    request_path: PathBuf,
    request_sha256: String,
    phase: ForegroundPhase,
    #[serde(default)]
    result_path: Option<PathBuf>,
    #[serde(default)]
    result_sha256: Option<String>,
    /// Explicit client acknowledgement (or operator-audited terminal with no
    /// result). Queuing a socket frame is never a delivery acknowledgement.
    #[serde(default)]
    reported: bool,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ForegroundTombstone {
    request_id: String,
    operation_id: u64,
    request_sha256: String,
}

fn foreground_tombstone_path(state_dir: &Path, request_id: &str) -> PathBuf {
    state_dir.join(format!("foreground-request-{request_id}.json"))
}

fn read_foreground_tombstone(
    state_dir: &Path,
    request_id: &str,
) -> Result<Option<ForegroundTombstone>> {
    let path = foreground_tombstone_path(state_dir, request_id);
    if !path.exists() {
        return Ok(None);
    }
    let tombstone: ForegroundTombstone =
        serde_json::from_slice(&bounded_regular_file(&path, 4096)?)
            .map_err(|e| format!("foreground tombstone: {e}"))?;
    if tombstone.request_id != request_id
        || tombstone.operation_id == 0
        || tombstone.request_sha256.len() != 64
        || !tombstone
            .request_sha256
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("foreground tombstone identity changed".into());
    }
    Ok(Some(tombstone))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ForegroundRequest {
    #[serde(rename = "requestId")]
    request_id: String,
    name: String,
    arguments: Value,
}

fn valid_foreground_request_id(id: &str) -> bool {
    id.len() == 32
        && id
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}

fn foreground_request_id(frame: &[u8]) -> Option<String> {
    let value: Value = serde_json::from_slice(frame).ok()?;
    let id = value.get("requestId")?.as_str()?;
    valid_foreground_request_id(id).then(|| id.to_owned())
}

fn bounded_foreground_result(mut result: Value) -> Result<(Value, Vec<u8>)> {
    let mut bytes = serde_json::to_vec(&result).map_err(|e| e.to_string())?;
    // Leave room for the operation/request IDs and the outer control frame.
    // Native effects and their exact receipts remain in the journal even if a
    // tool produced more text than this foreground transport can retain.
    if bytes.len() > 1_000_000 {
        result = json!({"isError":true,
            "text":"foreground result exceeds the 1 MiB transport profile; inspect retained native receipts before any further work",
            "originalResultSha256":sha256_bytes(&bytes)?,
            "originalResultBytes":bytes.len()});
        bytes = serde_json::to_vec(&result).map_err(|e| e.to_string())?;
    }
    Ok((result, bytes))
}

fn managed_worker_policy_source(owner: &str, workers: &[String], generation: &str) -> Value {
    if workers.len() == 1 {
        json!({"owner":owner,"workerSubject":workers[0],"workerGeneration":generation})
    } else {
        json!({"owner":owner,"workerSubjects":workers,"workerGeneration":generation})
    }
}

#[derive(Clone, Copy, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum ForegroundPhase {
    Prepared,
    Reserved,
    Executing,
    Definite,
    Uncertain,
    Audited,
}

#[derive(Clone, Copy, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum ApplicationBirthRoute {
    Application,
    Session,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum DispatchFenceOutcome {
    Released,
    HeldForAudit,
}

impl BirthPending {
    fn members(&self) -> &[resource_tools::BornResource] {
        if self.born_bundle.is_empty() {
            std::slice::from_ref(&self.born)
        } else {
            &self.born_bundle
        }
    }

    fn validate_members(&self) -> Result<()> {
        match &self.work_origin {
            None if self.session_id.is_empty() => {
                return Err("Hermes birth origin lacks its retained session".into());
            }
            Some(WorkOrigin::ForegroundTool { operation_id })
                if *operation_id != self.prompt_operation_id || !self.session_id.is_empty() =>
            {
                return Err("foreground birth origin differs from its operation".into());
            }
            _ => {}
        }
        let expected = match self.route {
            None => {
                if !self.born_bundle.is_empty() {
                    return Err("legacy resource birth carries an unexpected bundle".into());
                }
                1
            }
            Some(ApplicationBirthRoute::Application) => 3,
            Some(ApplicationBirthRoute::Session) => 2,
        };
        let members = self.members();
        if members.len() != expected || members.first() != Some(&self.born) {
            return Err("birth bundle has the wrong member count or primary resource".into());
        }
        if (self.route == Some(ApplicationBirthRoute::Session))
            != self.selected_application.is_some()
            || self
                .selected_application
                .as_ref()
                .is_some_and(String::is_empty)
            || self.route.is_some() != self.authored_intent_sha256.is_some()
        {
            return Err("birth bundle has an invalid application selector".into());
        }
        if self.selected_shared.as_ref().is_some_and(|shared| {
            self.route != Some(ApplicationBirthRoute::Session)
                || self.selected_application.as_deref() != Some(shared.name.as_str())
        }) {
            return Err("birth bundle has a mismatched shared application reference".into());
        }
        let mut names = std::collections::HashSet::new();
        let mut targets = std::collections::HashSet::new();
        let mut grants = std::collections::HashSet::new();
        for member in members {
            if member.name.is_empty()
                || member.kind != "object"
                || member.max_result_bytes == 0
                || member.max_result_bytes > 4 * 1024 * 1024
                || !names.insert(&member.name)
            {
                return Err("birth bundle has an invalid or duplicate member".into());
            }
            for (id, label) in [
                (&member.target, "born target"),
                (&member.owner_capability, "born owner capability"),
                (&member.control_capability, "born control capability"),
            ] {
                decimal(id, label)?;
            }
            if !targets.insert(&member.target)
                || !grants.insert(&member.owner_capability)
                || !grants.insert(&member.control_capability)
            {
                return Err("birth bundle has duplicate targets or grants".into());
            }
        }
        Ok(())
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BirthOperation {
    family: String,
    ordinal: u16,
    // Old journals have no proof of the pre-submit boundary. They keep the
    // consumed ordinal even when a later zero settlement clears the marker.
    #[serde(default)]
    no_native_submit: bool,
}

fn retire_no_birth_operation(journal: &mut Journal) -> Result<()> {
    let Some(operation) = journal.birth_operation.as_ref() else {
        return Ok(());
    };
    if journal.birth_pending.is_some() || journal.tool_pending.is_some() {
        return Err("no-birth ordinal still has a pending native attempt".into());
    }
    if operation.no_native_submit {
        let expected_next = operation
            .ordinal
            .checked_add(1)
            .ok_or("no-birth ordinal overflow")?;
        if journal.birth_next_ordinal.get(&operation.family) != Some(&expected_next)
            || journal.born_resources.iter().any(|record| {
                record.pending.family == operation.family
                    && record.pending.ordinal == operation.ordinal
            })
        {
            return Err("no-birth ordinal is not an unoccupied family tail".into());
        }
        journal
            .birth_next_ordinal
            .insert(operation.family.clone(), operation.ordinal);
    }
    journal.birth_operation = None;
    Ok(())
}

fn persist_retired_no_birth_operation(path: &Path, journal: &mut Journal) -> Result<()> {
    let mut terminal = journal.clone();
    retire_no_birth_operation(&mut terminal)?;
    atomic_json(path, &terminal)?;
    *journal = terminal;
    Ok(())
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BornResourceRecord {
    pending: BirthPending,
    attempt: PathBuf,
    call_sha256: String,
    outcome_path: PathBuf,
    outcome_sha256: String,
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    image_boundary: String,
    #[serde(default)]
    reported: bool,
}

fn same_publication_confirmation(a: &PublicationReceipt, b: &PublicationReceipt) -> bool {
    a.operation_id == b.operation_id
        && a.prompt_operation_id == b.prompt_operation_id
        && a.session_id == b.session_id
        && a.work_origin == b.work_origin
        && a.source_sha256 == b.source_sha256
        && a.call_sha256 == b.call_sha256
        && a.targets == b.targets
        && a.transaction_id == b.transaction_id
        && a.event_id == b.event_id
        && a.accepted_count == b.accepted_count
        && a.image_boundary == b.image_boundary
}

fn current_publication_receipt<'a>(
    records: &'a [PublicationReceipt],
    prior_operation_ids: &[u64],
    prompt_operation_id: u64,
    session_id: &str,
    work_origin: Option<&WorkOrigin>,
    targets: &[String],
) -> Result<&'a PublicationReceipt> {
    let mut matching = records.iter().filter(|record| {
        !prior_operation_ids.contains(&record.operation_id)
            && record.prompt_operation_id == prompt_operation_id
            && record.session_id == session_id
            && record.work_origin.as_ref() == work_origin
            && record.targets == targets
            && !record.reported
    });
    let record = matching
        .next()
        .ok_or("current publication has no journaled confirmed receipt")?;
    if matching.next().is_some() {
        return Err("current publication has ambiguous journaled receipts".into());
    }
    Ok(record)
}

fn publication_receipt_json(record: &PublicationReceipt) -> Value {
    json!({
        "type":"confirmed-mini-publication-v1",
        "scope":"historical-accepted-transition",
        "promptOperationId":record.prompt_operation_id,
        "toolOperationId":record.operation_id,
        "transactionId":record.transaction_id,
        "eventId":record.event_id,
        "acceptedCount":record.accepted_count,
        "imageBoundary":record.image_boundary,
        "publicationTargetIds":record.targets,
    })
}

fn birth_receipt_json(record: &BornResourceRecord) -> Value {
    if let Some(route) = record.pending.route {
        return json!({"type":"confirmed-mini-application-birth-v1",
            "scope":"historical-accepted-transition",
            "route":route,
            "bornResources":record.pending.members(),
            "birthReceipt":{"operationId":record.pending.operation_id.to_string(),
            "transactionId":record.transaction_id,"eventId":record.event_id,
            "acceptedCount":record.accepted_count,"imageBoundary":record.image_boundary}});
    }
    json!({"type":"confirmed-mini-resource-birth-v1",
        "scope":"historical-accepted-transition",
        "name":record.pending.born.name,"kind":record.pending.born.kind,
        "target":record.pending.born.target,
        "birthReceipt":{"operationId":record.pending.operation_id.to_string(),
        "transactionId":record.transaction_id,"eventId":record.event_id,
        "acceptedCount":record.accepted_count,"imageBoundary":record.image_boundary}})
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ChildRecord {
    operation_id: u64,
    pid: u32,
    program: PathBuf,
    /// The process-group ID is diagnostic after controller death. Recovery
    /// never signals it: PIDs can be recycled after a crash.
    pgid: i32,
    #[serde(default)]
    unit: Option<String>,
    /// A durable launch-gate tombstone exists before the wrapper can start.
    /// Old records lacking the exact paired launcher protocol require an
    /// operator's physical audit.
    #[serde(default)]
    launch_gate_protocol: Option<String>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct HeldCharge {
    reserve: String,
    charge: String,
    before_generation: String,
    before_target_root: String,
    reserve_attempt: Option<PathBuf>,
    reserve_confirmed: bool,
    reserve_refused: bool,
    reserve_boundary: Option<String>,
    #[serde(default)]
    reserve_call_sha256: Option<String>,
    #[serde(default)]
    reserve_source_sha256: Option<String>,
    #[serde(default)]
    reserve_outcome_path: Option<PathBuf>,
    #[serde(default)]
    reserve_outcome_sha256: Option<String>,
    #[serde(default)]
    reserve_anchor: Option<ReserveAnchor>,
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ReserveAnchor {
    transaction_id: String,
    event_id: String,
    accepted_count: String,
    image_boundary: String,
}

impl ReserveAnchor {
    fn from_confirmed(value: &Value) -> Result<Self> {
        if value.get("type").and_then(Value::as_str) != Some("confirmed") {
            return Err("reserve has no confirmed native receipt".into());
        }
        let field = |name: &str| -> Result<String> {
            let value = value
                .get(name)
                .and_then(Value::as_str)
                .ok_or_else(|| format!("confirmed reserve lacks {name}"))?;
            decimal(value, name)?;
            Ok(value.to_owned())
        };
        Ok(Self {
            transaction_id: field("transactionId")?,
            event_id: field("eventId")?,
            accepted_count: field("acceptedCount")?,
            image_boundary: field("imageBoundary")?,
        })
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProviderAttempt {
    id: u64,
    prompt_operation_id: u64,
    parent_generation: String,
    model: String,
    request_path: PathBuf,
    request_bytes: usize,
    request_sha256: String,
    /// The send boundary is durable before gateway I/O starts. An absent
    /// response after this point means the external effect is uncertain.
    send_started: bool,
    outcome_path: Option<PathBuf>,
    outcome_bytes: Option<usize>,
    outcome_sha256: Option<String>,
    outcome: Option<String>,
    #[serde(default)]
    response_status: Option<u16>,
    #[serde(default)]
    response_content_type: Option<String>,
    #[serde(default)]
    response_headers_path: Option<PathBuf>,
    #[serde(default)]
    response_headers_bytes: Option<usize>,
    #[serde(default)]
    response_headers_sha256: Option<String>,
    #[serde(default)]
    metering_pin: Option<ProviderMeteringPin>,
    #[serde(default)]
    meter_report_path: Option<PathBuf>,
    #[serde(default)]
    meter_report_sha256: Option<String>,
    #[serde(default)]
    metered_charge: Option<String>,
}

/// One exact app dispatch attempt under the separate AgentGrain purse. The
/// request is retained before reserve; `send_started` is durable before fd3.
#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DispatchAttempt {
    id: u64,
    http_operation_id: String,
    parent_generation: String,
    parent_root: String,
    request_path: PathBuf,
    request_bytes: usize,
    request_sha256: String,
    source_request_digest: String,
    reserve_operation_id: Option<u64>,
    #[serde(default)]
    reserve_v2_dir: Option<PathBuf>,
    #[serde(default)]
    reserve_v2_request_sha256: Option<String>,
    #[serde(default)]
    reserve_v2_plan_sha256: Option<String>,
    #[serde(default)]
    reserve_v2_source_sha256: Option<String>,
    /// Event26 has a distinct source/receipt/lookup chain. It must never
    /// enter the event21 recovery path or reinterpret a v2 attempt directory.
    #[serde(default)]
    lifetime: Option<LifetimeDispatchCustody>,
    #[serde(default)]
    dispatch_generation: Option<String>,
    #[serde(default)]
    dispatch_post_root: Option<String>,
    #[serde(default)]
    no_send_release_started: bool,
    #[serde(default)]
    audited_charge: Option<String>,
    #[serde(default)]
    settlement: Option<DispatchSettlement>,
    send_started: bool,
    #[serde(default)]
    committed_dispatch_transaction: Option<String>,
    #[serde(default)]
    committed_dispatch_event: Option<String>,
    #[serde(default)]
    committed_permit_sha256: Option<String>,
    #[serde(default)]
    response_sha256: Option<String>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LifetimeDispatchCustody {
    route_name: String,
    #[serde(default)]
    worker_wall_seconds: Option<u64>,
    original_issue_index: String,
    original_issue_receipt: application_api_tools::SourceReceiptPin,
    grant_issue_receipt: application_api_tools::SourceReceiptPin,
    grant_resource: String,
    grant_issue_index: String,
    grant_digest: String,
    grant_initialized_root: String,
    source_path: PathBuf,
    source_sha256: String,
    reserve_dir: PathBuf,
    reserve_request_sha256: String,
    reserve_plan_sha256: String,
    context_hex: String,
    app_generation: String,
    session_generation: String,
    parent_generation: String,
    purse_generation: String,
    app_physical_root: String,
    session_physical_root: String,
    parent_physical_root: String,
    pre_reserve_purse_physical_root: String,
    #[serde(default)]
    reserve_index: Option<String>,
    #[serde(default)]
    reserve_receipt: Option<ReserveAnchor>,
    #[serde(default)]
    post_reserve_purse_physical_root: Option<String>,
    #[serde(default)]
    paid_dir: Option<PathBuf>,
    #[serde(default)]
    paid_plan_sha256: Option<String>,
    #[serde(default)]
    paid_ingress_sha256: Option<String>,
    #[serde(default)]
    committed_frame_sha256: Option<String>,
    #[serde(default)]
    committed_receipt: Option<ReserveAnchor>,
}

/// The controller persists this before any byte of the forward request can
/// cross to the resident host. Socket errors after that point never allocate
/// a replacement ID or resend the request.
#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ApplicationApiAttempt {
    operation_id: u64,
    route_name: String,
    request_path: PathBuf,
    request_sha256: String,
    phase: ApplicationApiPhase,
    #[serde(default)]
    binding_sha256: Option<String>,
    #[serde(default)]
    host_invocation: Option<String>,
    /// Source-derived per-dispatch current claims bind every v3 reply and
    /// historical inspection. This is never copied from Hello alone.
    #[serde(default)]
    operation_fingerprint: Option<String>,
    /// Event26 delivery lineage is recorded before fd3 ACK. A definite
    /// response also needs the exact confirmed purse settlement below.
    #[serde(default)]
    lifetime_committed_receipt: Option<ReserveAnchor>,
    #[serde(default)]
    lifetime_settled_response_sha256: Option<String>,
    #[serde(default)]
    lifetime_settlement: Option<LifetimeDefiniteSettlement>,
    #[serde(default)]
    reply_path: Option<PathBuf>,
    #[serde(default)]
    reply_sha256: Option<String>,
    #[serde(default)]
    reported: bool,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LifetimeDefiniteSettlement {
    dispatch_attempt_id: u64,
    forward_operation_id: u64,
    settlement: DispatchSettlement,
}

fn verified_lifetime_definite_reply(
    attempt: &ApplicationApiAttempt,
    reply: &Value,
    native_unresolved: bool,
) -> Result<()> {
    let committed = attempt
        .lifetime_committed_receipt
        .as_ref()
        .ok_or("lifetime definite reply lacks durable fresh permit lineage")?;
    let settled = attempt
        .lifetime_settled_response_sha256
        .as_deref()
        .ok_or("lifetime definite reply lacks confirmed purse settlement")?;
    let settlement = attempt
        .lifetime_settlement
        .as_ref()
        .ok_or("lifetime definite reply lacks durable native settlement record")?;
    if native_unresolved
        || settlement.forward_operation_id != attempt.operation_id
        || settlement.settlement.operation != "dispatch settle"
        || reply.get("committedReceipt") != Some(&json!(committed))
        || reply.get("responseSha256").and_then(Value::as_str) != Some(settled)
    {
        return Err("lifetime definite reply differs from settled native dispatch".into());
    }
    Ok(())
}

fn recovered_lifetime_http(
    attempt: &ApplicationApiAttempt,
    inspection: &Value,
    native_unresolved: bool,
) -> Result<Option<Value>> {
    if inspection.get("type").and_then(Value::as_str) != Some("inspection-v3")
        || inspection.get("protocol").and_then(Value::as_str) != Some("mini-spk-agent-api-v3")
        || inspection.get("operationId").and_then(Value::as_str)
            != Some(attempt.operation_id.to_string().as_str())
        || inspection.get("bindingSha256").and_then(Value::as_str)
            != attempt.binding_sha256.as_deref()
        || !matches!(
            inspection.get("state").and_then(Value::as_str),
            Some("not-seen" | "received" | "uncertain" | "definite")
        )
    {
        return Err("lifetime historical inspection differs from retained operation".into());
    }
    match (
        attempt.operation_fingerprint.as_deref(),
        inspection.get("operationFingerprint"),
    ) {
        (None, None) => {}
        (Some(saved), Some(Value::String(observed))) if saved == observed => {}
        _ => return Err("lifetime historical fingerprint differs".into()),
    }
    let digest = inspection.get("definiteReplySha256");
    let encoded = inspection.get("definiteReplyJsonHex");
    let (Some(Value::String(digest)), Some(Value::String(encoded))) = (digest, encoded) else {
        if digest.is_some()
            || encoded.is_some()
            || inspection.get("state").and_then(Value::as_str) == Some("definite")
            || (inspection.get("retentionError").is_some()
                && inspection.get("state").and_then(Value::as_str) != Some("uncertain"))
        {
            return Err("lifetime historical definite reply is incomplete".into());
        }
        return Ok(None);
    };
    if inspection.get("state").and_then(Value::as_str) != Some("definite")
        || inspection.get("retentionError").is_some()
        || encoded.len() > 2 * 262_144
    {
        return Err("lifetime historical definite reply is not cleanly retained".into());
    }
    let bytes = dispatch_custody::decode_hex(encoded)?;
    if sha256_bytes(&bytes)? != *digest {
        return Err("lifetime historical reply digest differs".into());
    }
    let reply: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("lifetime historical reply JSON: {error}"))?;
    if reply.get("type").and_then(Value::as_str) != Some("http-v3")
        || reply.get("protocol").and_then(Value::as_str) != Some("mini-spk-agent-api-v3")
        || reply.get("operationId").and_then(Value::as_str)
            != Some(attempt.operation_id.to_string().as_str())
        || reply.get("bindingSha256") != inspection.get("bindingSha256")
        || reply.get("operationFingerprint") != inspection.get("operationFingerprint")
    {
        return Err("lifetime historical HTTP reply differs from inspection".into());
    }
    verified_lifetime_definite_reply(attempt, &reply, native_unresolved)?;
    Ok(Some(reply))
}

fn checked_lifetime_reserve_plan_hex(plan: &Value, plan_path: &Path) -> Result<String> {
    let encoded = plan
        .get("canonicalPlanHex")
        .and_then(Value::as_str)
        .ok_or("lifetime source plan hex absent")?;
    if dispatch_custody::decode_hex(encoded)? != bounded_regular_file(plan_path, 10 * 1024 * 1024)?
    {
        return Err("lifetime source plan hex differs from retained bytes".into());
    }
    Ok(encoded.to_owned())
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum ApplicationApiPhase {
    Prepared,
    BindingVerified,
    DispatchStarted,
    NoDispatch,
    Definite,
    Uncertain,
}

enum ApplicationApiStep {
    Hello(application_api_tools::PendingExchange),
    Dispatch(application_api_tools::PendingExchange),
}

struct ActiveApplicationApi {
    operation_id: u64,
    route: ApplicationApiRoute,
    lifetime_input: Option<application_api_tools::HttpInput>,
    request: Value,
    reply: mpsc::Sender<Value>,
    step: ApplicationApiStep,
    deadline: Instant,
    raw_worker_reply: bool,
}

enum ApplicationApiRoute {
    V2(Box<application_api_tools::RoutePin>),
    Lifetime(Box<application_api_tools::LifetimeRoutePin>),
}

impl ApplicationApiRoute {
    fn socket_path(&self) -> &Path {
        match self {
            Self::V2(route) => &route.socket_path,
            Self::Lifetime(route) => &route.socket_path,
        }
    }

    fn host_uid(&self) -> u32 {
        match self {
            Self::V2(route) => route.host_uid,
            Self::Lifetime(route) => route.host_uid,
        }
    }
}

fn cancel_application_api_on_acp_failure(
    cancelled: &AtomicBool,
    gate: &application_api_tools::ForwardSendGate,
) -> Instant {
    cancelled.store(true, Ordering::SeqCst);
    gate.cancel();
    Instant::now() + Duration::from_secs(2)
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DispatchSettlement {
    operation_id: u64,
    operation: String,
    attempt: PathBuf,
    charge: String,
    source_sha256: String,
    call_sha256: String,
    outcome_path: PathBuf,
    outcome_sha256: String,
    receipt: ReserveAnchor,
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProviderSettlement {
    provider_attempt_id: u64,
    operation_id: u64,
    operation: String,
    attempt: PathBuf,
    charge: String,
    source_sha256: String,
    call_sha256: String,
    outcome_path: PathBuf,
    outcome_sha256: String,
    receipt: ReserveAnchor,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum MeteredAuditPath {
    ProvenNoSend,
    CompleteResponse,
}

fn metered_audit_path(send_started: bool, outcome: Option<&str>) -> Result<MeteredAuditPath> {
    if outcome.is_some_and(|kind| kind.starts_with("not-sent:"))
        || (!send_started && outcome.is_none())
    {
        Ok(MeteredAuditPath::ProvenNoSend)
    } else if send_started && outcome.is_some_and(|kind| kind.starts_with("received:")) {
        Ok(MeteredAuditPath::CompleteResponse)
    } else {
        Err("metered provider audit has no complete retained response or proven no-send".into())
    }
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProviderMeteringPin {
    provider_resource_id: String,
    #[serde(default = "legacy_metering_metadata_version")]
    metadata_version: u8,
    model: String,
    tariff_version: String,
    tariff_digest: String,
    #[serde(default)]
    input_micro_per_million: String,
    #[serde(default)]
    output_micro_per_million: String,
    #[serde(default)]
    max_input_tokens: Option<u32>,
    #[serde(default)]
    max_output_tokens: Option<u32>,
}

fn legacy_metering_metadata_version() -> u8 {
    1
}

fn provider_metering_metadata(
    pin: &ProviderMeteringPin,
    status: u16,
    content_type: &str,
    reserve: &str,
) -> Result<Value> {
    let common = json!({"status":status.to_string(),"contentType":content_type,
        "reserve":reserve});
    match pin.metadata_version {
        1 => Ok(common),
        2 => Ok(
            json!({"version":"2","providerResourceId":pin.provider_resource_id,
            "status":status.to_string(),"contentType":content_type,"reserve":reserve}),
        ),
        _ => Err("unknown pinned provider metering metadata version".into()),
    }
}

fn provider_max_charge_bound(pin: &ProviderMeteringPin, input: u32, output: u32) -> Result<u128> {
    let input_rate = pin
        .input_micro_per_million
        .parse::<u128>()
        .map_err(|_| "provider input tariff rate exceeds u128")?;
    let output_rate = pin
        .output_micro_per_million
        .parse::<u128>()
        .map_err(|_| "provider output tariff rate exceeds u128")?;
    let total = u128::from(input)
        .checked_mul(input_rate)
        .and_then(|amount| {
            u128::from(output)
                .checked_mul(output_rate)
                .and_then(|other| amount.checked_add(other))
        })
        .ok_or("provider maximum charge bound overflows")?;
    total
        .checked_add(999_999)
        .map(|value| value / 1_000_000)
        .ok_or("provider maximum charge rounding overflows".into())
}

fn provider_quote_charge(
    report: &Value,
    pin: &ProviderMeteringPin,
    reserve: &str,
    request_bytes: usize,
    response_bytes: usize,
) -> Result<String> {
    if report.get("type").and_then(Value::as_str) != Some("minidregg-provider-metering-v1")
        || report.get("status").and_then(Value::as_str) != Some("quoted-reported-usage")
        || report.get("model").and_then(Value::as_str) != Some(pin.model.as_str())
        || report.get("providerResourceId").and_then(Value::as_str)
            != Some(pin.provider_resource_id.as_str())
        || report.get("tariffVersion").and_then(Value::as_str) != Some(pin.tariff_version.as_str())
        || report.get("tariffDigest").and_then(Value::as_str) != Some(pin.tariff_digest.as_str())
        || report.get("reserve").and_then(Value::as_str) != Some(reserve)
        || report.get("requestBytes").and_then(Value::as_str)
            != Some(request_bytes.to_string().as_str())
        || report.get("responseBytes").and_then(Value::as_str)
            != Some(response_bytes.to_string().as_str())
        || report.get("claim").and_then(Value::as_str)
            != Some("provider-reported usage under operator tariff; not invoice-verified")
    {
        return Err(
            "provider quote differs from pinned task, tariff, hold, or exact byte lengths".into(),
        );
    }
    let charge = report
        .get("charge")
        .and_then(Value::as_str)
        .ok_or("provider quote has no charge")?;
    if charge.len() > 20 {
        return Err("provider quote charge exceeds decimal width".into());
    }
    decimal(charge, "provider quote charge")?;
    if charge
        .parse::<u64>()
        .map_err(|_| "provider quote charge exceeds u64")?
        > reserve
            .parse::<u64>()
            .map_err(|_| "provider reserve exceeds u64")?
        || report.pointer("/operation/type").and_then(Value::as_str) != Some("settle")
        || report.pointer("/operation/charge").and_then(Value::as_str) != Some(charge)
    {
        return Err("provider quote settlement exceeds the signed reserve".into());
    }
    for name in [
        "requestDigest",
        "responseDigest",
        "promptTokens",
        "completionTokens",
        "totalTokens",
    ] {
        let value = report
            .get(name)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("provider quote lacks {name}"))?;
        if value.len() > 80 {
            return Err(format!("provider quote {name} exceeds decimal bound"));
        }
        decimal(value, name)?;
    }
    let prompt_tokens = report
        .get("promptTokens")
        .and_then(Value::as_str)
        .ok_or("provider quote lacks promptTokens")?
        .parse::<u128>()
        .map_err(|_| "provider quote promptTokens exceeds u128")?;
    let completion_tokens = report
        .get("completionTokens")
        .and_then(Value::as_str)
        .ok_or("provider quote lacks completionTokens")?
        .parse::<u128>()
        .map_err(|_| "provider quote completionTokens exceeds u128")?;
    if prompt_tokens > u128::from(pin.max_input_tokens.ok_or("metered input ceiling absent")?)
        || completion_tokens
            > u128::from(
                pin.max_output_tokens
                    .ok_or("metered output ceiling absent")?,
            )
    {
        return Err("provider-reported usage exceeds operator-pinned token ceiling".into());
    }
    Ok(charge.to_owned())
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProviderReplay {
    prompt_operation_id: u64,
    parent_generation: String,
    request_path: PathBuf,
    request_bytes: usize,
    request_sha256: String,
    response_path: PathBuf,
    response_bytes: usize,
    response_sha256: String,
    status: u16,
    content_type: String,
    #[serde(default)]
    response_headers_path: Option<PathBuf>,
    #[serde(default)]
    response_headers_bytes: Option<usize>,
    #[serde(default)]
    response_headers_sha256: Option<String>,
    #[serde(default)]
    meter_report_path: Option<PathBuf>,
    #[serde(default)]
    meter_report_sha256: Option<String>,
    #[serde(default)]
    metered_charge: Option<String>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum AuthoritySlot {
    Parent,
    Tool,
    Dispatch,
    Provider,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct HermesSession {
    id: String,
    workspace: PathBuf,
    /// A successful fresh-process session/load proves this ID was retained.
    load_verified: bool,
    /// Hashes of the closed SQLite database and WAL, if present. This detects
    /// changes between turns; the worker can still write its own transcript.
    state_fingerprint: Option<String>,
    retention_issue: Option<String>,
    /// A prompt was sent but no completed-turn fingerprint was recorded.
    /// Its expected SQLite writes are examined after physical and Mini
    /// reconciliation, then the exact ID must pass session/load.
    #[serde(default)]
    pending_prompt: bool,
}

impl Journal {
    fn validate_workspace(&self, config: &Config) -> Result<()> {
        if self.workspace_proposals.len() > 64 {
            return Err("workspace proposal retention bound exceeded".into());
        }
        if self.workspace_resolutions.len() > MAX_WORKSPACE_RESOLUTIONS {
            return Err("workspace resolution retention bound exceeded".into());
        }
        let mut resolved = std::collections::HashSet::new();
        for record in &self.workspace_resolutions {
            if record.operation_id >= self.next_operation_id
                || !resolved.insert(record.operation_id)
                || !matches!(
                    record.resolution.as_str(),
                    "performed" | "refused" | "uncertain"
                )
                || self
                    .workspace_attempt
                    .as_ref()
                    .is_some_and(|pending| pending.operation_id == record.operation_id)
            {
                return Err("workspace resolution record is malformed".into());
            }
        }
        if self.workspace_proposals.is_empty()
            && self.workspace_attempt.is_none()
            && self.workspace_birth.is_none()
        {
            return Ok(());
        }
        let tool = config
            .tool_task
            .as_ref()
            .ok_or("workspace records have no ToolTask")?;
        let root = validate_resource_workspace(config, tool)?;
        let mut ids = std::collections::HashSet::new();
        for proposal in &self.workspace_proposals {
            if proposal.id >= self.next_operation_id
                || !ids.insert(proposal.id)
                || sha256_bytes(&bounded_regular_file(
                    &config
                        .state_dir
                        .join(format!("workspace-proposal-{:016}.json", proposal.id)),
                    32_768,
                )?)? != proposal.request_sha256
                || sha256_bytes(&bounded_regular_file(
                    &root
                        .join("proposals")
                        .join(proposal.id.to_string())
                        .join("intent.json"),
                    262_144,
                )?)? != proposal.intent_sha256
            {
                return Err("workspace proposal differs from retained source".into());
            }
        }
        if let Some(pending) = &self.workspace_attempt {
            if pending.operation_id >= self.next_operation_id
                || pending.attempt != root.join("attempts").join(pending.operation_id.to_string())
                || !self.workspace_proposals.iter().any(|proposal| {
                    proposal.id == pending.proposal_id
                        && proposal.submitted
                        && proposal.intent_sha256 == pending.intent_sha256
                })
                || (pending.no_submit && pending.attempt.exists())
            {
                return Err("workspace attempt differs from submitted proposal".into());
            }
        }
        if self.workspace_attempt.is_some() && self.workspace_birth.is_some() {
            return Err("workspace cannot retain two concurrent native effects".into());
        }
        if let Some(birth) = &self.workspace_birth {
            if birth.operation_id >= self.next_operation_id
                || birth.name.is_empty()
                || birth.name.len() > 64
                || !birth
                    .name
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-')
                || !matches!(birth.storage.as_str(), "content" | "declared")
                || birth.predicate_path
                    != config.state_dir.join(format!(
                        "workspace-birth-{:016}.predicate.json",
                        birth.operation_id
                    ))
                || sha256_bytes(&bounded_regular_file(&birth.predicate_path, 32_768)?)?
                    != birth.predicate_sha256
                || birth.attempt != root.join("attempts").join(format!("create-{}", birth.name))
                || (birth.no_submit && birth.attempt.exists())
            {
                return Err("workspace birth marker differs from retained request".into());
            }
        }
        Ok(())
    }

    fn validate_application_api(&self, state_dir: &Path) -> Result<()> {
        if self.application_api_history.len() > 16 {
            return Err("application API history exceeds retention bound".into());
        }
        let mut seen = std::collections::HashSet::new();
        for attempt in self
            .application_api_history
            .iter()
            .chain(self.application_api_attempt.iter())
        {
            if !seen.insert(attempt.operation_id)
                || attempt.operation_id >= self.next_operation_id
                || attempt.request_path
                    != state_dir.join(format!("application-api-{:016}.json", attempt.operation_id))
                || sha256_bytes(&bounded_regular_file(&attempt.request_path, 262_144)?)?
                    != attempt.request_sha256
            {
                return Err("application API attempt has changed or repeated".into());
            }
            if attempt.binding_sha256.is_some() != attempt.host_invocation.is_some()
                || (matches!(
                    attempt.phase,
                    ApplicationApiPhase::BindingVerified
                        | ApplicationApiPhase::DispatchStarted
                        | ApplicationApiPhase::Definite
                ) && attempt.binding_sha256.is_none())
            {
                return Err("application API binding phase is inconsistent".into());
            }
            match (&attempt.reply_path, &attempt.reply_sha256) {
                (None, None) if !matches!(attempt.phase, ApplicationApiPhase::Definite) => {}
                (Some(path), Some(digest))
                    if *path
                        == state_dir.join(format!(
                            "application-api-reply-{:016}.json",
                            attempt.operation_id
                        ))
                        && sha256_bytes(&bounded_regular_file(path, 262_144)?)? == *digest => {}
                _ => return Err("application API retained reply differs".into()),
            }
            if attempt.reported
                && !matches!(
                    attempt.phase,
                    ApplicationApiPhase::Definite | ApplicationApiPhase::NoDispatch
                )
            {
                return Err("application API reported a nondefinite result".into());
            }
            if let Some(settled) = attempt.lifetime_settlement.as_ref() {
                if settled.forward_operation_id != attempt.operation_id
                    || settled.settlement.operation != "dispatch settle"
                    || attempt.lifetime_settled_response_sha256.is_none()
                    || attempt.lifetime_committed_receipt.is_none()
                {
                    return Err("application API retained lifetime settlement differs".into());
                }
            }
        }
        Ok(())
    }

    fn validate_foreground(&self, state_dir: &Path) -> Result<()> {
        if self.foreground_history.len() > 256 {
            return Err("foreground result history exceeds retention bound".into());
        }
        let mut seen = std::collections::HashSet::new();
        for attempt in self
            .foreground_history
            .iter()
            .chain(self.foreground_attempt.iter())
        {
            if !valid_foreground_request_id(&attempt.request_id)
                || !seen.insert((attempt.operation_id, attempt.request_id.clone()))
                || attempt.operation_id >= self.next_operation_id
                || attempt.request_path
                    != state_dir.join(format!(
                        "foreground-{:016}.request.json",
                        attempt.operation_id
                    ))
                || sha256_bytes(&bounded_regular_file(&attempt.request_path, 262_144)?)?
                    != attempt.request_sha256
            {
                return Err("foreground request origin changed or repeated".into());
            }
            let tombstone = read_foreground_tombstone(state_dir, &attempt.request_id)?
                .ok_or("foreground request tombstone absent")?;
            if tombstone.operation_id != attempt.operation_id
                || tombstone.request_sha256 != attempt.request_sha256
            {
                return Err("foreground request tombstone differs from journal".into());
            }
            match (&attempt.result_path, &attempt.result_sha256) {
                (None, None) if attempt.phase != ForegroundPhase::Definite => {}
                (Some(path), Some(digest))
                    if *path
                        == state_dir.join(format!(
                            "foreground-{:016}.result.json",
                            attempt.operation_id
                        ))
                        && sha256_bytes(&bounded_regular_file(path, 1_048_576)?)? == *digest => {}
                _ => return Err("foreground retained result differs".into()),
            }
            if attempt.reported
                && !matches!(
                    attempt.phase,
                    ForegroundPhase::Definite | ForegroundPhase::Audited
                )
            {
                return Err("foreground result was reported before settlement".into());
            }
        }
        let mut request_ids = std::collections::HashSet::new();
        let mut operation_ids = std::collections::HashSet::new();
        for attempt in self
            .foreground_history
            .iter()
            .chain(self.foreground_attempt.iter())
        {
            if !request_ids.insert(&attempt.request_id)
                || !operation_ids.insert(attempt.operation_id)
            {
                return Err("foreground identity repeated".into());
            }
        }
        Ok(())
    }

    fn validate_birth_registry(&self) -> Result<()> {
        let mut operations = std::collections::HashSet::new();
        let mut names = std::collections::HashSet::new();
        let mut targets = std::collections::HashSet::new();
        let mut grants = std::collections::HashSet::new();
        let mut count = 0usize;
        for record in &self.born_resources {
            record.pending.validate_members()?;
            if !operations.insert(record.pending.operation_id) {
                return Err("born registry repeats an operation ID".into());
            }
            count = count
                .checked_add(record.pending.members().len())
                .ok_or("born registry count overflow")?;
            for member in record.pending.members() {
                if !names.insert(&member.name)
                    || !targets.insert(&member.target)
                    || !grants.insert(&member.owner_capability)
                    || !grants.insert(&member.control_capability)
                {
                    return Err("born registry repeats a name, target or grant".into());
                }
            }
        }
        if count > 8 * 1024 {
            return Err("born registry exceeds resource capacity".into());
        }
        if let Some(pending) = &self.birth_pending {
            pending.validate_members()?;
            if count + pending.members().len() > 8 * 1024 {
                return Err("pending birth exceeds resource capacity".into());
            }
            for member in pending.members() {
                if names.contains(&member.name)
                    || targets.contains(&member.target)
                    || grants.contains(&member.owner_capability)
                    || grants.contains(&member.control_capability)
                {
                    return Err("pending birth overlaps the installed registry".into());
                }
            }
        }
        Ok(())
    }

    fn born_resource_count(&self) -> usize {
        self.born_resources
            .iter()
            .map(|record| record.pending.members().len())
            .sum()
    }

    fn pending_for(&self, slot: AuthoritySlot) -> &Option<Pending> {
        match slot {
            AuthoritySlot::Parent => &self.pending,
            AuthoritySlot::Tool => &self.tool_pending,
            AuthoritySlot::Dispatch => &self.dispatch_pending,
            AuthoritySlot::Provider => &self.provider_pending,
        }
    }
    fn pending_for_mut(&mut self, slot: AuthoritySlot) -> &mut Option<Pending> {
        match slot {
            AuthoritySlot::Parent => &mut self.pending,
            AuthoritySlot::Tool => &mut self.tool_pending,
            AuthoritySlot::Dispatch => &mut self.dispatch_pending,
            AuthoritySlot::Provider => &mut self.provider_pending,
        }
    }
    fn hold_for(&self, slot: AuthoritySlot) -> &Option<HeldCharge> {
        match slot {
            AuthoritySlot::Parent => &self.parent_hold,
            AuthoritySlot::Tool => &self.tool_hold,
            AuthoritySlot::Dispatch => &self.dispatch_hold,
            AuthoritySlot::Provider => &self.provider_hold,
        }
    }
    fn hold_for_mut(&mut self, slot: AuthoritySlot) -> &mut Option<HeldCharge> {
        match slot {
            AuthoritySlot::Parent => &mut self.parent_hold,
            AuthoritySlot::Tool => &mut self.tool_hold,
            AuthoritySlot::Dispatch => &mut self.dispatch_hold,
            AuthoritySlot::Provider => &mut self.provider_hold,
        }
    }
    fn fresh(binding: Value) -> Self {
        Self {
            format: "minidregg-grain-runtime-v1".into(),
            binding,
            next_operation_id: 1,
            connection: Connection::Detached,
            pending: None,
            tool_pending: None,
            provider_pending: None,
            hard_reconnect_pending: false,
            child: None,
            settlement_due: None,
            parent_hold: None,
            tool_hold: None,
            dispatch_pending: None,
            dispatch_hold: None,
            dispatch_attempt: None,
            application_api_attempt: None,
            application_api_history: Vec::new(),
            provider_hold: None,
            provider_attempt: None,
            provider_settlement: None,
            provider_replays: Vec::new(),
            foreground_attempt: None,
            foreground_history: Vec::new(),
            publication_receipts: Vec::new(),
            birth_next_ordinal: BTreeMap::new(),
            birth_operation: None,
            birth_pending: None,
            born_resources: Vec::new(),
            workspace_proposals: Vec::new(),
            workspace_attempt: None,
            workspace_birth: None,
            workspace_resolutions: Vec::new(),
            managed_law_generation: None,
            reconciliation_log: Vec::new(),
            hermes_session: None,
            prior_hermes_sessions: Vec::new(),
            prompt_witness: None,
            unresolved_external: Vec::new(),
        }
    }
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut options = OpenOptions::new();
    options.write(true).create_new(true);
    use std::os::unix::fs::OpenOptionsExt;
    options.mode(0o600);
    let mut file = options
        .open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(bytes)
        .and_then(|_| file.sync_all())
        .map_err(|e| format!("{}: {e}", path.display()))
}

/// Re-enter a private pre-send artifact only if its entire retained byte
/// sequence is unchanged. A partial prior write stays explicit and cannot
/// silently become a new approval on retry.
fn retain_exact_private(path: &Path, bytes: &[u8], limit: usize) -> Result<()> {
    if bytes.is_empty() || bytes.len() > limit {
        return Err("private custody artifact exceeds its bound".into());
    }
    if path.exists() {
        if bounded_regular_file(path, limit)? != bytes {
            return Err("retained private custody artifact differs from prior attempt".into());
        }
        Ok(())
    } else {
        write_new(path, bytes)
    }
}

fn bounded_policy_bytes(path: &Path) -> Result<Vec<u8>> {
    let metadata = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() == 0 || metadata.len() > 131_072 {
        return Err("source-authored policy predicate is absent or exceeds 128 KiB".into());
    }
    fs::read(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn sha256_file(path: &Path) -> Result<String> {
    let output = Command::new("/usr/bin/openssl")
        .args(["dgst", "-sha256"])
        .arg(path)
        .output()
        .map_err(|e| format!("file digest: {e}"))?;
    if !output.status.success() {
        return Err(format!("file digest refused for {}", path.display()));
    }
    let line = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let digest = line.split_whitespace().last().ok_or("file digest absent")?;
    if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("file digest is not SHA-256 hex".into());
    }
    Ok(digest.to_ascii_lowercase())
}

fn sha256_bytes(bytes: &[u8]) -> Result<String> {
    let mut child = Command::new("/usr/bin/openssl")
        .args(["dgst", "-sha256"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .map_err(|e| format!("byte digest: {e}"))?;
    child
        .stdin
        .take()
        .ok_or("byte digest stdin absent")?
        .write_all(bytes)
        .map_err(|e| format!("byte digest input: {e}"))?;
    let output = child
        .wait_with_output()
        .map_err(|e| format!("byte digest result: {e}"))?;
    if !output.status.success() {
        return Err("byte digest refused".into());
    }
    let line = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let digest = line.split_whitespace().last().ok_or("byte digest absent")?;
    if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        return Err("byte digest is not SHA-256 hex".into());
    }
    Ok(digest.to_ascii_lowercase())
}

fn retained_exact(
    path: &Path,
    expected_len: usize,
    digest: &str,
    maximum: usize,
) -> Result<Vec<u8>> {
    let metadata =
        fs::symlink_metadata(path).map_err(|e| format!("retained {}: {e}", path.display()))?;
    if !metadata.file_type().is_file()
        || metadata.len() != expected_len as u64
        || expected_len > maximum
    {
        return Err(format!(
            "retained {} has the wrong type or length",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| format!("retained {}: {e}", path.display()))?
        .take((maximum + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("retained {}: {e}", path.display()))?;
    if bytes.len() != expected_len || sha256_bytes(&bytes)? != digest {
        return Err(format!(
            "retained {} differs from its journaled bytes",
            path.display()
        ));
    }
    Ok(bytes)
}

fn bounded_regular_file(path: &Path, maximum: usize) -> Result<Vec<u8>> {
    let metadata =
        fs::symlink_metadata(path).map_err(|e| format!("bounded {}: {e}", path.display()))?;
    if !metadata.file_type().is_file() || metadata.len() > maximum as u64 {
        return Err(format!(
            "bounded {} has the wrong type or length",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| format!("bounded {}: {e}", path.display()))?
        .take((maximum + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("bounded {}: {e}", path.display()))?;
    if bytes.len() > maximum {
        return Err(format!("bounded {} changed during read", path.display()));
    }
    Ok(bytes)
}

/// A socket prepare refusal is definitive only when the custody client
/// retained its exact op-255 reply before any call existed. The marker binds
/// the attempt-local request, config, and manifest; Lean decodes the Outcome.
/// Missing or inconsistent custody evidence is uncertainty, not a refusal.
fn inspected_pre_submit_refusal(config: &Config, attempt: &Path) -> Result<Option<Value>> {
    let frame_path = attempt.join("pre-submit-refusal.frame");
    let marker_path = attempt.join("pre-submit-refusal.json");
    if !frame_path.exists() && !marker_path.exists() {
        return Ok(None);
    }
    let read_bounded = |path: &Path, max: usize| -> Result<Vec<u8>> {
        let named = fs::symlink_metadata(path)
            .map_err(|e| format!("prepare refusal file {}: {e}", path.display()))?;
        if !named.file_type().is_file() || named.len() > max as u64 {
            return Err("prepare refusal file is not bounded regular data".into());
        }
        let file = File::open(path).map_err(|e| format!("prepare refusal open: {e}"))?;
        let opened = file
            .metadata()
            .map_err(|e| format!("prepare refusal stat: {e}"))?;
        if !opened.file_type().is_file()
            || (named.dev(), named.ino()) != (opened.dev(), opened.ino())
        {
            return Err("prepare refusal file changed while opening".into());
        }
        let mut bytes = Vec::new();
        file.take((max + 1) as u64)
            .read_to_end(&mut bytes)
            .map_err(|e| format!("prepare refusal read: {e}"))?;
        if bytes.len() > max {
            return Err("prepare refusal file exceeded byte bound".into());
        }
        Ok(bytes)
    };
    let marker_bytes = read_bounded(&marker_path, 65_536)?;
    let marker: Value = serde_json::from_slice(&marker_bytes)
        .map_err(|e| format!("prepare refusal marker decode: {e}"))?;
    if marker.as_object().is_none_or(|object| object.len() != 7)
        || marker["type"] != "minidregg-pre-submit-refusal-v1"
        || marker["stage"] != "prepare"
        || marker["operation"] != 1
    {
        return Err("prepare refusal marker has the wrong contract".into());
    }
    let digest_field = |name: &str| -> Result<&str> {
        let value = marker[name]
            .as_str()
            .ok_or("prepare refusal digest absent")?;
        if value.len() != 64
            || !value
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
        {
            return Err("prepare refusal digest is not lowercase SHA-256".into());
        }
        Ok(value)
    };
    if config.host_socket.is_none() {
        return Err("prepare refusal did not use a pinned socket".into());
    }
    let manifest_path = attempt.join("attempt.json");
    let manifest_bytes = read_bounded(&manifest_path, 65_536)?;
    let manifest: Value = serde_json::from_slice(&manifest_bytes)
        .map_err(|e| format!("prepare refusal manifest decode: {e}"))?;
    let copied_config = attempt.join("config.json");
    if manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["host"].as_str().map(Path::new) != Some(config.host.as_path())
        || manifest["config"].as_str().map(Path::new) != Some(copied_config.as_path())
        || manifest["socket"].as_str().map(Path::new) != config.host_socket.as_deref()
        || sha256_file(&manifest_path)? != digest_field("attemptManifestSha256")?
    {
        return Err("prepare refusal manifest differs from this operator-pinned submit".into());
    }
    let config_bytes = read_bounded(&copied_config, 65_536)?;
    let operator_config = read_bounded(&config.host_config, 65_536)?;
    if config_bytes != operator_config
        || sha256_file(&copied_config)? != digest_field("hostConfigSha256")?
    {
        return Err("prepare refusal config differs from operator pin".into());
    }
    let request_path = attempt.join("signed-observation.bin");
    let request = read_bounded(&request_path, 12_102_760)?;
    if request.is_empty() || sha256_file(&request_path)? != digest_field("requestSha256")? {
        return Err("prepare refusal signed observation differs from request pin".into());
    }
    for name in ["plan.bin", "call.bin", "outcome.bin", "outcome.json"] {
        match fs::symlink_metadata(attempt.join(name)) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Ok(_) => return Err("prepare refusal attempt contains later-stage artifact".into()),
            Err(e) => return Err(format!("prepare refusal artifact stat: {e}")),
        }
    }
    let frame = read_bounded(&frame_path, 12_102_761)?;
    if frame.len() < 2
        || frame[0] != 255
        || sha256_file(&frame_path)? != digest_field("frameSha256")?
    {
        return Err("prepare refusal frame differs from retained op-255 reply".into());
    }
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| format!("prepare refusal verification clock: {e}"))?
        .as_nanos();
    let inspect_dir = attempt.join(format!(
        "prepare-refusal-verify-{}-{nonce}",
        std::process::id()
    ));
    fs::create_dir(&inspect_dir).map_err(|e| format!("prepare refusal inspect directory: {e}"))?;
    let body = inspect_dir.join("outcome.bin");
    let result = inspect_dir.join("outcome.json");
    write_new(&body, &frame[1..])?;
    let status = Command::new(&config.host)
        .arg(&config.host_config)
        .arg("inspect")
        .arg("outcome")
        .arg(&body)
        .arg(&result)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map_err(|e| format!("native prepare refusal inspection: {e}"))?;
    if !status.success() {
        return Err("native Host did not decode prepare refusal Outcome".into());
    }
    let value: Value = serde_json::from_slice(&read_bounded(&result, 65_536)?)
        .map_err(|e| format!("native prepare refusal JSON: {e}"))?;
    if value["type"] != "refused" || value["phase"] != "70726570617265" {
        return Err("native Outcome is not a prepare-phase refusal".into());
    }
    Ok(Some(value))
}

fn valid_workspace_name(name: &str) -> bool {
    !name.is_empty()
        && name.len() <= 64
        && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
}

fn workspace_resolution_json(record: &WorkspaceResolution) -> Value {
    json!({"operationId":record.operation_id.to_string(),
        "proposalId":record.proposal_id.to_string(),
        "resolution":record.resolution,"basis":record.basis,
        "outcome":record.outcome,"toolCharge":record.tool_charge,
        "resolvedBy":record.resolved_by,"historical":true})
}

fn retained_retry_names(attempt: &Path) -> Result<std::collections::BTreeSet<String>> {
    let mut names = std::collections::BTreeSet::new();
    for entry in fs::read_dir(attempt).map_err(|e| format!("retained attempt listing: {e}"))? {
        let entry = entry.map_err(|e| format!("retained attempt listing: {e}"))?;
        if let Some(name) = entry.file_name().to_str() {
            if name.starts_with("retry-") && name.ends_with(".json") {
                names.insert(name.to_owned());
            }
        }
    }
    Ok(names)
}

/// The native record written by the lookup just run, if any. A lookup that
/// wrote nothing (transport failure) is not an answer.
fn newest_new_retry(
    attempt: &Path,
    before: &std::collections::BTreeSet<String>,
) -> Result<Option<Value>> {
    let after = retained_retry_names(attempt)?;
    let Some(name) = after.difference(before).max() else {
        return Ok(None);
    };
    let value = serde_json::from_slice(&bounded_regular_file(&attempt.join(name), 131_072)?)
        .map_err(|e| format!("retained lookup record JSON: {e}"))?;
    Ok(Some(value))
}

fn next_retry_json(attempt: &Path) -> Result<PathBuf> {
    for index in 1..=9999 {
        let binary = attempt.join(format!("retry-{index:04}.bin"));
        let json = attempt.join(format!("retry-{index:04}.json"));
        if !binary.exists() && !json.exists() {
            return Ok(json);
        }
    }
    Err("attempt exhausted native retry evidence names".into())
}

fn atomic_json(path: &Path, value: &impl Serialize) -> Result<()> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    let tmp = path.with_extension("tmp");
    if tmp.exists() {
        return Err(format!("unresolved temporary journal {}", tmp.display()));
    }
    write_new(&tmp, &bytes)?;
    fs::rename(&tmp, path).map_err(|e| format!("journal rename: {e}"))?;
    File::open(path.parent().unwrap())
        .and_then(|f| f.sync_all())
        .map_err(|e| format!("journal directory sync: {e}"))
}

fn decimal(s: &str, label: &str) -> Result<()> {
    if s.is_empty() || (s.len() > 1 && s.starts_with('0')) || !s.bytes().all(|b| b.is_ascii_digit())
    {
        Err(format!("{label} must be canonical nonnegative decimal"))
    } else {
        Ok(())
    }
}

fn previous_accepted_index(accepted: &str) -> Result<String> {
    decimal(accepted, "accepted count")?;
    if accepted == "0" || accepted.len() > 80 {
        return Err("accepted count cannot identify a preceding history index".into());
    }
    let mut digits = accepted.as_bytes().to_vec();
    for digit in digits.iter_mut().rev() {
        if *digit == b'0' {
            *digit = b'9';
        } else {
            *digit -= 1;
            break;
        }
    }
    let first = digits
        .iter()
        .position(|digit| *digit != b'0')
        .unwrap_or(digits.len() - 1);
    String::from_utf8(digits[first..].to_vec()).map_err(|error| error.to_string())
}

fn grain_observation_grants(
    authority: &Authority,
    parent: Option<(&str, &str)>,
    publications: &[Value],
) -> Result<Vec<Value>> {
    let mut grants = vec![json!({"kind":"object","target":authority.task,
        "capability":authority.query_capability})];
    if let Some((task, capability)) = parent {
        grants.push(json!({"kind":"object","target":task,"capability":capability}));
    }
    for publication in publications {
        let kind = publication
            .get("kind")
            .and_then(Value::as_str)
            .ok_or("publication observation kind absent")?;
        let target = publication
            .get("target")
            .and_then(Value::as_str)
            .ok_or("publication observation target absent")?;
        let capability = publication
            .get("observeCapability")
            .and_then(Value::as_str)
            .ok_or("publication observe capability absent")?;
        grants.push(json!({"kind":kind,"target":target,"capability":capability}));
    }
    Ok(grants)
}

fn provider_reserve_coordinates(state: &Value, hold: &HeldCharge) -> bool {
    hold.reserve_confirmed
        && state.pointer("/grain/status").and_then(Value::as_str) == Some("3")
        && state.pointer("/grain/reserved").and_then(Value::as_str) == Some(hold.reserve.as_str())
        && state.pointer("/grain/generation").and_then(Value::as_str)
            == Some(hold.before_generation.as_str())
}

fn provider_audit_coordinates(state: &Value, hold: &HeldCharge) -> bool {
    if provider_reserve_coordinates(state, hold) {
        return true;
    }
    if !hold.reserve_confirmed
        || !matches!(
            state.pointer("/grain/status").and_then(Value::as_str),
            Some("5" | "7")
        )
        || state.pointer("/grain/reserved").and_then(Value::as_str) != Some(hold.reserve.as_str())
    {
        return false;
    }
    hold.before_generation
        .parse::<u64>()
        .ok()
        .and_then(|generation| generation.checked_add(1))
        .is_some_and(|generation| {
            state.pointer("/grain/generation").and_then(Value::as_str)
                == Some(generation.to_string().as_str())
        })
}

fn hermes_workspace_home(cwd: &Path) -> Result<(PathBuf, PathBuf)> {
    let workspace = fs::canonicalize(cwd).map_err(|e| format!("Hermes workspace: {e}"))?;
    if !workspace.is_dir() {
        return Err("Hermes workspace is not a directory".into());
    }
    let home = workspace.join(".hermes");
    if !home.exists() {
        let mut builder = fs::DirBuilder::new();
        builder.mode(0o700);
        builder
            .create(&home)
            .map_err(|e| format!("Hermes home create: {e}"))?;
    }
    let meta = fs::symlink_metadata(&home).map_err(|e| format!("Hermes home: {e}"))?;
    if !meta.file_type().is_dir()
        || meta.file_type().is_symlink()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
    {
        return Err("Hermes home must be an owned real 0700 directory".into());
    }
    Ok((workspace, home))
}

fn hermes_state_fingerprint(home: &Path) -> Result<Option<String>> {
    let db = home.join("state.db");
    if !db.exists() {
        return Ok(None);
    }
    let mut parts = Vec::new();
    for name in ["state.db", "state.db-wal"] {
        let path = home.join(name);
        let meta = match fs::symlink_metadata(&path) {
            Ok(meta) => meta,
            Err(error) if error.kind() == io::ErrorKind::NotFound => {
                parts.push(format!("{name}:absent"));
                continue;
            }
            Err(error) => return Err(format!("Hermes state metadata: {error}")),
        };
        if !meta.file_type().is_file()
            || meta.file_type().is_symlink()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.mode() & 0o077 != 0
            || meta.len() > 536_870_912
        {
            return Err(format!(
                "Hermes {name} must be an owned private regular file under 512 MiB"
            ));
        }
        let output = Command::new("/usr/bin/openssl")
            .args(["dgst", "-sha256"])
            .arg(&path)
            .output()
            .map_err(|e| format!("Hermes state digest: {e}"))?;
        if !output.status.success() {
            return Err(format!("Hermes state digest refused for {name}"));
        }
        let line = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
        let digest = line
            .split_whitespace()
            .last()
            .ok_or("Hermes state digest absent")?;
        if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err("Hermes state digest malformed".into());
        }
        parts.push(format!("{name}:{}:{digest}", meta.len()));
    }
    Ok(Some(parts.join("|")))
}

fn validate(c: &Config) -> Result<()> {
    for (name, p) in [
        ("mini", &c.mini),
        ("host", &c.host),
        ("hostConfig", &c.host_config),
        ("custodyKey", &c.custody_key),
        ("stateDir", &c.state_dir),
        ("cwd", &c.cwd),
    ] {
        if !p.is_absolute() {
            return Err(format!("{name} must be absolute"));
        }
    }
    if c.host_socket.as_ref().is_some_and(|p| !p.is_absolute()) {
        return Err("hostSocket must be absolute".into());
    }
    if !c.control_socket.is_absolute() {
        return Err("controlSocket must be absolute".into());
    }
    if c.control_socket.parent() != Some(c.state_dir.as_path()) {
        return Err("controlSocket must be directly inside private stateDir".into());
    }
    for (name, s) in [
        ("task", &c.task),
        ("subject", &c.subject),
        ("capability", &c.capability),
        ("queryCapability", &c.query_capability),
    ] {
        decimal(s, name)?;
    }
    if let Some(control) = &c.policy_control_capability {
        decimal(control, "policyControlCapability")?;
    }
    if c.tool_task.is_some() && c.policy_control_capability.is_none() {
        return Err("toolTask requires policyControlCapability for generation renewal".into());
    }
    if let Some(profile) = &c.foreground_tool {
        if c.tool_task.is_none() {
            return Err("foregroundTool requires toolTask".into());
        }
        decimal(&profile.reserve, "foregroundTool.reserve")?;
        decimal(&profile.charge, "foregroundTool.charge")?;
        if profile
            .reserve
            .parse::<u64>()
            .ok()
            .filter(|value| *value > 0)
            .zip(profile.charge.parse::<u64>().ok())
            .is_none_or(|(reserve, charge)| charge > reserve)
        {
            return Err("foregroundTool charge must fit positive u64 reserve".into());
        }
    }
    #[cfg(not(target_os = "linux"))]
    if c.dispatch_task.is_some() {
        return Err("dispatchTask requires Linux SO_PEERCRED".into());
    }
    #[cfg(target_os = "linux")]
    if let Some(d) = &c.dispatch_task {
        if c.host_socket.is_none() || c.policy_control_capability.is_none() {
            return Err(
                "dispatchTask requires native host socket and parent generation renewal".into(),
            );
        }
        if d.task == c.task
            || c.tool_task.as_ref().is_some_and(|t| t.task == d.task)
            || c.provider_task.as_ref().is_some_and(|p| p.task == d.task)
        {
            return Err("dispatchTask must be a distinct Mini resource".into());
        }
        if d.subject == c.subject
            || c.tool_task.as_ref().is_some_and(|t| t.subject == d.subject)
            || c.provider_task
                .as_ref()
                .is_some_and(|p| p.subject == d.subject)
        {
            return Err("dispatchTask requires a distinct delegated subject".into());
        }
        for (name, value) in [
            ("dispatchTask.task", &d.task),
            ("dispatchTask.subject", &d.subject),
            ("dispatchTask.capability", &d.capability),
            ("dispatchTask.queryCapability", &d.query_capability),
            ("dispatchTask.parentCapability", &d.parent_capability),
            (
                "dispatchTask.parentObserveCapability",
                &d.parent_observe_capability,
            ),
            ("dispatchTask.reserve", &d.reserve),
            ("dispatchTask.charge", &d.charge),
        ] {
            decimal(value, name)?;
        }
        if !d.custody_key.is_absolute()
            || d.custody_key == c.custody_key
            || c.tool_task
                .as_ref()
                .is_some_and(|t| t.custody_key == d.custody_key)
            || c.provider_task
                .as_ref()
                .is_some_and(|p| p.custody_key == d.custody_key)
        {
            return Err("dispatchTask requires a distinct absolute custody key path".into());
        }
        if let Some(operator_socket) = &d.operator_socket {
            if !operator_socket.is_absolute()
                || c.host_socket.as_ref() == Some(operator_socket)
                || operator_socket == &d.socket_path
                || operator_socket == &c.control_socket
            {
                return Err("dispatchTask operatorSocket must be distinct and absolute".into());
            }
            let parent = operator_socket
                .parent()
                .ok_or("dispatchTask operatorSocket parent absent")?;
            let directory = fs::symlink_metadata(parent)
                .map_err(|error| format!("dispatchTask operatorSocket parent: {error}"))?;
            let named = fs::symlink_metadata(operator_socket)
                .map_err(|error| format!("dispatchTask operatorSocket: {error}"))?;
            if !directory.file_type().is_dir()
                || directory.uid() != unsafe { libc::geteuid() }
                || directory.mode() & 0o077 != 0
                || !named.file_type().is_socket()
                || named.uid() != unsafe { libc::geteuid() }
                || named.mode() & 0o077 != 0
            {
                return Err("dispatchTask operatorSocket must be owner-private".into());
            }
        }
        if let Some(signer) = &d.reserve_signer {
            decimal(&signer.role, "dispatchTask.reserveSigner.role")?;
            decimal(&signer.index, "dispatchTask.reserveSigner.index")?;
            decimal(&signer.key_id, "dispatchTask.reserveSigner.keyId")?;
            decimal(&signer.key_epoch, "dispatchTask.reserveSigner.keyEpoch")?;
            if signer.public_key.len() != 64
                || !signer
                    .public_key
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(
                    "dispatchTask.reserveSigner.publicKey must be lowercase Ed25519 hex".into(),
                );
            }
        }
        if !d.socket_path.is_absolute()
            || d.socket_path.starts_with(&c.state_dir)
            || d.socket_path == c.control_socket
            || d.host_uid == 0
            || d.host_uid == unsafe { libc::geteuid() }
        {
            return Err(
                "dispatchTask requires external socket and distinct non-root host UID".into(),
            );
        }
        let parent = d
            .socket_path
            .parent()
            .ok_or("dispatchTask socket parent absent")?;
        for (depth, directory_path) in parent.ancestors().enumerate() {
            let directory = fs::symlink_metadata(directory_path)
                .map_err(|e| format!("dispatchTask socket ancestor: {e}"))?;
            // A root-owned sticky ancestor (not the socket parent) cannot
            // rename a task-owned descendant, as with a private directory
            // below /tmp in the isolated Linux fixture.
            let safe_sticky_ancestor =
                depth > 0 && directory.uid() == 0 && directory.mode() & 0o1000 != 0;
            if !directory.file_type().is_dir()
                || directory.file_type().is_symlink()
                || (directory.mode() & 0o022 != 0 && !safe_sticky_ancestor)
                || directory.mode() & 0o001 == 0
                || (directory.uid() != 0 && directory.uid() != unsafe { libc::geteuid() })
            {
                return Err(format!(
                    "dispatchTask socket ancestor {} must be real, root/task-owned and non-writable by other users (uid {}, mode {:o})",
                    directory_path.display(), directory.uid(), directory.mode() & 0o7777
                ));
            }
        }
        if d.reserve
            .parse::<u64>()
            .ok()
            .zip(d.charge.parse::<u64>().ok())
            .is_none_or(|(reserve, charge)| charge > reserve)
        {
            return Err("dispatchTask charge exceeds reserve".into());
        }
    }
    for command in &c.commands {
        if command.name.is_empty()
            || !command
                .name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-')
        {
            return Err("command name must be alphanumeric or '-'".into());
        }
        if c.commands
            .iter()
            .filter(|other| other.name == command.name)
            .count()
            != 1
        {
            return Err(format!("duplicate command name {}", command.name));
        }
        if !command.program.is_absolute() || command.program == c.mini || command.program == c.host
        {
            return Err(format!("invalid executable for {}", command.name));
        }
        if command.systemd_scope
            && command.program.file_name().and_then(|s| s.to_str()) != Some("bwrap")
        {
            return Err("systemdScope requires the grain-host bwrap launcher".into());
        }
        if command
            .wall_time_seconds
            .is_some_and(|seconds| !command.systemd_scope || !(1..=1800).contains(&seconds))
        {
            return Err("wallTimeSeconds requires a scoped worker and 1..1800 seconds".into());
        }
        decimal(&command.reserve, "reserve")?;
        decimal(&command.charge, "charge")?;
        if command
            .reserve
            .parse::<u64>()
            .ok()
            .zip(command.charge.parse::<u64>().ok())
            .is_none_or(|(r, ch)| ch > r)
        {
            return Err(format!(
                "{} charge must fit reserved u64 allowance",
                command.name
            ));
        }
    }
    if let Some(t) = &c.tool_task {
        if t.resource_workspace.is_some() {
            validate_resource_workspace(c, t)?;
        }
        if t.task == c.task {
            return Err("toolTask must be a distinct Mini resource".into());
        }
        for (name, s) in [
            ("toolTask.task", &t.task),
            ("toolTask.subject", &t.subject),
            ("toolTask.capability", &t.capability),
            ("toolTask.queryCapability", &t.query_capability),
            ("toolTask.parentCapability", &t.parent_capability),
            (
                "toolTask.parentObserveCapability",
                &t.parent_observe_capability,
            ),
            ("toolTask.reserve", &t.reserve),
            ("toolTask.charge", &t.charge),
        ] {
            decimal(s, name)?;
        }
        if !t.custody_key.is_absolute() || t.custody_key == c.custody_key {
            return Err("toolTask requires a distinct absolute custody key path".into());
        }
        if t.reserve
            .parse::<u64>()
            .ok()
            .zip(t.charge.parse::<u64>().ok())
            .is_none_or(|(r, ch)| ch > r)
        {
            return Err("toolTask charge exceeds reserve".into());
        }
        for grant in &t.allowed_publications {
            if !matches!(grant.kind.as_str(), "object" | "account" | "program") {
                return Err("unknown publication kind".into());
            }
            decimal(&grant.target, "publication target")?;
            decimal(&grant.capability, "publication capability")?;
            decimal(&grant.observe_capability, "publication observe capability")?;
        }
        resource_tools::validate_reads(&t.allowed_reads, &t.allowed_publications)?;
        shared_app_refs::validate_refs(&t.registered_shared_applications, t)?;
        if !t.allowed_application_api_routes.is_empty() {
            let dispatch = c
                .dispatch_task
                .as_ref()
                .ok_or("application API routes require a distinct dispatchTask")?;
            if dispatch.operator_socket.is_none() {
                return Err("application API routes require dispatchTask.operatorSocket".into());
            }
            if dispatch.reserve_signer.is_none() {
                return Err("application API routes require dispatchTask.reserveSigner".into());
            }
            application_api_tools::validate_routes(
                &t.allowed_application_api_routes,
                &c.task,
                &dispatch.task,
                &c.subject,
                dispatch.host_uid,
            )?;
            let expected = t
                .agent_api_host_sha256
                .as_deref()
                .ok_or("application API routes require a source-qualified event21 Mini Host pin")?;
            if c.host_socket.is_none() || sha256_file(&c.host)? != expected {
                return Err(
                    "application API Mini Host or persistent socket differs from pin".into(),
                );
            }
        } else if t.agent_api_host_sha256.is_some() {
            return Err("application API Host pin has no operator route".into());
        }
        if !t.allowed_application_lifetime_routes.is_empty() {
            let dispatch = c
                .dispatch_task
                .as_ref()
                .ok_or("lifetime API routes require a distinct dispatchTask")?;
            if dispatch.operator_socket.is_none() || dispatch.reserve_signer.is_none() {
                return Err("lifetime API routes require private dispatch custody".into());
            }
            application_api_tools::validate_lifetime_routes(
                &t.allowed_application_lifetime_routes,
                &t.allowed_application_api_routes,
                &c.task,
                &dispatch.task,
                &c.subject,
                dispatch.host_uid,
            )?;
            let expected = t
                .lifetime_api_host_sha256
                .as_deref()
                .ok_or("lifetime API routes require an event26 Mini Host pin")?;
            if c.host_socket.is_none() || sha256_file(&c.host)? != expected {
                return Err("lifetime API Mini Host or persistent socket differs from pin".into());
            }
        } else if t.lifetime_api_host_sha256.is_some() {
            return Err("lifetime API Host pin has no operator route".into());
        }
        let mut peer_targets = vec![c.task.as_str(), t.task.as_str()];
        let mut peer_capabilities = vec![
            c.capability.as_str(),
            c.query_capability.as_str(),
            t.capability.as_str(),
            t.query_capability.as_str(),
            t.parent_capability.as_str(),
            t.parent_observe_capability.as_str(),
        ];
        if let Some(control) = &c.policy_control_capability {
            peer_capabilities.push(control);
        }
        if let Some(provider) = &c.provider_task {
            peer_targets.push(&provider.task);
            peer_capabilities.extend([
                provider.capability.as_str(),
                provider.query_capability.as_str(),
                provider.parent_capability.as_str(),
                provider.parent_observe_capability.as_str(),
            ]);
        }
        if let Some(dispatch) = &c.dispatch_task {
            peer_targets.push(&dispatch.task);
            peer_capabilities.extend([
                dispatch.capability.as_str(),
                dispatch.query_capability.as_str(),
                dispatch.parent_capability.as_str(),
                dispatch.parent_observe_capability.as_str(),
            ]);
        }
        resource_tools::validate_birth_families(
            &t.allowed_birth_families,
            &t.allowed_reads,
            &t.allowed_publications,
            &peer_targets,
            &peer_capabilities,
        )?;
        application_tools::validate_families(
            &t.allowed_application_families,
            &t.allowed_session_families,
            &t.registered_shared_applications
                .iter()
                .map(|reference| reference.application_family.as_str())
                .collect::<Vec<_>>(),
            &t.allowed_birth_families,
            &t.allowed_reads,
            &t.allowed_publications,
            (&peer_targets, &peer_capabilities),
        )?;
        for family in &t.allowed_birth_families {
            let charge = resource_tools::planned_birth_charge(family)?;
            if charge.parse::<u64>().ok() > t.reserve.parse::<u64>().ok() {
                return Err(format!("{} birth tariff exceeds tool reserve", family.name));
            }
        }
        for family in &t.allowed_application_families {
            let charge = application_tools::planned_charge(&family.profile, 3)?;
            if charge.parse::<u64>().ok() > t.reserve.parse::<u64>().ok() {
                return Err(format!(
                    "{} application birth tariff exceeds tool reserve",
                    family.name
                ));
            }
        }
        for family in &t.allowed_session_families {
            let charge = application_tools::planned_charge(&family.profile, 2)?;
            if charge.parse::<u64>().ok() > t.reserve.parse::<u64>().ok() {
                return Err(format!(
                    "{} session birth tariff exceeds tool reserve",
                    family.name
                ));
            }
        }
        if !t.allowed_application_families.is_empty() || !t.allowed_session_families.is_empty() {
            let expected = t.current_birth_host_sha256.as_deref().ok_or(
                "current application birth requires an operator-pinned qualified Host image",
            )?;
            if c.host_socket.is_none() || expected != sha256_file(&c.host)? {
                return Err(
                    "current application birth Host image or socket differs from operator pin"
                        .into(),
                );
            }
        }
    }
    if let Some(p) = &c.provider_task {
        if c.host_socket.is_none() {
            return Err("providerTask continuity requires hostSocket".into());
        }
        if p.task == c.task || c.tool_task.as_ref().is_some_and(|t| t.task == p.task) {
            return Err("providerTask must be a distinct Mini resource".into());
        }
        if p.subject == c.subject || c.tool_task.as_ref().is_some_and(|t| t.subject == p.subject) {
            return Err("providerTask requires a distinct delegated subject".into());
        }
        if c.policy_control_capability.is_none() {
            return Err("providerTask requires parent policy generation renewal".into());
        }
        for (name, value) in [
            ("providerTask.task", &p.task),
            ("providerTask.subject", &p.subject),
            ("providerTask.capability", &p.capability),
            ("providerTask.queryCapability", &p.query_capability),
            ("providerTask.parentCapability", &p.parent_capability),
            (
                "providerTask.parentObserveCapability",
                &p.parent_observe_capability,
            ),
            ("providerTask.reserve", &p.reserve),
            ("providerTask.charge", &p.charge),
        ] {
            decimal(value, name)?;
        }
        if !p.custody_key.is_absolute()
            || p.custody_key == c.custody_key
            || c.tool_task
                .as_ref()
                .is_some_and(|t| t.custody_key == p.custody_key)
            || !p.provider_key_file.is_absolute()
            || p.provider_key_file == p.custody_key
            || p.provider_key_file == c.custody_key
            || c.tool_task
                .as_ref()
                .is_some_and(|t| t.custody_key == p.provider_key_file)
        {
            return Err("providerTask needs distinct absolute key paths".into());
        }
        if p.provider_key_file.parent() != Some(c.state_dir.as_path()) {
            return Err("provider key must be directly inside private stateDir".into());
        }
        if p.reserve
            .parse::<u64>()
            .ok()
            .zip(p.charge.parse::<u64>().ok())
            .is_none_or(|(reserve, charge)| charge > reserve)
        {
            return Err("providerTask charge exceeds reserve".into());
        }
        if p.metering && p.charge != "0" {
            return Err(
                "metered providerTask requires charge 0; only the Lean quote may settle usage"
                    .into(),
            );
        }
        if p.metering {
            if !p
                .max_input_tokens
                .is_some_and(|value| (1..=131_072).contains(&value))
                || !p
                    .max_output_tokens
                    .is_some_and(|value| (1..=8_192).contains(&value))
            {
                return Err("metered providerTask requires maxInputTokens 1..131072 and maxOutputTokens 1..8192".into());
            }
        } else if p.max_input_tokens.is_some() || p.max_output_tokens.is_some() {
            return Err("fixed-charge providerTask cannot set metered token ceilings".into());
        }
        provider_max_iterations(p.max_iterations)?;
        let bind = p
            .gateway_bind
            .parse::<std::net::SocketAddr>()
            .map_err(|_| "providerTask.gatewayBind must be a socket address")?;
        if !bind.ip().is_loopback() || bind.port() == 0 {
            return Err("providerTask.gatewayBind must pin a loopback port".into());
        }
        if !p.local_fixture_host_network
            && bind.ip() != std::net::IpAddr::V4(std::net::Ipv4Addr::LOCALHOST)
        {
            return Err("isolated provider bridge requires gatewayBind 127.0.0.1:PORT".into());
        }
        if p.model.is_empty()
            || p.model.len() > 256
            || p.model.chars().any(char::is_control)
            || p.max_request_bytes == 0
            || p.max_request_bytes > 1_048_576
            || p.max_response_bytes == 0
            || p.max_response_bytes > 8_388_608
            || p.timeout_seconds == 0
            || p.timeout_seconds > 600
        {
            return Err("providerTask model or bounds invalid".into());
        }
        let required_network = provider_required_network(p)?;
        if !c
            .commands
            .iter()
            .find(|command| command.name == "hermes-acp")
            .is_some_and(|command| provider_command_route(command, required_network))
        {
            return Err(
                "providerTask requires the selected hermes-acp command to have its configured network route"
                    .into(),
            );
        }
    }
    Ok(())
}

fn validate_resource_workspace(c: &Config, tool: &ToolTask) -> Result<PathBuf> {
    let root = tool
        .resource_workspace
        .as_ref()
        .ok_or("toolTask resourceWorkspace is not configured")?;
    if !root.is_absolute() || root.parent() != Some(c.state_dir.as_path()) {
        return Err("resourceWorkspace must be a direct child of controller stateDir".into());
    }
    let uid = unsafe { libc::geteuid() };
    for dir in [
        root.clone(),
        root.join("refs"),
        root.join("attempts"),
        root.join("sources"),
        root.join("proposals"),
    ] {
        let meta = fs::symlink_metadata(&dir)
            .map_err(|e| format!("resourceWorkspace directory {}: {e}", dir.display()))?;
        if !meta.file_type().is_dir() || meta.uid() != uid || meta.mode() & 0o077 != 0 {
            return Err(
                "resourceWorkspace directories must be owner-private real directories".into(),
            );
        }
    }
    let config_path = root.join("workspace.json");
    let meta =
        fs::symlink_metadata(&config_path).map_err(|e| format!("resourceWorkspace config: {e}"))?;
    if !meta.file_type().is_file() || meta.uid() != uid || meta.mode() & 0o077 != 0 {
        return Err("resourceWorkspace config must be an owner-private regular file".into());
    }
    let record: Value = serde_json::from_slice(&bounded_regular_file(&config_path, 65_536)?)
        .map_err(|e| format!("resourceWorkspace config JSON: {e}"))?;
    if record["type"] != "minidregg-participant-workspace-v1"
        || record["subject"].as_str() != Some(tool.subject.as_str())
        || record["host"].as_str().map(Path::new) != Some(c.host.as_path())
        || record["config"].as_str().map(Path::new) != Some(c.host_config.as_path())
        || record["key"].as_str().map(Path::new) != Some(tool.custody_key.as_path())
        || record["socket"].as_str().map(Path::new) != c.host_socket.as_deref()
    {
        return Err("resourceWorkspace custody differs from delegated ToolTask pins".into());
    }
    Ok(root.clone())
}

const PHASE_IDLE: u8 = 0;
const PHASE_RUNNING: u8 = 1;
const PHASE_SETTLING: u8 = 2;
const PHASE_CANCELLED: u8 = 3;

struct ActiveProvider {
    endpoint: provider::GatewayEndpoint,
    requests: Receiver<provider::ProviderCommand>,
    token: String,
    control_slot: Arc<Mutex<Option<provider::GatewayControl>>>,
}

impl Drop for ActiveProvider {
    fn drop(&mut self) {
        self.endpoint.control().revoke();
        if let Ok(mut slot) = self.control_slot.lock() {
            *slot = None;
        }
    }
}

struct Runtime {
    config: Config,
    config_path: PathBuf,
    journal: Journal,
    child: Option<Child>,
    _lock: File,
    stdin_gone: bool,
    current_pgid: Arc<AtomicI32>,
    hard_connection: Arc<AtomicBool>,
    signal_lock: Arc<Mutex<()>>,
    cancelled: Arc<AtomicBool>,
    custody_gate: Arc<custody_gate::CustodyGate>,
    application_api_send_gate: Arc<application_api_tools::ForwardSendGate>,
    completion_phase: Arc<AtomicU8>,
    current_unit: Arc<Mutex<Option<(String, PathBuf)>>>,
    provider_control: Arc<Mutex<Option<provider::GatewayControl>>>,
    provider_lease: Option<provider::LeaseId>,
    prompt_active: bool,
    foreground_operation: Option<u64>,
    output: Option<control::OutputHandle>,
    /// First controller operation ID allocated by this process. Earlier
    /// attempts were started by a previous process.
    process_first_operation_id: u64,
    /// True while `serve` runs its own recovery before accepting input.
    startup_recovery_active: bool,
    /// Set only by the startup proof that this controller is the active
    /// MainPID of its unit and its cgroup holds no other process, so no
    /// custody child of an earlier controller run can still send a call.
    prior_run_stopped: bool,
}

impl Runtime {
    fn current_work_origin(&self) -> Result<(u64, String, Option<WorkOrigin>)> {
        if let Some(operation_id) = self.foreground_operation {
            return Ok((
                operation_id,
                String::new(),
                Some(WorkOrigin::ForegroundTool { operation_id }),
            ));
        }
        let operation_id = self
            .journal
            .child
            .as_ref()
            .ok_or("work has no active Hermes worker")?
            .operation_id;
        let session_id = self
            .journal
            .hermes_session
            .as_ref()
            .ok_or("work has no retained Hermes session")?
            .id
            .clone();
        Ok((operation_id, session_id, None))
    }

    fn reserve_parent_work_lease(
        &mut self,
        reserve: &str,
        charge: &str,
        label: &str,
    ) -> Result<()> {
        self.mark_hold(false, reserve, charge)?;
        self.transition(json!({"type":"reserve","amount":reserve}), "reserve", label)?;
        let parent = self.query()?;
        let before = parent.get("grain").ok_or("reserved parent grain absent")?;
        if !matches!(
            before.get("status").and_then(Value::as_str),
            Some("3" | "4")
        ) {
            return Err("parent grain is not reserved after work allowance".into());
        }
        self.journal.prompt_witness = Some(json!({"task":self.config.task,
            "expectedTargetRoot":parent.get("targetRoot").ok_or("parent root absent")?,
            "before":{"generation":before.get("generation"),"status":before.get("status"),
                "remaining":before.get("remaining"),"reserved":before.get("reserved")}}));
        self.save()
    }
    fn emit(&self, message: impl Into<String>) {
        if let Some(output) = &self.output {
            let _ = output.try_output(message);
        }
    }
    fn revoke_provider_gateway(&mut self) {
        let control = self
            .provider_control
            .lock()
            .ok()
            .and_then(|guard| guard.clone());
        if let Some(control) = control {
            control.revoke();
        }
        self.provider_lease = None;
    }
    fn claim_completion(&mut self, charge: &str) -> Result<bool> {
        match self.completion_phase.compare_exchange(
            PHASE_RUNNING,
            PHASE_SETTLING,
            Ordering::SeqCst,
            Ordering::SeqCst,
        ) {
            Ok(_) => {
                self.journal.settlement_due = Some(charge.to_owned());
                self.save()?;
                Ok(true)
            }
            Err(PHASE_CANCELLED) => {
                if self.journal.connection == Connection::Hard {
                    self.journal.connection = Connection::Fenced;
                }
                self.save()?;
                Ok(false)
            }
            Err(phase) => Err(format!("unexpected worker completion phase {phase}")),
        }
    }
    fn worker_unit(&self, id: u64, spec: &AllowedCommand) -> Option<String> {
        spec.systemd_scope
            .then(|| format!("mini-grain-t{}-o{id}", self.config.task))
    }
    fn launch_gate(&self, program: &Path, unit: &str, action: &str) -> Result<()> {
        launch_gate(&self.config.state_dir, program, unit, action)
    }
    fn prove_launcher_gate(program: &Path) -> Result<()> {
        let output = Command::new(program)
            .arg("--launch-gate-protocol")
            .output()
            .map_err(|e| format!("grain launcher protocol: {e}"))?;
        if !output.status.success() || output.stdout != b"mini-grain-launch-gate-v1\n" {
            return Err("configured grain launcher lacks launch-gate v1 protocol".into());
        }
        Ok(())
    }
    fn worker_env(
        &self,
        command: &mut Command,
        spec: &AllowedCommand,
        unit: &Option<String>,
        broker: Option<&Path>,
    ) {
        if let Some(unit) = unit {
            command
                .env("MINI_GRAIN_UNIT", unit)
                .env(
                    "MINI_GRAIN_CONTROLLER_UNIT",
                    format!("mini-grain-controller@{}.service", self.config.task),
                )
                .env("MINI_GRAIN_STATE_DIR", &self.config.state_dir)
                .env("MINI_GRAIN_CUSTODY_KEY", &self.config.custody_key)
                .env("MINI_GRAIN_TASK_CONFIG", &self.config_path)
                .env("MINI_GRAIN_HOST_CONFIG", &self.config.host_config);
            if let Some(seconds) = spec.wall_time_seconds {
                command.env("MINI_GRAIN_RUNTIME_MAX_SEC", seconds.to_string());
            }
            if let Some(tool) = &self.config.tool_task {
                command.env("MINI_GRAIN_TOOL_CUSTODY_KEY", &tool.custody_key);
            }
            if let Some(provider) = &self.config.provider_task {
                command.env("MINI_GRAIN_PROVIDER_CUSTODY_KEY", &provider.custody_key);
                command.env("MINI_GRAIN_PROVIDER_KEY_FILE", &provider.provider_key_file);
                if spec.name == "hermes-acp" && !provider.local_fixture_host_network {
                    let port = provider
                        .gateway_bind
                        .parse::<std::net::SocketAddr>()
                        .expect("validated provider gateway address")
                        .port();
                    command
                        .env(
                            "MINI_GRAIN_PROVIDER_SOCKET",
                            self.config.state_dir.join("provider-gateway.sock"),
                        )
                        .env("MINI_GRAIN_PROVIDER_PORT", port.to_string());
                }
            }
            if let Some(broker) = broker {
                command.env("MINI_GRAIN_BROKER_SOCKET", broker);
            }
        }
    }
    fn parent(&self) -> Authority {
        Authority {
            task: self.config.task.clone(),
            subject: self.config.subject.clone(),
            capability: self.config.capability.clone(),
            query_capability: self.config.query_capability.clone(),
            custody_key: self.config.custody_key.clone(),
        }
    }
    fn tool(&self) -> Result<Authority> {
        let t = self
            .config
            .tool_task
            .as_ref()
            .ok_or("toolTask is not configured")?;
        Ok(Authority {
            task: t.task.clone(),
            subject: t.subject.clone(),
            capability: t.capability.clone(),
            query_capability: t.query_capability.clone(),
            custody_key: t.custody_key.clone(),
        })
    }
    fn dispatch(&self) -> Result<Authority> {
        let d = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask is not configured")?;
        Ok(Authority {
            task: d.task.clone(),
            subject: d.subject.clone(),
            capability: d.capability.clone(),
            query_capability: d.query_capability.clone(),
            custody_key: d.custody_key.clone(),
        })
    }
    fn dispatch_settlement_record(
        &self,
        pending: &Pending,
        outcome_path: &Path,
    ) -> Result<DispatchSettlement> {
        if !matches!(
            pending.operation.as_str(),
            "dispatch settle" | "dispatch release" | "dispatch audit settle"
        ) {
            return Err("dispatch settlement operation differs".into());
        }
        let source_path = self
            .config
            .state_dir
            .join(format!("source-{:016}.json", pending.operation_id));
        let source: Value = serde_json::from_slice(&bounded_regular_file(&source_path, 131_072)?)
            .map_err(|e| format!("dispatch settlement source: {e}"))?;
        let task = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask absent")?
            .clone();
        if source.pointer("/grain/task").and_then(Value::as_str) != Some(task.task.as_str())
            || source
                .pointer("/grain/operation/type")
                .and_then(Value::as_str)
                != Some("settle")
        {
            return Err("dispatch settlement source targets another task/operation".into());
        }
        let charge = source
            .pointer("/grain/operation/charge")
            .and_then(Value::as_str)
            .ok_or("dispatch settlement charge absent")?
            .to_owned();
        decimal(&charge, "dispatch settlement charge")?;
        if charge != "0" && charge != task.charge {
            return Err("dispatch settlement charge differs from fixed purse tariff".into());
        }
        let outcome: Value = serde_json::from_slice(&bounded_regular_file(outcome_path, 131_072)?)
            .map_err(|e| format!("dispatch settlement outcome: {e}"))?;
        Ok(DispatchSettlement {
            operation_id: pending.operation_id,
            operation: pending.operation.clone(),
            attempt: pending.attempt.clone(),
            charge,
            source_sha256: sha256_file(&source_path)?,
            call_sha256: sha256_file(&pending.attempt.join("call.bin"))?,
            outcome_path: outcome_path.to_owned(),
            outcome_sha256: sha256_file(&pending.attempt.join("outcome.bin"))?,
            receipt: ReserveAnchor::from_confirmed(&outcome)?,
        })
    }
    fn verified_dispatch_settlement(
        &self,
        attempt: &DispatchAttempt,
    ) -> Result<DispatchSettlement> {
        let saved = attempt
            .settlement
            .as_ref()
            .ok_or("dispatch attempt lacks exact settlement receipt")?;
        let pending = Pending {
            operation_id: saved.operation_id,
            operation: saved.operation.clone(),
            attempt: saved.attempt.clone(),
            uncertain: false,
            publication: None,
        };
        let actual = self.dispatch_settlement_record(&pending, &saved.outcome_path)?;
        if &actual != saved
            || (attempt.no_send_release_started && actual.charge != "0")
            || attempt
                .audited_charge
                .as_ref()
                .is_some_and(|charge| charge != &actual.charge)
        {
            return Err("dispatch settlement differs from retained request/decision".into());
        }
        self.verified_dispatch_settlement_record(saved)?;
        Ok(actual)
    }
    fn verified_dispatch_settlement_record(&self, saved: &DispatchSettlement) -> Result<()> {
        let pending = Pending {
            operation_id: saved.operation_id,
            operation: saved.operation.clone(),
            attempt: saved.attempt.clone(),
            uncertain: false,
            publication: None,
        };
        if self.dispatch_settlement_record(&pending, &saved.outcome_path)? != *saved {
            return Err("retained dispatch settlement evidence changed".into());
        }
        let retry_result = next_retry_json(&saved.attempt)?;
        let mut args = vec![
            "retry",
            "--attempt",
            saved
                .attempt
                .to_str()
                .ok_or("dispatch settlement attempt path UTF-8")?,
            "--mode",
            "lookup",
        ];
        if let Some(socket) = &self.config.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("Host socket path UTF-8")?]);
        }
        self.command_output(&self.config.mini, &args)?;
        let lookup: Value = serde_json::from_slice(&bounded_regular_file(&retry_result, 131_072)?)
            .map_err(|e| format!("dispatch settlement lookup: {e}"))?;
        if lookup.get("type").and_then(Value::as_str) != Some("confirmed")
            || !matches!(
                lookup.get("confirmation").and_then(Value::as_str),
                Some("installed" | "replayed")
            )
            || ReserveAnchor::from_confirmed(&lookup)? != saved.receipt
        {
            return Err("dispatch settlement is not confirmed in current native image".into());
        }
        Ok(())
    }
    /// Audit-only reconstruction of a reserve that may have committed just
    /// before the wrapper copied its operation/gen/postroot into the attempt.
    /// This never fills send coordinates or enables a late mark-send.
    fn verified_dispatch_reserve_hold(
        &self,
        attempt: &DispatchAttempt,
        hold: &HeldCharge,
    ) -> Result<(u64, ReserveAnchor)> {
        if let Some(lifetime) = &attempt.lifetime {
            let directory = &lifetime.reserve_dir;
            let id = attempt
                .reserve_operation_id
                .ok_or("lifetime reserve ID absent")?;
            if *directory
                != self
                    .config
                    .state_dir
                    .join(format!("agent-lifetime-reserve-{:016}", attempt.id))
                || lifetime.source_path
                    != self
                        .config
                        .state_dir
                        .join(format!("dispatch-lifetime-source-{id:016}.json"))
                || !hold.reserve_confirmed
                || hold.reserve_refused
                || hold.reserve_attempt.as_ref() != Some(directory)
                || sha256_file(&lifetime.source_path)? != lifetime.source_sha256
                || hold.reserve_source_sha256.as_deref() != Some(lifetime.source_sha256.as_str())
                || sha256_file(&directory.join("request.bin"))? != lifetime.reserve_request_sha256
                || sha256_file(&directory.join("plan.bin"))? != lifetime.reserve_plan_sha256
                || sha256_file(&directory.join("call.bin"))?
                    != hold
                        .reserve_call_sha256
                        .as_deref()
                        .ok_or("lifetime reserve call hash absent")?
            {
                return Err("lifetime reserve retained custody differs from journal".into());
            }
            let anchor = hold
                .reserve_anchor
                .as_ref()
                .ok_or("lifetime reserve anchor absent")?;
            if lifetime.reserve_receipt.as_ref() != Some(anchor) {
                return Err("lifetime reserve anchor differs from attempt".into());
            }
            let outcome = hold
                .reserve_outcome_path
                .as_ref()
                .ok_or("lifetime reserve outcome absent")?;
            if outcome.parent() != Some(directory.as_path())
                || sha256_file(outcome)?
                    != hold
                        .reserve_outcome_sha256
                        .as_deref()
                        .ok_or("lifetime outcome hash absent")?
            {
                return Err("lifetime reserve outcome differs from held anchor".into());
            }
            let observed: Value = serde_json::from_slice(&bounded_regular_file(
                &outcome.with_extension("json"),
                131_072,
            )?)
            .map_err(|error| format!("lifetime outcome JSON: {error}"))?;
            if ReserveAnchor::from_confirmed(&observed)? != *anchor {
                return Err("lifetime original outcome changed".into());
            }
            // This exact op3 is read-only; a second op2 is never issued.
            self.command_output(
                &self.config.mini,
                &[
                    "agent-lifetime-reserve-lookup",
                    "--attempt",
                    directory.to_str().ok_or("lifetime reserve path UTF-8")?,
                ],
            )?;
            let receipt: Value = serde_json::from_slice(&bounded_regular_file(
                &directory.join("receipt.json"),
                4096,
            )?)
            .map_err(|error| format!("lifetime reserve receipt JSON: {error}"))?;
            if receipt.get("transactionId").and_then(Value::as_str)
                != Some(anchor.transaction_id.as_str())
                || receipt.get("eventId").and_then(Value::as_str) != Some(anchor.event_id.as_str())
                || receipt.get("acceptedCount").and_then(Value::as_str)
                    != Some(anchor.accepted_count.as_str())
                || receipt.get("imageBoundary").and_then(Value::as_str)
                    != Some(anchor.image_boundary.as_str())
                || receipt.get("reserveIndex").and_then(Value::as_str)
                    != lifetime.reserve_index.as_deref()
            {
                return Err("lifetime historical reserve receipt differs".into());
            }
            return Ok((id, anchor.clone()));
        }
        if let Some(directory) = &attempt.reserve_v2_dir {
            let id = attempt
                .reserve_operation_id
                .ok_or("v2 reserve operation ID absent")?;
            if *directory
                != self
                    .config
                    .state_dir
                    .join(format!("agent-reserve-{:016}", attempt.id))
                || !hold.reserve_confirmed
                || hold.reserve_refused
                || hold.reserve_attempt.as_ref() != Some(directory)
                || hold.reserve
                    != self
                        .config
                        .dispatch_task
                        .as_ref()
                        .ok_or("dispatchTask absent")?
                        .reserve
                || sha256_file(&directory.join("request.bin"))?
                    != attempt
                        .reserve_v2_request_sha256
                        .as_deref()
                        .ok_or("v2 reserve request digest absent")?
                || sha256_file(&directory.join("plan.bin"))?
                    != attempt
                        .reserve_v2_plan_sha256
                        .as_deref()
                        .ok_or("v2 reserve plan digest absent")?
                || sha256_file(&directory.join("call.bin"))?
                    != hold
                        .reserve_call_sha256
                        .as_deref()
                        .ok_or("v2 reserve call digest absent")?
                || sha256_file(
                    &self
                        .config
                        .state_dir
                        .join(format!("dispatch-reserve-source-{id:016}.json")),
                )? != hold
                    .reserve_source_sha256
                    .as_deref()
                    .ok_or("v2 reserve source digest absent")?
                || hold.reserve_source_sha256 != attempt.reserve_v2_source_sha256
            {
                return Err("v2 reserve retained custody differs from journal".into());
            }
            let outcome_path = hold
                .reserve_outcome_path
                .as_ref()
                .ok_or("v2 reserve outcome path absent")?;
            if outcome_path.parent() != Some(directory.as_path())
                || !outcome_path
                    .file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| {
                        name == "submit.outcome.bin"
                            || name.starts_with("lookup-") && name.ends_with(".outcome.bin")
                    })
                || sha256_file(outcome_path)?
                    != hold
                        .reserve_outcome_sha256
                        .as_deref()
                        .ok_or("v2 reserve outcome digest absent")?
            {
                return Err("v2 reserve retained outcome differs from journal".into());
            }
            let anchor = hold
                .reserve_anchor
                .as_ref()
                .ok_or("v2 reserve original anchor absent")?;
            let original: Value = serde_json::from_slice(&bounded_regular_file(
                &outcome_path.with_extension("json"),
                131_072,
            )?)
            .map_err(|error| format!("v2 original outcome JSON: {error}"))?;
            if ReserveAnchor::from_confirmed(&original)? != *anchor {
                return Err("v2 original outcome differs from held anchor".into());
            }
            // Exact public op3 is the only permissible recovery probe.
            self.command_output(
                &self.config.mini,
                &[
                    "agent-reserve-lookup",
                    "--attempt",
                    directory.to_str().ok_or("v2 reserve directory UTF-8")?,
                ],
            )?;
            let receipt: Value = serde_json::from_slice(&bounded_regular_file(
                &directory.join("receipt.json"),
                4096,
            )?)
            .map_err(|error| format!("v2 retained receipt JSON: {error}"))?;
            if receipt.get("transactionId").and_then(Value::as_str)
                != Some(anchor.transaction_id.as_str())
                || receipt.get("eventId").and_then(Value::as_str) != Some(anchor.event_id.as_str())
                || receipt.get("acceptedCount").and_then(Value::as_str)
                    != Some(anchor.accepted_count.as_str())
                || receipt.get("imageBoundary").and_then(Value::as_str)
                    != Some(anchor.image_boundary.as_str())
                || receipt.get("reserveIndex").and_then(Value::as_str)
                    != Some(previous_accepted_index(&anchor.accepted_count)?.as_str())
            {
                return Err("v2 current historical receipt differs from original".into());
            }
            return Ok((id, anchor.clone()));
        }
        if !hold.reserve_confirmed
            || hold.reserve_refused
            || hold.reserve
                != self
                    .config
                    .dispatch_task
                    .as_ref()
                    .ok_or("dispatchTask absent")?
                    .reserve
        {
            return Err("dispatch audit lacks exact confirmed reserve hold".into());
        }
        let path = hold
            .reserve_attempt
            .as_ref()
            .ok_or("dispatch reserve attempt path absent")?;
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("dispatch reserve attempt name invalid")?;
        let encoded = name
            .strip_prefix("attempt-")
            .ok_or("dispatch reserve attempt name differs")?;
        let id = encoded
            .parse::<u64>()
            .map_err(|_| "dispatch reserve operation ID malformed")?;
        if encoded.len() != 16
            || *path != self.config.state_dir.join(format!("attempt-{id:016}"))
            || attempt
                .reserve_operation_id
                .is_some_and(|saved| saved != id)
        {
            return Err(
                "dispatch reserve attempt path/operation differs from retained origin".into(),
            );
        }
        let source_path = self.config.state_dir.join(format!("source-{id:016}.json"));
        if sha256_file(&source_path)?
            != hold
                .reserve_source_sha256
                .as_deref()
                .ok_or("dispatch reserve source digest absent")?
        {
            return Err("dispatch reserve signed source bytes changed".into());
        }
        let source: Value = serde_json::from_slice(&bounded_regular_file(&source_path, 131_072)?)
            .map_err(|e| format!("dispatch reserve source: {e}"))?;
        let task = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask absent")?;
        let payload = format!(
            "DREGG/APPLICATION/AGENT-DISPATCH-RESERVE/v1/{}",
            attempt.source_request_digest
        );
        if source.pointer("/grain/task").and_then(Value::as_str) != Some(task.task.as_str())
            || source.pointer("/grain/subject").and_then(Value::as_str)
                != Some(task.subject.as_str())
            || source
                .pointer("/grain/operation/type")
                .and_then(Value::as_str)
                != Some("reserve")
            || source
                .pointer("/grain/operation/amount")
                .and_then(Value::as_str)
                != Some(hold.reserve.as_str())
            || source
                .pointer("/grain/context/operationId")
                .and_then(Value::as_str)
                != Some(id.to_string().as_str())
            || source
                .pointer("/grain/context/payload")
                .and_then(Value::as_str)
                != Some(payload.as_str())
            || source
                .pointer("/grain/before/generation")
                .and_then(Value::as_str)
                != Some(hold.before_generation.as_str())
            || source
                .pointer("/grain/expectedTargetRoot")
                .and_then(Value::as_str)
                != Some(hold.before_target_root.as_str())
        {
            return Err("dispatch reserve source differs from exact held request".into());
        }
        let call_hash = hold
            .reserve_call_sha256
            .as_deref()
            .ok_or("dispatch reserve call digest absent")?;
        let outcome_path = hold
            .reserve_outcome_path
            .as_ref()
            .ok_or("dispatch reserve outcome path absent")?;
        let outcome_hash = hold
            .reserve_outcome_sha256
            .as_deref()
            .ok_or("dispatch reserve outcome digest absent")?;
        if sha256_file(&path.join("call.bin"))? != call_hash
            || sha256_file(outcome_path)? != outcome_hash
            || outcome_path.parent() != Some(path.as_path())
        {
            return Err("dispatch reserve retained native call/outcome changed".into());
        }
        let receipt_path = outcome_path.with_extension("json");
        let original: Value =
            serde_json::from_slice(&bounded_regular_file(&receipt_path, 131_072)?)
                .map_err(|e| format!("dispatch reserve receipt: {e}"))?;
        let anchor = hold
            .reserve_anchor
            .as_ref()
            .ok_or("dispatch reserve anchor absent")?;
        if ReserveAnchor::from_confirmed(&original)? != *anchor {
            return Err("dispatch reserve receipt differs from retained anchor".into());
        }
        let retry_result = next_retry_json(path)?;
        let mut args = vec![
            "retry",
            "--attempt",
            path.to_str().ok_or("dispatch reserve attempt path UTF-8")?,
            "--mode",
            "lookup",
        ];
        if let Some(socket) = &self.config.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("Host socket path UTF-8")?]);
        }
        self.command_output(&self.config.mini, &args)?;
        let current: Value = serde_json::from_slice(&bounded_regular_file(&retry_result, 131_072)?)
            .map_err(|e| format!("dispatch reserve lookup: {e}"))?;
        if current.get("type").and_then(Value::as_str) != Some("confirmed")
            || !matches!(
                current.get("confirmation").and_then(Value::as_str),
                Some("installed" | "replayed")
            )
            || ReserveAnchor::from_confirmed(&current)? != *anchor
        {
            return Err("dispatch reserve is absent from current native image".into());
        }
        Ok((id, anchor.clone()))
    }
    /// Retain one exact source-authored HTTP request before its separately
    /// paid AgentGrain reserve. The source digest is checked against the full
    /// request again by Mini's v2 dispatch admission; this receipt alone is
    /// never permission to send to fd3.
    fn verified_reverse_fixed_request(
        &self,
        route_name: &str,
        forward_operation_id: &str,
        fixed_request: &Value,
    ) -> Result<(application_api_tools::RoutePin, Value)> {
        decimal(forward_operation_id, "forward HTTP operation ID")?;
        let forward_id = forward_operation_id
            .parse::<u64>()
            .map_err(|_| "forward HTTP operation ID exceeds u64")?;
        let attempt = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("no retained forward API attempt")?;
        if !self.prompt_active && self.foreground_operation.is_none()
            || self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || attempt.operation_id != forward_id
            || attempt.route_name != route_name
            || attempt.phase != ApplicationApiPhase::DispatchStarted
            || sha256_file(&attempt.request_path)? != attempt.request_sha256
        {
            return Err("reverse reserve differs from active retained forward API call".into());
        }
        let route = self
            .config
            .tool_task
            .as_ref()
            .and_then(|task| {
                task.allowed_application_api_routes
                    .iter()
                    .find(|route| route.name == route_name)
            })
            .ok_or("reverse reserve route is not operator-pinned")?
            .clone();
        let dispatch = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask absent")?;
        if dispatch.operator_socket.is_none() || dispatch.reserve_signer.is_none() {
            return Err("reverse reserve lacks private operator socket or signer pin".into());
        }
        let retained: Value =
            serde_json::from_slice(&bounded_regular_file(&attempt.request_path, 262_144)?)
                .map_err(|error| format!("retained forward API request JSON: {error}"))?;
        if retained.get("operation_id").and_then(Value::as_str) != Some(forward_operation_id) {
            return Err("retained forward API operation ID changed".into());
        }
        let expected = json!({
            "base": {
                "issueIndex":route.dispatch_selectors.issue_index,
                "ticketResource":route.ticket_resource,
                "packageManifest":route.dispatch_selectors.package_manifest,
                "snapshotManifest":route.dispatch_selectors.snapshot_manifest,
                "sessionObserveCapability":route.dispatch_selectors.session_observe,
                "manifestObserveCapability":route.dispatch_selectors.manifest_observe,
                "enrollmentObserveCapability":route.dispatch_selectors.enrollment_observe,
                "http":application_api_tools::routed_reserve_http(
                    &retained, &route.signed_api_path)?,
            },
            "parentTask":self.config.task,
            "parentCapability":dispatch.parent_capability,
            "parentObserve":dispatch.parent_observe_capability,
            "purseTask":dispatch.task,
            "purseCapability":dispatch.capability,
            "purseObserve":dispatch.query_capability,
            "payerSubject":dispatch.subject,
            "reserveAmount":dispatch.reserve,
            "maximumCharge":dispatch.charge,
            "reserveOperationId":"0",
        });
        if fixed_request != &expected {
            return Err(
                "reverse reserve selectors or routed HTTP differ from operator intent".into(),
            );
        }
        Ok((route, retained))
    }

    /// Compare a v3 reverse reserve request with the exact durable forward
    /// HTTP and immutable event22/event27 route pins before any purse signer
    /// is opened. Fresh generations and roots are supplied later by the
    /// source-owned op80 plan and current Mini observations, never by this
    /// transport request or a copied v2 generation pin.
    fn verified_reverse_lifetime_fixed_request(
        &self,
        route_name: &str,
        forward_operation_id: &str,
        binding_sha256: &str,
        fixed_request: &Value,
    ) -> Result<(application_api_tools::LifetimeRoutePin, Value)> {
        decimal(forward_operation_id, "forward HTTP operation ID")?;
        let forward_id = forward_operation_id
            .parse::<u64>()
            .map_err(|_| "forward HTTP operation ID exceeds u64")?;
        let attempt = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("no retained forward API attempt")?;
        if (!self.prompt_active && self.foreground_operation.is_none())
            || self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || attempt.operation_id != forward_id
            || attempt.route_name != route_name
            || attempt.phase != ApplicationApiPhase::DispatchStarted
            || attempt.binding_sha256.as_deref() != Some(binding_sha256)
            || sha256_file(&attempt.request_path)? != attempt.request_sha256
        {
            return Err(
                "lifetime reverse reserve differs from active retained forward call".into(),
            );
        }
        let route = self
            .config
            .tool_task
            .as_ref()
            .and_then(|task| {
                task.allowed_application_lifetime_routes
                    .iter()
                    .find(|route| route.name == route_name)
            })
            .ok_or("lifetime reverse route is not operator-pinned")?
            .clone();
        let dispatch = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask absent")?;
        if dispatch.operator_socket.is_none() || dispatch.reserve_signer.is_none() {
            return Err("lifetime reserve lacks private operator socket or signer pin".into());
        }
        let retained: Value =
            serde_json::from_slice(&bounded_regular_file(&attempt.request_path, 262_144)?)
                .map_err(|error| format!("retained lifetime API request JSON: {error}"))?;
        if retained.get("type").and_then(Value::as_str) != Some("dispatch-v3")
            || retained.get("protocol").and_then(Value::as_str) != Some("mini-spk-agent-api-v3")
            || retained.get("operationId").and_then(Value::as_str) != Some(forward_operation_id)
            || retained.get("bindingSha256").and_then(Value::as_str) != Some(binding_sha256)
        {
            return Err("retained lifetime HTTP operation ID changed".into());
        }
        let expected = json!({
            "fixed": {
                "base": {
                    "issueIndex":route.dispatch_selectors.issue_index,
                    "ticketResource":route.ticket_resource,
                    "packageManifest":route.dispatch_selectors.package_manifest,
                    "snapshotManifest":route.dispatch_selectors.snapshot_manifest,
                    "sessionObserveCapability":route.dispatch_selectors.session_observe,
                    "manifestObserveCapability":route.dispatch_selectors.manifest_observe,
                    "enrollmentObserveCapability":route.dispatch_selectors.enrollment_observe,
                    "http":application_api_tools::routed_reserve_http(
                        &retained, &route.signed_api_path)?,
                },
                "parentTask":self.config.task,
                "parentCapability":dispatch.parent_capability,
                "parentObserve":dispatch.parent_observe_capability,
                "purseTask":dispatch.task,
                "purseCapability":dispatch.capability,
                "purseObserve":dispatch.query_capability,
                "payerSubject":dispatch.subject,
                "reserveAmount":dispatch.reserve,
                "maximumCharge":dispatch.charge,
                "reserveOperationId":"0",
            },
            "grantIssueIndex":route.grant_issue_index,
            "grantResource":route.grant_resource,
            "grantObserveCapability":route.grant_observe_capability,
        });
        if fixed_request != &expected {
            return Err("lifetime reserve selectors or HTTP differ from operator intent".into());
        }
        Ok((route, retained))
    }

    /// Source-owned event26 reserve for one retained v3 forward call. The
    /// exact op80 plan and current signed parent/purse are checked before the
    /// protected signer is opened. The client durably marks one public op2;
    /// any lost reply can only take the receipt-only op3 path.
    fn dispatch_reserve_v3(
        &mut self,
        route_name: &str,
        forward_operation_id: &str,
        binding_sha256: &str,
        worker_wall_seconds: u64,
        fixed_request: &Value,
    ) -> Result<Value> {
        let selected = self
            .config
            .commands
            .iter()
            .find(|command| command.name == "hermes-acp")
            .ok_or("selected Hermes worker command absent")?;
        let effective_wall = checked_lifetime_worker_wall(
            selected,
            worker_wall_seconds,
            self.prompt_active,
            self.child.is_some(),
            self.journal
                .child
                .as_ref()
                .map(|child| child.program.as_path()),
            self.foreground_operation.is_some(),
        )?;
        let (route, retained_forward) = self.verified_reverse_lifetime_fixed_request(
            route_name,
            forward_operation_id,
            binding_sha256,
            fixed_request,
        )?;
        if self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err("lifetime dispatch has an unresolved prior custody attempt".into());
        }
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let operator_socket = task
            .operator_socket
            .as_ref()
            .ok_or("operator socket absent")?;
        let public_socket = self
            .config
            .host_socket
            .clone()
            .ok_or("public socket absent")?;
        let signer = task
            .reserve_signer
            .as_ref()
            .ok_or("reserve signer absent")?;
        let parent = self.query()?;
        let parent_generation = parent
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("parent generation absent")?
            .to_owned();
        let parent_root = parent
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("parent physical root absent")?
            .to_owned();
        if !matches!(
            parent.pointer("/grain/status").and_then(Value::as_str),
            Some("3" | "4")
        ) || self.journal.prompt_witness.is_none()
        {
            return Err("lifetime parent prompt is not reserved".into());
        }
        let authority = self.dispatch()?;
        let mut purse = self.query_as(&authority)?;
        let status = purse
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("dispatch purse status absent")?;
        if status == "0" {
            self.check_not_cancelled()?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "dispatch attach",
                "agent lifetime dispatch attach",
                vec![],
            )?;
            purse = self.query_as(&authority)?;
        } else if status != "1" {
            return Err("dispatch purse is not available for lifetime reserve".into());
        }
        if purse.pointer("/grain/status").and_then(Value::as_str) != Some("1")
            || purse.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
        {
            return Err("lifetime purse is not running and unreserved".into());
        }
        let purse_generation = purse
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("purse generation absent")?
            .to_owned();
        let purse_root = purse
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("purse physical root absent")?
            .to_owned();
        let reserve_operation_id = self.next_id()?;
        let attempt_id = self.next_id()?;
        let mut source = fixed_request.clone();
        source["fixed"]["reserveOperationId"] = json!(reserve_operation_id.to_string());
        let source_path = self.config.state_dir.join(format!(
            "dispatch-lifetime-source-{reserve_operation_id:016}.json"
        ));
        write_new(
            &source_path,
            &serde_json::to_vec(&source)
                .map_err(|error| format!("lifetime source JSON: {error}"))?,
        )?;
        let directory = self
            .config
            .state_dir
            .join(format!("agent-lifetime-reserve-{attempt_id:016}"));
        fn path(value: &Path) -> Result<&str> {
            value
                .to_str()
                .ok_or_else(|| format!("{} is not UTF-8", value.display()))
        }
        self.check_not_cancelled()?;
        let plan_stdout = self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args([
                "agent-lifetime-reserve-plan",
                "--host",
                path(&self.config.host)?,
                "--config",
                path(&self.config.host_config)?,
                "--operator-socket",
                path(operator_socket)?,
                "--public-socket",
                path(&public_socket)?,
                "--request",
                path(&source_path)?,
                "--dir",
                path(&directory)?,
            ]);
            command
        })?;
        let read_json = |name: &str| -> Result<Value> {
            serde_json::from_slice(&bounded_regular_file(&directory.join(name), 2_097_152)?)
                .map_err(|error| format!("retained lifetime {name}: {error}"))
        };
        let request = read_json("request-inspected.json")?;
        let plan = read_json("plan-inspected.json")?;
        if plan_stdout != plan {
            return Err("lifetime plan stdout differs from retained source inspection".into());
        }
        let fixed_selectors = json!({
            "issueIndex":route.dispatch_selectors.issue_index,
            "ticketResource":route.ticket_resource,
            "packageManifest":route.dispatch_selectors.package_manifest,
            "snapshotManifest":route.dispatch_selectors.snapshot_manifest,
            "sessionObserve":route.dispatch_selectors.session_observe,
            "manifestObserve":route.dispatch_selectors.manifest_observe,
            "enrollmentObserve":route.dispatch_selectors.enrollment_observe,
            "parentTask":self.config.task,
            "parentCapability":task.parent_capability,
            "parentObserve":task.parent_observe_capability,
            "purseTask":task.task,
            "purseCapability":task.capability,
            "purseObserve":task.query_capability,
            "payerSubject":task.subject,
            "reserveAmount":task.reserve,
            "maximumCharge":task.charge,
            "grantIssueIndex":route.grant_issue_index,
            "grantResource":route.grant_resource,
            "grantObserveCapability":route.grant_observe_capability,
        });
        let context = plan
            .get("context")
            .ok_or("lifetime reserve context absent")?;
        let bindings = plan
            .get("bindings")
            .ok_or("lifetime reserve bindings absent")?;
        let get = |object: &Value, field: &str| -> Result<String> {
            object
                .get(field)
                .and_then(Value::as_str)
                .map(str::to_owned)
                .ok_or_else(|| format!("lifetime source {field} absent"))
        };
        let app_generation = get(context, "appGeneration")?;
        let session_generation = get(context, "sessionGeneration")?;
        let app_physical_root = get(bindings, "appPhysicalRoot")?;
        let session_physical_root = get(bindings, "sessionPhysicalRoot")?;
        application_api_tools::verify_lifetime_reserve_inspection(
            application_api_tools::LifetimeReserveInspection {
                route: &route,
                retained_forward: &retained_forward,
                expected_selectors: &fixed_selectors,
                reserve_operation_id: &reserve_operation_id.to_string(),
                signed_parent_generation: &parent_generation,
                signed_purse_generation: &purse_generation,
                signed_app_physical_root: &app_physical_root,
                signed_session_physical_root: &session_physical_root,
                signed_parent_physical_root: &parent_root,
                signed_purse_physical_root: &purse_root,
                request: &request,
                plan: &plan,
            },
        )?;
        if request.get("canonicalRequestHex") != plan.get("canonicalRequestHex")
            || request.get("http") != plan.get("http")
            || get(context, "appGeneration")? != app_generation
            || get(context, "sessionGeneration")? != session_generation
        {
            return Err("lifetime reserve request changed during planning".into());
        }
        let canonical_http = dispatch_custody::decode_hex(
            plan.get("canonicalHttpHex")
                .and_then(Value::as_str)
                .ok_or("lifetime canonical HTTP absent")?,
        )?;
        if canonical_http.is_empty() || canonical_http.len() > 10 * 1024 * 1024 {
            return Err("lifetime canonical HTTP exceeds retained bound".into());
        }
        let request_path = self
            .config
            .state_dir
            .join(format!("dispatch-{attempt_id:016}.canonical-request"));
        write_new(&request_path, &canonical_http)?;
        let request_sha256 = sha256_file(&request_path)?;
        let claims = application_api_tools::LifetimeCurrentClaims {
            app_generation: app_generation.clone(),
            session_generation: session_generation.clone(),
            parent_generation: parent_generation.clone(),
            purse_generation: purse_generation.clone(),
            app_physical_root: app_physical_root.clone(),
            session_physical_root: session_physical_root.clone(),
            parent_physical_root: parent_root.clone(),
            purse_physical_root: purse_root.clone(),
        };
        let fingerprint = application_api_tools::lifetime_operation_fingerprint(
            binding_sha256,
            &claims,
            forward_operation_id,
            &request_sha256,
        )?;
        let slots = plan
            .get("slots")
            .and_then(Value::as_array)
            .ok_or("lifetime reserve slots absent")?;
        let signers = lifetime_purse_signers(slots, signer, &task.custody_key)?;
        let approval = json!({
            "type":"minidregg-agent-lifetime-reserve-approval-v1",
            "requestSha256":sha256_file(&directory.join("request.bin"))?,
            "planSha256":sha256_file(&directory.join("plan.bin"))?,
            "fixedSelectors":fixed_selectors,
            "context":context,
            "bindings":bindings,
            "canonicalHttpHex":plan.get("canonicalHttpHex"),
            "signers":signers,
        });
        let approval_path = self.config.state_dir.join(format!(
            "dispatch-lifetime-approval-{reserve_operation_id:016}.json"
        ));
        write_new(
            &approval_path,
            &serde_json::to_vec(&approval)
                .map_err(|error| format!("lifetime reserve approval JSON: {error}"))?,
        )?;
        let forward = self
            .journal
            .application_api_attempt
            .as_mut()
            .ok_or("lifetime forward attempt disappeared")?;
        if forward.operation_id.to_string() != forward_operation_id
            || forward.operation_fingerprint.is_some()
        {
            return Err("lifetime forward fingerprint was already allocated".into());
        }
        forward.operation_fingerprint = Some(fingerprint.clone());
        self.journal.dispatch_attempt = Some(DispatchAttempt {
            id: attempt_id,
            http_operation_id: forward_operation_id.into(),
            parent_generation: parent_generation.clone(),
            parent_root: parent_root.clone(),
            request_path,
            request_bytes: canonical_http.len(),
            request_sha256,
            source_request_digest: get(context, "requestDigest")?,
            reserve_operation_id: Some(reserve_operation_id),
            reserve_v2_dir: None,
            reserve_v2_request_sha256: None,
            reserve_v2_plan_sha256: None,
            reserve_v2_source_sha256: None,
            lifetime: Some(LifetimeDispatchCustody {
                route_name: route_name.into(),
                worker_wall_seconds: Some(effective_wall),
                original_issue_index: route.dispatch_selectors.issue_index.clone(),
                original_issue_receipt: route.original_issue_receipt.clone(),
                grant_issue_receipt: route.grant_issue_receipt.clone(),
                grant_resource: route.grant_resource.clone(),
                grant_issue_index: route.grant_issue_index.clone(),
                grant_digest: route.grant_digest.clone(),
                grant_initialized_root: route.grant_initialized_root.clone(),
                source_path: source_path.clone(),
                source_sha256: sha256_file(&source_path)?,
                reserve_dir: directory.clone(),
                reserve_request_sha256: sha256_file(&directory.join("request.bin"))?,
                reserve_plan_sha256: sha256_file(&directory.join("plan.bin"))?,
                context_hex: get(context, "canonicalHex")?,
                app_generation,
                session_generation,
                parent_generation: parent_generation.clone(),
                purse_generation,
                app_physical_root,
                session_physical_root,
                parent_physical_root: parent_root,
                pre_reserve_purse_physical_root: purse_root,
                reserve_index: None,
                reserve_receipt: None,
                post_reserve_purse_physical_root: None,
                paid_dir: None,
                paid_plan_sha256: None,
                paid_ingress_sha256: None,
                committed_frame_sha256: None,
                committed_receipt: None,
            }),
            dispatch_generation: None,
            dispatch_post_root: None,
            no_send_release_started: false,
            audited_charge: None,
            settlement: None,
            send_started: false,
            committed_dispatch_transaction: None,
            committed_dispatch_event: None,
            committed_permit_sha256: None,
            response_sha256: None,
        });
        self.save()?;
        self.mark_hold_as(
            AuthoritySlot::Dispatch,
            &authority,
            &task.reserve,
            &task.charge,
        )?;
        self.check_not_cancelled()?;
        self.work_output(
            &self.config.mini,
            &[
                "agent-lifetime-reserve-seal",
                "--attempt",
                path(&directory)?,
                "--approval",
                path(&approval_path)?,
            ],
        )
        .map_err(|error| format!("lifetime reserve seal: {error}"))?;
        self.check_not_cancelled()?;
        self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args([
                "agent-lifetime-reserve-submit",
                "--attempt",
                path(&directory)?,
            ]);
            command
        })?;
        let receipt = read_json("receipt.json")?;
        let original = read_json("submit.outcome.json")?;
        let anchor = ReserveAnchor::from_confirmed(&original)?;
        if receipt.get("transactionId").and_then(Value::as_str)
            != Some(anchor.transaction_id.as_str())
            || receipt.get("eventId").and_then(Value::as_str) != Some(anchor.event_id.as_str())
            || receipt.get("acceptedCount").and_then(Value::as_str)
                != Some(anchor.accepted_count.as_str())
            || receipt.get("imageBoundary").and_then(Value::as_str)
                != Some(anchor.image_boundary.as_str())
            || receipt.get("reserveIndex").and_then(Value::as_str)
                != Some(previous_accepted_index(&anchor.accepted_count)?.as_str())
        {
            return Err("lifetime reserve receipt differs from native outcome".into());
        }
        let hold = self
            .journal
            .dispatch_hold
            .as_mut()
            .ok_or("lifetime hold disappeared")?;
        hold.reserve_attempt = Some(directory.clone());
        hold.reserve_confirmed = true;
        hold.reserve_boundary = Some(anchor.image_boundary.clone());
        hold.reserve_call_sha256 = Some(sha256_file(&directory.join("call.bin"))?);
        hold.reserve_source_sha256 = Some(sha256_file(&source_path)?);
        hold.reserve_outcome_path = Some(directory.join("submit.outcome.bin"));
        hold.reserve_outcome_sha256 = Some(sha256_file(&directory.join("submit.outcome.bin"))?);
        hold.reserve_anchor = Some(anchor.clone());
        let saved = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("lifetime attempt disappeared")?;
        saved
            .lifetime
            .as_mut()
            .ok_or("lifetime custody absent")?
            .reserve_index = receipt
            .get("reserveIndex")
            .and_then(Value::as_str)
            .map(str::to_owned);
        saved.lifetime.as_mut().unwrap().reserve_receipt = Some(anchor.clone());
        self.save()?;
        // This lookup is read-only and requires the exact historical receipt.
        self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args([
                "agent-lifetime-reserve-lookup",
                "--attempt",
                path(&directory)?,
            ]);
            command
        })?;
        let state = self.query_as(&authority)?;
        if state.pointer("/grain/status").and_then(Value::as_str) != Some("3")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(task.reserve.as_str())
        {
            return Err("lifetime reserve lacks signed held purse".into());
        }
        let generation = state
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("held purse generation absent")?
            .to_owned();
        let post_root = state
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("held purse root absent")?
            .to_owned();
        let saved = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("lifetime attempt disappeared")?;
        saved.dispatch_generation = Some(generation);
        saved.dispatch_post_root = Some(post_root.clone());
        saved
            .lifetime
            .as_mut()
            .ok_or("lifetime custody absent")?
            .post_reserve_purse_physical_root = Some(post_root);
        self.save()?;
        let reserve_plan_hex =
            checked_lifetime_reserve_plan_hex(&plan, &directory.join("plan.bin"))?;
        Ok(json!({"type":"dispatch-reserved-v3",
            "attemptId":attempt_id.to_string(),
            "httpOperationId":forward_operation_id,
            "bindingSha256":binding_sha256,
            "operationFingerprint":fingerprint,
            "currentClaims":claims,
            "reserveOperationId":reserve_operation_id.to_string(),
            "fixedRequestHex":request.get("canonicalRequestHex"),
            "reservePlanHex":reserve_plan_hex,
            "effectiveWorkerWallSeconds":effective_wall.to_string(),
            "contextHex":context.get("canonicalHex"),
            "reserveIndex":receipt.get("reserveIndex"),
            "reserveReceipt":anchor}))
    }

    /// Source-owned v2 reserve for exactly the active forward API call. The
    /// private op58/59 phases expose and seal a plan; only the marked public
    /// op2 phase can mutate Mini. A lost op2 reply remains in custody for op3
    /// lookup and never triggers a second submit.
    fn dispatch_reserve_v2(
        &mut self,
        route_name: &str,
        forward_operation_id: &str,
        fixed_request: &Value,
    ) -> Result<Value> {
        let (route, retained_forward) =
            self.verified_reverse_fixed_request(route_name, forward_operation_id, fixed_request)?;
        if self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err("dispatch reserve has an unresolved prior custody attempt".into());
        }
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let operator_socket = task
            .operator_socket
            .as_ref()
            .ok_or("operator socket absent")?;
        let public_socket = self
            .config
            .host_socket
            .clone()
            .ok_or("public socket absent")?;
        let signer = task
            .reserve_signer
            .as_ref()
            .ok_or("reserve signer absent")?;
        let parent = self.query()?;
        let parent_generation = parent
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("parent generation absent")?
            .to_owned();
        let parent_root = parent
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("parent root absent")?
            .to_owned();
        if route.parent_task != self.config.task || route.parent_generation != parent_generation {
            return Err("v2 reserve parent differs from the operator route".into());
        }
        if !matches!(
            parent.pointer("/grain/status").and_then(Value::as_str),
            Some("3" | "4")
        ) || self.journal.prompt_witness.is_none()
        {
            return Err("parent prompt is not reserved for API dispatch".into());
        }
        let authority = self.dispatch()?;
        let status = self
            .query_as(&authority)?
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("dispatch purse status absent")?
            .to_owned();
        if status == "0" {
            self.check_not_cancelled()?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "dispatch attach",
                "agent app dispatch attach",
                vec![],
            )?;
        } else if status != "1" {
            return Err("dispatch purse is not available for a fresh reserve".into());
        }
        let reserve_operation_id = self.next_id()?;
        let attempt_id = self.next_id()?;
        let mut source = fixed_request.clone();
        source["reserveOperationId"] = json!(reserve_operation_id.to_string());
        let source_path = self.config.state_dir.join(format!(
            "dispatch-reserve-source-{reserve_operation_id:016}.json"
        ));
        write_new(
            &source_path,
            &serde_json::to_vec(&source)
                .map_err(|error| format!("dispatch reserve source JSON: {error}"))?,
        )?;
        let directory = self
            .config
            .state_dir
            .join(format!("agent-reserve-{attempt_id:016}"));
        fn string(path: &Path) -> Result<&str> {
            path.to_str()
                .ok_or_else(|| format!("{} is not UTF-8", path.display()))
        }
        self.check_not_cancelled()?;
        let plan_stdout = self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args([
                "agent-reserve-plan",
                "--host",
                string(&self.config.host)?,
                "--config",
                string(&self.config.host_config)?,
                "--operator-socket",
                string(operator_socket)?,
                "--public-socket",
                string(&public_socket)?,
                "--request",
                string(&source_path)?,
                "--dir",
                string(&directory)?,
            ]);
            command
        })?;
        let read_json = |name: &str| -> Result<Value> {
            serde_json::from_slice(&bounded_regular_file(&directory.join(name), 2_097_152)?)
                .map_err(|error| format!("retained {name} JSON: {error}"))
        };
        let request_view = read_json("request-inspected.json")?;
        let plan_view = read_json("plan-inspected.json")?;
        if plan_stdout != plan_view
            || request_view.get("type").and_then(Value::as_str)
                != Some("application-agent-reserve-request-v2")
            || plan_view.get("type").and_then(Value::as_str)
                != Some("application-agent-reserve-plan-v2")
            || request_view.get("base") != source.get("base")
            || request_view.get("reserveOperationId") != source.get("reserveOperationId")
            || request_view.get("parentTask") != source.get("parentTask")
            || request_view.get("parentCapability") != source.get("parentCapability")
            || request_view.get("parentObserve") != source.get("parentObserve")
            || request_view.get("purseTask") != source.get("purseTask")
            || request_view.get("purseCapability") != source.get("purseCapability")
            || request_view.get("purseObserve") != source.get("purseObserve")
            || request_view.get("payerSubject") != source.get("payerSubject")
            || request_view.get("reserveAmount") != source.get("reserveAmount")
            || request_view.get("maximumCharge") != source.get("maximumCharge")
            || request_view.get("canonicalRequestHex") != plan_view.get("canonicalRequestHex")
        {
            return Err("source reserve plan differs from exact protected request".into());
        }
        application_api_tools::verify_routed_reserve_http(
            &retained_forward,
            &route.signed_api_path,
            &request_view,
        )?;
        let context = plan_view
            .get("context")
            .ok_or("source reserve context absent")?;
        let same = |name: &str, expected: &str| -> Result<()> {
            if context.get(name).and_then(Value::as_str) != Some(expected) {
                return Err(format!(
                    "source reserve {name} differs from operator/current pin"
                ));
            }
            Ok(())
        };
        same("appResource", &route.app_resource)?;
        same("appGeneration", &route.app_generation)?;
        same("sessionResource", &route.session_resource)?;
        same("sessionGeneration", &route.session_generation)?;
        same("participantSubject", &route.participant_subject)?;
        same("ticketResource", &route.ticket_resource)?;
        same("parentTask", &self.config.task)?;
        same("parentGeneration", &parent_generation)?;
        same("purseTask", &task.task)?;
        same("payerSubject", &task.subject)?;
        same("reserveAmount", &task.reserve)?;
        same("maximumCharge", &task.charge)?;
        same("reserveOperationId", &reserve_operation_id.to_string())?;
        same("httpOperationId", forward_operation_id)?;
        if context.get("requestDigest") != request_view.get("httpRequestDigest") {
            return Err("source reserve context changed exact HTTP digest".into());
        }
        let expected_selectors = json!({
            "issueIndex":route.dispatch_selectors.issue_index,
            "ticketResource":route.ticket_resource,
            "packageManifest":route.dispatch_selectors.package_manifest,
            "snapshotManifest":route.dispatch_selectors.snapshot_manifest,
            "sessionObserve":route.dispatch_selectors.session_observe,
            "manifestObserve":route.dispatch_selectors.manifest_observe,
            "enrollmentObserve":route.dispatch_selectors.enrollment_observe,
            "parentTask":self.config.task,
            "parentCapability":task.parent_capability,
            "parentObserve":task.parent_observe_capability,
            "purseTask":task.task,
            "purseCapability":task.capability,
            "purseObserve":task.query_capability,
            "payerSubject":task.subject,
            "reserveAmount":task.reserve,
            "maximumCharge":task.charge,
        });
        if plan_view.get("fixedSelectors") != Some(&expected_selectors) {
            return Err("source reserve selectors differ from operator pins".into());
        }
        let canonical_http_hex = plan_view
            .get("canonicalHttpHex")
            .and_then(Value::as_str)
            .ok_or("source canonical HTTP absent")?;
        let canonical_http = dispatch_custody::decode_hex(canonical_http_hex)?;
        if canonical_http.is_empty() || canonical_http.len() > 10 * 1024 * 1024 {
            return Err("source canonical HTTP exceeds retained bound".into());
        }
        let request_path = self
            .config
            .state_dir
            .join(format!("dispatch-{attempt_id:016}.canonical-request"));
        write_new(&request_path, &canonical_http)?;
        let slots = plan_view
            .get("slots")
            .and_then(Value::as_array)
            .ok_or("source reserve slots absent")?;
        if slots.len() != 1 {
            return Err("first agent purse profile requires exactly one reserve signer".into());
        }
        let slot = &slots[0];
        let slot_field = |key: &str| -> Result<&str> {
            slot.get(key)
                .and_then(Value::as_str)
                .ok_or_else(|| format!("source reserve slot lacks {key}"))
        };
        let signing = slot
            .get("signing")
            .ok_or("source reserve signing header absent")?;
        if slot_field("role")? != signer.role
            || slot_field("index")? != signer.index
            || signing.get("decoded").and_then(Value::as_bool) != Some(true)
            || signing.get("keyId").and_then(Value::as_str) != Some(&signer.key_id)
            || signing.get("keyEpoch").and_then(Value::as_str) != Some(&signer.key_epoch)
            || signing.get("algorithm").and_then(Value::as_str) != Some("1")
        {
            return Err("source reserve signer differs from operator enrollment pin".into());
        }
        let header = dispatch_custody::decode_hex(slot_field("headerHex")?)?;
        let approval = json!({
            "type":"minidregg-agent-reserve-approval-v1",
            "requestSha256":sha256_file(&directory.join("request.bin"))?,
            "planSha256":sha256_file(&directory.join("plan.bin"))?,
            "fixedSelectors":expected_selectors,
            "signers":[{"role":signer.role,"index":signer.index,
                "keyId":signer.key_id,"keyEpoch":signer.key_epoch,
                "publicKey":signer.public_key,"headerSha256":sha256_bytes(&header)?,
                "keyPath":task.custody_key}],
        });
        let approval_path = self.config.state_dir.join(format!(
            "dispatch-reserve-approval-{reserve_operation_id:016}.json"
        ));
        write_new(
            &approval_path,
            &serde_json::to_vec(&approval)
                .map_err(|error| format!("reserve approval JSON: {error}"))?,
        )?;
        self.journal.dispatch_attempt = Some(DispatchAttempt {
            id: attempt_id,
            http_operation_id: forward_operation_id.into(),
            parent_generation: parent_generation.clone(),
            parent_root: parent_root.clone(),
            request_path: request_path.clone(),
            request_bytes: canonical_http.len(),
            request_sha256: sha256_file(&request_path)?,
            source_request_digest: context
                .get("requestDigest")
                .and_then(Value::as_str)
                .ok_or("source request digest absent")?
                .into(),
            reserve_operation_id: Some(reserve_operation_id),
            reserve_v2_dir: Some(directory.clone()),
            reserve_v2_request_sha256: Some(sha256_file(&directory.join("request.bin"))?),
            reserve_v2_plan_sha256: Some(sha256_file(&directory.join("plan.bin"))?),
            reserve_v2_source_sha256: Some(sha256_file(&source_path)?),
            lifetime: None,
            dispatch_generation: None,
            dispatch_post_root: None,
            no_send_release_started: false,
            audited_charge: None,
            settlement: None,
            send_started: false,
            committed_dispatch_transaction: None,
            committed_dispatch_event: None,
            committed_permit_sha256: None,
            response_sha256: None,
        });
        self.save()?;
        self.mark_hold_as(
            AuthoritySlot::Dispatch,
            &authority,
            &task.reserve,
            &task.charge,
        )?;
        self.check_not_cancelled()?;
        self.work_output(
            &self.config.mini,
            &[
                "agent-reserve-seal",
                "--attempt",
                string(&directory)?,
                "--approval",
                string(&approval_path)?,
            ],
        )
        .map_err(|error| format!("agent reserve seal: {error}"))?;
        // The op2 marker is written by the client before any public send. A
        // failure after this point is uncertain and can only use exact op3.
        self.check_not_cancelled()?;
        self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args(["agent-reserve-submit", "--attempt", string(&directory)?]);
            command
        })?;
        let receipt = read_json("receipt.json")?;
        let original = read_json("submit.outcome.json")?;
        let anchor = ReserveAnchor::from_confirmed(&original)?;
        if receipt.get("transactionId").and_then(Value::as_str)
            != Some(anchor.transaction_id.as_str())
            || receipt.get("eventId").and_then(Value::as_str) != Some(anchor.event_id.as_str())
            || receipt.get("acceptedCount").and_then(Value::as_str)
                != Some(anchor.accepted_count.as_str())
            || receipt.get("imageBoundary").and_then(Value::as_str)
                != Some(anchor.image_boundary.as_str())
        {
            return Err("v2 reserve custody receipt differs from original native outcome".into());
        }
        let reserve_index = receipt
            .get("reserveIndex")
            .and_then(Value::as_str)
            .ok_or("reserve receipt index absent")?;
        if previous_accepted_index(&anchor.accepted_count)?.as_str() != reserve_index {
            return Err("reserve receipt history index differs from accepted count".into());
        }
        let hold = self
            .journal
            .dispatch_hold
            .as_mut()
            .ok_or("v2 reserve hold disappeared")?;
        hold.reserve_attempt = Some(directory.clone());
        hold.reserve_confirmed = true;
        hold.reserve_boundary = Some(anchor.image_boundary.clone());
        hold.reserve_call_sha256 = Some(sha256_file(&directory.join("call.bin"))?);
        hold.reserve_source_sha256 = Some(sha256_file(&source_path)?);
        hold.reserve_outcome_path = Some(directory.join("submit.outcome.bin"));
        hold.reserve_outcome_sha256 = Some(sha256_file(&directory.join("submit.outcome.bin"))?);
        hold.reserve_anchor = Some(anchor.clone());
        self.save()?;
        // This op3 is receipt-only. It cannot submit a second reserve, and
        // the client requires the exact historical anchor.
        self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args(["agent-reserve-lookup", "--attempt", string(&directory)?]);
            command
        })?;
        let state = self.query_as(&authority)?;
        if state.pointer("/grain/status").and_then(Value::as_str) != Some("3")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(task.reserve.as_str())
        {
            return Err("confirmed v2 reserve lacks signed held purse".into());
        }
        let dispatch_generation = state
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("v2 purse generation absent")?
            .to_owned();
        let dispatch_post_root = state
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("v2 purse root absent")?
            .to_owned();
        let attempt = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("v2 reserve attempt disappeared")?;
        attempt.dispatch_generation = Some(dispatch_generation);
        attempt.dispatch_post_root = Some(dispatch_post_root);
        self.save()?;
        let fixed_request_hex = request_view
            .get("canonicalRequestHex")
            .and_then(Value::as_str)
            .ok_or("v2 canonical fixed request absent")?;
        let context_hex = context
            .get("canonicalHex")
            .and_then(Value::as_str)
            .ok_or("v2 canonical context absent")?;
        Ok(
            json!({"type":"dispatch-reserved-v2", "attemptId":attempt_id.to_string(),
            "httpOperationId":forward_operation_id,
            "reserveOperationId":reserve_operation_id.to_string(),
            "fixedRequestHex":fixed_request_hex,
            "contextHex":context_hex,
            "reserveIndex":reserve_index,"reserveReceipt":anchor}),
        )
    }

    fn dispatch_inspect_v2(&self, route_name: &str, forward_operation_id: &str) -> Result<Value> {
        decimal(forward_operation_id, "forward HTTP operation ID")?;
        let forward_id = forward_operation_id
            .parse::<u64>()
            .map_err(|_| "forward HTTP operation ID exceeds u64")?;
        let forward = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("no retained forward API attempt")?;
        if forward.operation_id != forward_id
            || forward.route_name != route_name
            || sha256_file(&forward.request_path)? != forward.request_sha256
        {
            return Err("reverse inspection differs from retained forward call".into());
        }
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("no retained v2 dispatch attempt")?;
        let directory = attempt
            .reserve_v2_dir
            .as_ref()
            .ok_or("retained dispatch is not a v2 reserve")?;
        if attempt.http_operation_id != forward_operation_id {
            return Err("v2 dispatch attempt differs from forward operation".into());
        }
        let hold = self
            .journal
            .dispatch_hold
            .as_ref()
            .ok_or("v2 dispatch hold absent")?;
        if !hold.reserve_confirmed || attempt.dispatch_generation.is_none() {
            return Ok(json!({"type":"dispatch-reserve-uncertain-v2",
                "httpOperationId":forward_operation_id,
                "attemptId":attempt.id.to_string()}));
        }
        let (reserve_id, anchor) = self.verified_dispatch_reserve_hold(attempt, hold)?;
        let request: Value = serde_json::from_slice(&bounded_regular_file(
            &directory.join("request-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("v2 inspected request JSON: {error}"))?;
        let plan: Value = serde_json::from_slice(&bounded_regular_file(
            &directory.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("v2 inspected plan JSON: {error}"))?;
        if sha256_file(&directory.join("request.bin"))?
            != attempt
                .reserve_v2_request_sha256
                .as_deref()
                .ok_or("v2 request hash absent")?
            || sha256_file(&directory.join("plan.bin"))?
                != attempt
                    .reserve_v2_plan_sha256
                    .as_deref()
                    .ok_or("v2 plan hash absent")?
            || request.get("canonicalRequestHex") != plan.get("canonicalRequestHex")
            || request
                .pointer("/base/http/operationId")
                .and_then(Value::as_str)
                != Some(forward_operation_id)
            || plan
                .pointer("/context/reserveOperationId")
                .and_then(Value::as_str)
                != Some(reserve_id.to_string().as_str())
        {
            return Err("v2 inspected request or plan differs from custody".into());
        }
        Ok(json!({"type":"dispatch-reserved-v2",
            "attemptId":attempt.id.to_string(),
            "httpOperationId":forward_operation_id,
            "reserveOperationId":reserve_id.to_string(),
            "fixedRequestHex":request.get("canonicalRequestHex")
                .and_then(Value::as_str).ok_or("v2 fixed request absent")?,
            "contextHex":plan.pointer("/context/canonicalHex")
                .and_then(Value::as_str).ok_or("v2 context absent")?,
            "reserveIndex":previous_accepted_index(&anchor.accepted_count)?,
            "reserveReceipt":anchor}))
    }

    fn dispatch_inspect_v3(&self, route_name: &str, forward_operation_id: &str) -> Result<Value> {
        decimal(forward_operation_id, "lifetime forward operation ID")?;
        let forward_id = forward_operation_id
            .parse::<u64>()
            .map_err(|_| "lifetime forward operation ID exceeds u64")?;
        let forward = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("lifetime forward attempt absent")?;
        if forward.operation_id != forward_id
            || forward.route_name != route_name
            || sha256_file(&forward.request_path)? != forward.request_sha256
        {
            return Err("lifetime inspect differs from retained forward call".into());
        }
        let binding = forward
            .binding_sha256
            .as_deref()
            .ok_or("lifetime stable Hello binding absent")?;
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("lifetime reserve attempt absent")?;
        let lifetime = attempt
            .lifetime
            .as_ref()
            .ok_or("retained dispatch is not a lifetime reserve")?;
        let worker_wall = lifetime
            .worker_wall_seconds
            .ok_or("retained lifetime worker wall absent")?;
        if lifetime.route_name != route_name
            || attempt.http_operation_id != forward_operation_id
            || sha256_file(&attempt.request_path)? != attempt.request_sha256
            || sha256_file(&lifetime.source_path)? != lifetime.source_sha256
            || sha256_file(&lifetime.reserve_dir.join("request.bin"))?
                != lifetime.reserve_request_sha256
            || sha256_file(&lifetime.reserve_dir.join("plan.bin"))? != lifetime.reserve_plan_sha256
        {
            return Err("lifetime reserve source custody differs".into());
        }
        let current = application_api_tools::LifetimeCurrentClaims {
            app_generation: lifetime.app_generation.clone(),
            session_generation: lifetime.session_generation.clone(),
            parent_generation: lifetime.parent_generation.clone(),
            purse_generation: lifetime.purse_generation.clone(),
            app_physical_root: lifetime.app_physical_root.clone(),
            session_physical_root: lifetime.session_physical_root.clone(),
            parent_physical_root: lifetime.parent_physical_root.clone(),
            purse_physical_root: lifetime.pre_reserve_purse_physical_root.clone(),
        };
        let fingerprint = application_api_tools::lifetime_operation_fingerprint(
            binding,
            &current,
            forward_operation_id,
            &attempt.request_sha256,
        )?;
        if forward.operation_fingerprint.as_deref() != Some(fingerprint.as_str()) {
            return Err("lifetime operation fingerprint differs from journal".into());
        }
        let Some(hold) = self.journal.dispatch_hold.as_ref() else {
            return Ok(json!({"type":"dispatch-reserve-uncertain-v3",
                "httpOperationId":forward_operation_id,
                "bindingSha256":binding,
                "operationFingerprint":fingerprint,
                "attemptId":attempt.id.to_string()}));
        };
        if !hold.reserve_confirmed
            || lifetime.reserve_receipt.is_none()
            || attempt.dispatch_generation.is_none()
        {
            return Ok(json!({"type":"dispatch-reserve-uncertain-v3",
                "httpOperationId":forward_operation_id,
                "bindingSha256":binding,
                "operationFingerprint":fingerprint,
                "attemptId":attempt.id.to_string()}));
        }
        let (reserve_id, anchor) = self.verified_dispatch_reserve_hold(attempt, hold)?;
        let request: Value = serde_json::from_slice(&bounded_regular_file(
            &lifetime.reserve_dir.join("request-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("lifetime request inspection: {error}"))?;
        let plan: Value = serde_json::from_slice(&bounded_regular_file(
            &lifetime.reserve_dir.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("lifetime plan inspection: {error}"))?;
        if plan
            .pointer("/context/reserveOperationId")
            .and_then(Value::as_str)
            != Some(reserve_id.to_string().as_str())
            || plan
                .pointer("/context/canonicalHex")
                .and_then(Value::as_str)
                != Some(lifetime.context_hex.as_str())
            || plan.get("canonicalRequestHex") != request.get("canonicalRequestHex")
        {
            return Err("lifetime retained plan differs from reserve custody".into());
        }
        let plan_hex =
            checked_lifetime_reserve_plan_hex(&plan, &lifetime.reserve_dir.join("plan.bin"))?;
        Ok(json!({"type":"dispatch-reserved-v3",
            "attemptId":attempt.id.to_string(),
            "httpOperationId":forward_operation_id,
            "bindingSha256":binding,
            "operationFingerprint":fingerprint,
            "currentClaims":current,
            "reserveOperationId":reserve_id.to_string(),
            "fixedRequestHex":request.get("canonicalRequestHex"),
            "reservePlanHex":plan_hex,
            "effectiveWorkerWallSeconds":worker_wall.to_string(),
            "contextHex":lifetime.context_hex,
            "reserveIndex":lifetime.reserve_index,
            "reserveReceipt":anchor}))
    }

    /// Return only detached payer signatures for this exact v3 source plan.
    /// Resident app/grant keys never enter this process; op79 assembly and
    /// fresh op76 delivery remain the resident's separate custody phase.
    fn dispatch_sign_payer_v3(
        &mut self,
        route_name: &str,
        forward_operation_id: &str,
        attempt_id: &str,
        paid_plan_hex: &str,
        resident_inspection: &Value,
        operation_fingerprint: &str,
    ) -> Result<Value> {
        let confirmed = self.dispatch_inspect_v3(route_name, forward_operation_id)?;
        if confirmed.get("type").and_then(Value::as_str) != Some("dispatch-reserved-v3")
            || confirmed.get("attemptId").and_then(Value::as_str) != Some(attempt_id)
            || confirmed
                .get("operationFingerprint")
                .and_then(Value::as_str)
                != Some(operation_fingerprint)
        {
            return Err("lifetime payer lacks exact confirmed reserve/fingerprint".into());
        }
        if self.cancelled.load(Ordering::SeqCst)
            || (!self.prompt_active && self.foreground_operation.is_none())
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
        {
            return Err("lifetime parent no longer permits payer signing".into());
        }
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let signer = task
            .reserve_signer
            .as_ref()
            .ok_or("protected payer signer absent")?;
        let route = self
            .config
            .tool_task
            .as_ref()
            .and_then(|tool| {
                tool.allowed_application_lifetime_routes
                    .iter()
                    .find(|route| route.name == route_name)
            })
            .ok_or("lifetime route absent")?
            .clone();
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("lifetime dispatch attempt absent")?;
        let lifetime = attempt.lifetime.as_ref().ok_or("lifetime custody absent")?;
        if attempt.id.to_string() != attempt_id
            || attempt.send_started
            || attempt.no_send_release_started
            || attempt.audited_charge.is_some()
            || lifetime.paid_dir.is_some()
        {
            return Err("lifetime payer attempt is already used or unresolved".into());
        }
        let reserve_dir = lifetime.reserve_dir.clone();
        let post_purse_root = lifetime
            .post_reserve_purse_physical_root
            .as_ref()
            .ok_or("lifetime signed post-reserve purse root absent")?
            .clone();
        let state = self.query_as(&self.dispatch()?)?;
        if state.pointer("/grain/status").and_then(Value::as_str) != Some("3")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(task.reserve.as_str())
            || state.get("targetRoot").and_then(Value::as_str) != Some(post_purse_root.as_str())
        {
            return Err("lifetime payer lacks current signed held purse".into());
        }
        if paid_plan_hex.len() > 2 * 10 * 1024 * 1024 {
            return Err("lifetime paid plan exceeds native bound".into());
        }
        let resident_bytes = dispatch_custody::decode_hex(paid_plan_hex)?;
        if resident_bytes.is_empty() {
            return Err("lifetime paid plan is empty".into());
        }
        let directory = self
            .config
            .state_dir
            .join(format!("agent-lifetime-paid-{attempt_id}"));
        fn path(value: &Path) -> Result<&str> {
            value
                .to_str()
                .ok_or_else(|| format!("{} is not UTF-8", value.display()))
        }
        self.check_not_cancelled()?;
        let current = self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args([
                "agent-lifetime-paid-plan",
                "--reserve-attempt",
                path(&reserve_dir)?,
                "--grant-attempt",
                path(&route.grant_attempt_dir)?,
                "--dir",
                path(&directory)?,
            ]);
            command
        })?;
        if sha256_file(&directory.join("plan.bin"))? != sha256_bytes(&resident_bytes)?
            || bounded_regular_file(&directory.join("plan.bin"), 10 * 1024 * 1024)?
                != resident_bytes
        {
            return Err("resident lifetime paid bytes differ from source-owned op78".into());
        }
        let paid: Value = serde_json::from_slice(&bounded_regular_file(
            &directory.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("lifetime paid inspection JSON: {error}"))?;
        if current != paid
            || &paid != resident_inspection
            || paid.get("canonicalPlanHex").and_then(Value::as_str) != Some(paid_plan_hex)
        {
            return Err("resident lifetime paid inspection differs from source".into());
        }
        let reserve: Value = serde_json::from_slice(&bounded_regular_file(
            &reserve_dir.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("lifetime original reserve plan JSON: {error}"))?;
        let reserve_receipt: Value = serde_json::from_slice(&bounded_regular_file(
            &reserve_dir.join("receipt.json"),
            4096,
        )?)
        .map_err(|error| format!("lifetime original reserve receipt JSON: {error}"))?;
        application_api_tools::verify_lifetime_paid_inspection(
            application_api_tools::LifetimePaidInspection {
                reserve: &reserve,
                paid: &paid,
                reserve_index: confirmed
                    .get("reserveIndex")
                    .and_then(Value::as_str)
                    .ok_or("lifetime reserve index absent")?,
                reserve_receipt: &json!({
                    "transactionId":reserve_receipt.get("transactionId"),
                    "eventId":reserve_receipt.get("eventId"),
                    "acceptedCount":reserve_receipt.get("acceptedCount"),
                    "imageBoundary":reserve_receipt.get("imageBoundary"),
                }),
                signed_post_purse_physical_root: &post_purse_root,
            },
        )?;
        let slots = paid
            .get("payerSlots")
            .and_then(Value::as_array)
            .ok_or("lifetime paid payer slots absent")?;
        let payer_signers = lifetime_purse_signers(slots, signer, &task.custody_key)?;
        let approval = json!({
            "type":"minidregg-agent-lifetime-payer-approval-v1",
            "requestSha256":sha256_file(&directory.join("request.bin"))?,
            "planSha256":sha256_file(&directory.join("plan.bin"))?,
            "fixedSelectors":paid.get("fixedSelectors"),
            "context":paid.get("context"),
            "bindings":paid.get("bindings"),
            "canonicalHttpHex":paid.get("canonicalHttpHex"),
            "reserveReceipt":paid.get("reserveReceipt"),
            "grantIssueReceipt":paid.pointer("/bindings/grantIssueReceipt"),
            "payerSigners":payer_signers,
        });
        let approval_path = self
            .config
            .state_dir
            .join(format!("agent-lifetime-payer-approval-{attempt_id}.json"));
        write_new(
            &approval_path,
            &serde_json::to_vec(&approval)
                .map_err(|error| format!("lifetime payer approval JSON: {error}"))?,
        )?;
        let lifetime = self
            .journal
            .dispatch_attempt
            .as_mut()
            .and_then(|saved| saved.lifetime.as_mut())
            .ok_or("lifetime attempt disappeared before signing")?;
        lifetime.paid_dir = Some(directory.clone());
        lifetime.paid_plan_sha256 = Some(sha256_file(&directory.join("plan.bin"))?);
        self.save()?;
        self.check_not_cancelled()?;
        let result = self.supervised_json_command({
            let mut command = Command::new(&self.config.mini);
            command.args([
                "agent-lifetime-paid-payer-sign",
                "--attempt",
                path(&directory)?,
                "--approval",
                path(&approval_path)?,
            ]);
            command
        })?;
        if result.get("type").and_then(Value::as_str)
            != Some("minidregg-agent-lifetime-payer-signatures-v1")
            || result.get("planSha256").and_then(Value::as_str)
                != Some(sha256_file(&directory.join("plan.bin"))?.as_str())
            || result
                .get("signatures")
                .and_then(Value::as_array)
                .is_none_or(|list| {
                    list.len() != 3
                        || list.iter().any(|entry| {
                            entry.as_str().is_none_or(|signature| {
                                signature.len() != 128
                                    || !signature.bytes().all(|byte| {
                                        byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)
                                    })
                            })
                        })
                })
        {
            return Err("lifetime detached payer signatures differ from approved plan".into());
        }
        Ok(json!({"type":"payer-signatures-v3",
            "attemptId":attempt_id,
            "bindingSha256":confirmed.get("bindingSha256"),
            "operationFingerprint":operation_fingerprint,
            "signedPostReservePursePhysicalRoot":post_purse_root,
            "planSha256":result.get("planSha256"),
            "signatures":result.get("signatures")}))
    }

    /// The resident supplies an op48 paid plan, but only the controller's
    /// retained reserve, protected signer pin, and a fresh source inspection
    /// can approve use of the private purse key. The Mini client independently
    /// reauthors op48 from the original confirmed reserve before signing.
    fn dispatch_sign_payer_v2(
        &mut self,
        route_name: &str,
        forward_operation_id: &str,
        attempt_id: &str,
        paid_plan_hex: &str,
        resident_inspection: &Value,
    ) -> Result<Value> {
        let confirmed = self.dispatch_inspect_v2(route_name, forward_operation_id)?;
        if confirmed.get("type").and_then(Value::as_str) != Some("dispatch-reserved-v2")
            || confirmed.get("attemptId").and_then(Value::as_str) != Some(attempt_id)
        {
            return Err("payer request lacks exact confirmed v2 reserve".into());
        }
        if self.cancelled.load(Ordering::SeqCst)
            || (!self.prompt_active && self.foreground_operation.is_none())
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
        {
            return Err("agent parent no longer permits payer signing".into());
        }
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("payer reserve attempt absent")?;
        if attempt.send_started
            || attempt.no_send_release_started
            || attempt.audited_charge.is_some()
        {
            return Err("payer reserve is no longer available for paid dispatch".into());
        }
        let reserve_dir = attempt
            .reserve_v2_dir
            .as_ref()
            .ok_or("payer reserve custody directory absent")?
            .clone();
        let task = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask absent")?;
        let operator_socket = task
            .operator_socket
            .as_ref()
            .ok_or("private operator socket absent")?;
        let signer = task
            .reserve_signer
            .as_ref()
            .ok_or("protected purse signer pin absent")?;
        if paid_plan_hex.len() > 2 * 10 * 1024 * 1024 {
            return Err("paid plan exceeds native custody bound".into());
        }
        let plan_bytes = dispatch_custody::decode_hex(paid_plan_hex)?;
        if plan_bytes.is_empty() {
            return Err("paid plan is empty".into());
        }
        let plan_sha = sha256_bytes(&plan_bytes)?;
        let plan_path = self
            .config
            .state_dir
            .join(format!("agent-payer-plan-{attempt_id}.bin"));
        retain_exact_private(&plan_path, &plan_bytes, 10 * 1024 * 1024)?;
        let inspected_path = self
            .config
            .state_dir
            .join(format!("agent-payer-inspection-{attempt_id}.json"));
        if !inspected_path.exists() {
            let strings = [
                self.config
                    .host_config
                    .to_str()
                    .ok_or("Host config path UTF-8")?,
                plan_path.to_str().ok_or("paid plan path UTF-8")?,
                inspected_path
                    .to_str()
                    .ok_or("paid inspection path UTF-8")?,
            ];
            self.work_output(
                &self.config.host,
                &[
                    strings[0],
                    "inspect",
                    "application-agent-paid-dispatch-plan",
                    strings[1],
                    strings[2],
                ],
            )
            .map_err(|error| format!("paid plan source inspection: {error}"))?;
        }
        let paid: Value =
            serde_json::from_slice(&bounded_regular_file(&inspected_path, 2_097_152)?)
                .map_err(|error| format!("source paid plan inspection JSON: {error}"))?;
        if &paid != resident_inspection
            || paid.get("type").and_then(Value::as_str)
                != Some("application-agent-paid-dispatch-plan-v2")
            || paid.get("canonicalPlanHex").and_then(Value::as_str) != Some(paid_plan_hex)
        {
            return Err("resident paid plan differs from pinned Host inspection".into());
        }
        let original: Value = serde_json::from_slice(&bounded_regular_file(
            &reserve_dir.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("original reserve inspection JSON: {error}"))?;
        let receipt: Value = serde_json::from_slice(&bounded_regular_file(
            &reserve_dir.join("receipt.json"),
            4096,
        )?)
        .map_err(|error| format!("original reserve receipt JSON: {error}"))?;
        if paid.get("fixedSelectors") != original.get("fixedSelectors")
            || paid.get("context") != original.get("context")
            || paid.get("canonicalHttpHex") != original.get("canonicalHttpHex")
            || paid.get("reserveIndex") != receipt.get("reserveIndex")
            || confirmed.get("reserveReceipt")
                != Some(&json!({
                    "transactionId": receipt.get("transactionId"),
                    "eventId": receipt.get("eventId"),
                    "acceptedCount": receipt.get("acceptedCount"),
                    "imageBoundary": receipt.get("imageBoundary"),
                }))
        {
            return Err("paid plan differs from exact confirmed reserve".into());
        }
        let compact = paid
            .get("compactSelectorRequestHex")
            .and_then(Value::as_str)
            .ok_or("paid compact selector request absent")?;
        let compact_sha = sha256_bytes(&dispatch_custody::decode_hex(compact)?)?;
        let slots = paid
            .get("payerSlots")
            .and_then(Value::as_array)
            .ok_or("paid payer slots absent")?;
        if slots.len() != 1 {
            return Err("first purse profile requires exactly one payer slot".into());
        }
        let slot = &slots[0];
        let signing = slot.get("signing").ok_or("payer signing header absent")?;
        if slot.get("role").and_then(Value::as_str) != Some(&signer.role)
            || slot.get("index").and_then(Value::as_str) != Some(&signer.index)
            || signing.get("decoded").and_then(Value::as_bool) != Some(true)
            || signing.get("keyId").and_then(Value::as_str) != Some(&signer.key_id)
            || signing.get("keyEpoch").and_then(Value::as_str) != Some(&signer.key_epoch)
            || signing.get("algorithm").and_then(Value::as_str) != Some("1")
        {
            return Err("paid payer slot differs from protected signer pin".into());
        }
        let header = dispatch_custody::decode_hex(
            slot.get("headerHex")
                .and_then(Value::as_str)
                .ok_or("payer signing header hex absent")?,
        )?;
        let approval = json!({
            "type":"minidregg-agent-payer-approval-v1",
            "planSha256":plan_sha,
            "compactSelectorRequestSha256":compact_sha,
            "fixedSelectors":original.get("fixedSelectors"),
            "context":original.get("context"),
            "canonicalHttpHex":original.get("canonicalHttpHex"),
            "reserveIndex":receipt.get("reserveIndex"),
            "reserveReceipt":receipt,
            "signers":[{
                "role":signer.role,"index":signer.index,
                "publicKey":signer.public_key,"keyId":signer.key_id,
                "keyEpoch":signer.key_epoch,"headerSha256":sha256_bytes(&header)?,
            }],
        });
        let approval_path = self
            .config
            .state_dir
            .join(format!("agent-payer-approval-{attempt_id}.json"));
        let approval_bytes = serde_json::to_vec(&approval)
            .map_err(|error| format!("payer approval JSON: {error}"))?;
        retain_exact_private(&approval_path, &approval_bytes, 2_097_152)?;
        // A helper crash can leave a private directory without its final
        // signature artifact. The helper performs no native mutation. Preserve
        // that directory, and on a later exact-plan request use a fresh one;
        // never reinterpret a partial directory as a completed approval.
        let payer_base = self
            .config
            .state_dir
            .join(format!("agent-payer-{attempt_id}"));
        let mut payer_dir = None;
        for retry in 0..=9999 {
            let candidate = if retry == 0 {
                payer_base.clone()
            } else {
                self.config
                    .state_dir
                    .join(format!("agent-payer-{attempt_id}-retry-{retry:04}"))
            };
            if !candidate.exists() || candidate.join("payer-signatures.json").exists() {
                payer_dir = Some(candidate);
                break;
            }
        }
        let payer_dir = payer_dir.ok_or("payer signing retry directory limit reached")?;
        if !payer_dir.exists() {
            let args = [
                "agent-payer-sign",
                "--host",
                self.config.host.to_str().ok_or("Host path UTF-8")?,
                "--config",
                self.config
                    .host_config
                    .to_str()
                    .ok_or("Host config path UTF-8")?,
                "--operator-socket",
                operator_socket
                    .to_str()
                    .ok_or("operator socket path UTF-8")?,
                "--reserve-attempt",
                reserve_dir.to_str().ok_or("reserve path UTF-8")?,
                "--plan",
                plan_path.to_str().ok_or("payer plan path UTF-8")?,
                "--approval",
                approval_path.to_str().ok_or("payer approval path UTF-8")?,
                "--key",
                task.custody_key.to_str().ok_or("payer key path UTF-8")?,
                "--dir",
                payer_dir.to_str().ok_or("payer directory UTF-8")?,
            ];
            self.work_output(&self.config.mini, &args)
                .map_err(|error| format!("agent payer source signing: {error}"))?;
        }
        let signatures: Value = serde_json::from_slice(&bounded_regular_file(
            &payer_dir.join("payer-signatures.json"),
            65_536,
        )?)
        .map_err(|error| format!("retained payer signatures JSON: {error}"))?;
        if signatures.get("type").and_then(Value::as_str)
            != Some("minidregg-agent-payer-signatures-v1")
            || signatures.get("paidPlanSha256").and_then(Value::as_str) != Some(&plan_sha)
            || signatures
                .get("compactSelectorRequestSha256")
                .and_then(Value::as_str)
                != Some(&compact_sha)
            || signatures
                .get("originalRequestSha256")
                .and_then(Value::as_str)
                != Some(&sha256_file(&reserve_dir.join("request.bin"))?)
            || signatures.get("reserveReceipt") != approval.get("reserveReceipt")
        {
            return Err("retained payer signatures differ from exact approved plan".into());
        }
        let values = signatures
            .get("signatures")
            .and_then(Value::as_array)
            .ok_or("retained payer signatures absent")?;
        if values.len() != 1
            || values[0].as_str().is_none_or(|signature| {
                signature.len() != 128
                    || !signature
                        .bytes()
                        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            })
        {
            return Err("retained payer signature has invalid shape".into());
        }
        self.check_not_cancelled()?;
        if !self.prompt_active && self.foreground_operation.is_none()
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
        {
            return Err("agent parent disconnected before payer signature reply".into());
        }
        Ok(json!({"type":"payer-signatures-v2","attemptId":attempt_id,
            "planSha256":plan_sha,"signatures":values}))
    }

    fn dispatch_reserve(
        &mut self,
        canonical_request: &[u8],
        source_request_digest: &str,
        http_operation_id: &str,
    ) -> Result<Value> {
        decimal(source_request_digest, "source request digest")?;
        decimal(http_operation_id, "HTTP operation ID")?;
        if source_request_digest.len() > 78
            || http_operation_id.parse::<u64>().is_err()
            || canonical_request.is_empty()
            || canonical_request.len() > 10 * 1024 * 1024
        {
            return Err("dispatch request coordinates exceed bounds".into());
        }
        if self.cancelled.load(Ordering::SeqCst)
            || !self.prompt_active
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || (self.journal.child.is_none() && self.foreground_operation.is_none())
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err("dispatch task or parent prompt is unavailable".into());
        }
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let parent = self.query()?;
        let parent_state = parent.get("grain").ok_or("parent grain absent")?;
        let parent_generation = parent_state
            .get("generation")
            .and_then(Value::as_str)
            .ok_or("parent generation absent")?;
        let parent_root = parent
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("parent root absent")?;
        if !matches!(
            parent_state.get("status").and_then(Value::as_str),
            Some("3" | "4")
        ) || self.journal.prompt_witness.is_none()
        {
            return Err("parent prompt is not reserved".into());
        }
        let attempt_id = self.next_id()?;
        let request_path = self
            .config
            .state_dir
            .join(format!("dispatch-{attempt_id:016}.canonical-request"));
        write_new(&request_path, canonical_request)?;
        self.journal.dispatch_attempt = Some(DispatchAttempt {
            id: attempt_id,
            http_operation_id: http_operation_id.into(),
            parent_generation: parent_generation.into(),
            parent_root: parent_root.into(),
            request_path: request_path.clone(),
            request_bytes: canonical_request.len(),
            request_sha256: sha256_file(&request_path)?,
            source_request_digest: source_request_digest.into(),
            reserve_operation_id: None,
            reserve_v2_dir: None,
            reserve_v2_request_sha256: None,
            reserve_v2_plan_sha256: None,
            reserve_v2_source_sha256: None,
            lifetime: None,
            dispatch_generation: None,
            dispatch_post_root: None,
            no_send_release_started: false,
            audited_charge: None,
            settlement: None,
            send_started: false,
            committed_dispatch_transaction: None,
            committed_dispatch_event: None,
            committed_permit_sha256: None,
            response_sha256: None,
        });
        self.save()?;
        let authority = self.dispatch()?;
        let status = self
            .query_as(&authority)?
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("dispatch grain status absent")?
            .to_owned();
        if status == "0" {
            self.check_not_cancelled()?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "dispatch attach",
                "agent app dispatch attach",
                vec![],
            )?;
        } else if status != "1" {
            return Err(format!(
                "dispatch task status {status} requires reconciliation"
            ));
        }
        self.check_not_cancelled()?;
        self.mark_hold_as(
            AuthoritySlot::Dispatch,
            &authority,
            &task.reserve,
            &task.charge,
        )?;
        let payload =
            format!("DREGG/APPLICATION/AGENT-DISPATCH-RESERVE/v1/{source_request_digest}");
        self.transition_as(
            &authority,
            json!({"type":"reserve","amount":task.reserve}),
            "dispatch reserve",
            &payload,
            vec![],
        )?;
        let dispatch_state = self.query_as(&authority)?;
        if dispatch_state
            .pointer("/grain/status")
            .and_then(Value::as_str)
            != Some("3")
            || dispatch_state
                .pointer("/grain/reserved")
                .and_then(Value::as_str)
                != Some(task.reserve.as_str())
        {
            return Err("confirmed dispatch reserve lacks exact signed reserved state".into());
        }
        let dispatch_generation = dispatch_state
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("dispatch generation absent after reserve")?
            .to_owned();
        let dispatch_post_root = dispatch_state
            .get("targetRoot")
            .and_then(Value::as_str)
            .ok_or("dispatch root absent after reserve")?
            .to_owned();
        let hold = self
            .journal
            .dispatch_hold
            .as_ref()
            .filter(|hold| hold.reserve_confirmed)
            .ok_or("dispatch reserve has no exact confirmed native hold")?;
        let anchor = hold
            .reserve_anchor
            .as_ref()
            .ok_or("dispatch reserve has no exact confirmed native anchor")?
            .clone();
        let reserve_path = hold
            .reserve_attempt
            .as_ref()
            .ok_or("dispatch reserve attempt path absent")?;
        let reserve_name = reserve_path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or("dispatch reserve attempt name invalid")?;
        let encoded = reserve_name
            .strip_prefix("attempt-")
            .ok_or("dispatch reserve attempt name differs")?;
        let reserve_operation_id = encoded
            .parse::<u64>()
            .map_err(|_| "dispatch reserve operation ID malformed")?;
        if encoded.len() != 16
            || *reserve_path
                != self
                    .config
                    .state_dir
                    .join(format!("attempt-{reserve_operation_id:016}"))
        {
            return Err("dispatch reserve attempt path differs from retained source".into());
        }
        let reserve_index = anchor
            .accepted_count
            .parse::<u64>()
            .ok()
            .and_then(|count| count.checked_sub(1))
            .ok_or("dispatch reserve receipt has no selected history index")?;
        let attempt = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("dispatch attempt disappeared")?;
        attempt.reserve_operation_id = Some(reserve_operation_id);
        attempt.dispatch_generation = Some(dispatch_generation.clone());
        attempt.dispatch_post_root = Some(dispatch_post_root.clone());
        self.save()?;
        Ok(json!({
            "type":"dispatch-reserved-v1",
            "attemptId":attempt_id.to_string(),
            "httpOperationId":http_operation_id,
            "requestSha256":sha256_file(&request_path)?,
            "sourceRequestDigest":source_request_digest,
            "reserveOperationId":reserve_operation_id.to_string(),
            "reserveIndex":reserve_index.to_string(),
            "dispatchTask":task.task,
            "dispatchSubject":task.subject,
            "parentTask":self.config.task,
            "parentGeneration":parent_generation,
            "parentRoot":parent_root,
            "dispatchGeneration":dispatch_generation,
            "dispatchPostRoot":dispatch_post_root,
            "reserve":task.reserve,
            "charge":task.charge,
            "reserveReceipt":anchor,
        }))
    }
    /// Persist the one-shot external boundary before the physical host writes
    /// to fd3. The host must already have inspected the exact committed Mini
    /// permit; this marker does not inspect or mint that permit.
    fn dispatch_mark_send(
        &mut self,
        attempt_id: u64,
        request_sha256: &str,
        transaction_id: &str,
        event_id: &str,
        permit_sha256: &str,
    ) -> Result<Value> {
        for (label, value) in [
            ("dispatch request SHA-256", request_sha256),
            ("dispatch permit SHA-256", permit_sha256),
        ] {
            if value.len() != 64
                || !value
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(format!("{label} must be 32 lowercase hex bytes"));
            }
        }
        decimal(transaction_id, "dispatch transaction")?;
        decimal(event_id, "dispatch event")?;
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("no held dispatch attempt")?
            .clone();
        if attempt.lifetime.is_some() {
            return Err(
                "event26 lifetime dispatch requires distinct v3 committed-permit verification"
                    .into(),
            );
        }
        if attempt.id != attempt_id
            || attempt.send_started
            || attempt.no_send_release_started
            || attempt.audited_charge.is_some()
            || attempt.request_sha256 != request_sha256
            || attempt.reserve_operation_id.is_none()
            || self.journal.dispatch_pending.is_some()
            || !self
                .journal
                .dispatch_hold
                .as_ref()
                .is_some_and(|hold| hold.reserve_confirmed && hold.reserve_anchor.is_some())
        {
            return Err("dispatch attempt is not a confirmed unsent reserve".into());
        }
        if sha256_file(&attempt.request_path)? != request_sha256 {
            return Err("retained dispatch request bytes changed".into());
        }
        if attempt.reserve_v2_dir.is_some() {
            self.verified_dispatch_reserve_hold(
                &attempt,
                self.journal
                    .dispatch_hold
                    .as_ref()
                    .ok_or("v2 reserve hold absent")?,
            )?;
        }
        if self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || (!self.prompt_active && self.foreground_operation.is_none())
        {
            return Err("agent parent no longer permits app send".into());
        }
        let parent = self.query()?;
        let parent_state = parent.get("grain").ok_or("parent grain absent")?;
        if parent_state.get("generation").and_then(Value::as_str)
            != Some(attempt.parent_generation.as_str())
            || parent.get("targetRoot").and_then(Value::as_str)
                != Some(attempt.parent_root.as_str())
            || !matches!(
                parent_state.get("status").and_then(Value::as_str),
                Some("3" | "4")
            )
        {
            return Err("agent parent generation changed before app send".into());
        }
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let state = self.query_as(&self.dispatch()?)?;
        if state.pointer("/grain/status").and_then(Value::as_str) != Some("3")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(task.reserve.as_str())
            || state.pointer("/grain/generation").and_then(Value::as_str)
                != attempt.dispatch_generation.as_deref()
            || state.get("targetRoot").and_then(Value::as_str)
                != attempt.dispatch_post_root.as_deref()
        {
            return Err("dispatch purse is no longer reserved".into());
        }
        if self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || (!self.prompt_active && self.foreground_operation.is_none())
        {
            return Err("agent parent fenced during app send preparation".into());
        }
        let attempt = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("dispatch attempt disappeared")?;
        attempt.committed_dispatch_transaction = Some(transaction_id.into());
        attempt.committed_dispatch_event = Some(event_id.into());
        attempt.committed_permit_sha256 = Some(permit_sha256.into());
        attempt.send_started = true;
        self.save()?;
        Ok(
            json!({"type":"dispatch-send-marked-v1","attemptId":attempt_id.to_string(),
            "requestSha256":request_sha256,"transactionId":transaction_id,
            "eventId":event_id,"permitSha256":permit_sha256}),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn dispatch_mark_send_v3(
        &mut self,
        attempt_id: &str,
        binding_sha256: &str,
        operation_fingerprint: &str,
        request_sha256: &str,
        ingress_hex: &str,
        committed_frame_hex: &str,
        receipt: &Value,
    ) -> Result<Value> {
        decimal(attempt_id, "lifetime mark-send attempt ID")?;
        let id = attempt_id
            .parse::<u64>()
            .map_err(|_| "lifetime mark-send attempt ID exceeds u64")?;
        for (label, value) in [
            ("stable binding SHA-256", binding_sha256),
            ("operation fingerprint", operation_fingerprint),
            ("HTTP request SHA-256", request_sha256),
        ] {
            if value.len() != 64
                || !value
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(format!("{label} must be 32 lowercase hex bytes"));
            }
        }
        let exact_receipt: ReserveAnchor = serde_json::from_value(receipt.clone())
            .map_err(|error| format!("lifetime committed receipt shape: {error}"))?;
        for (label, value) in [
            ("transaction ID", &exact_receipt.transaction_id),
            ("event ID", &exact_receipt.event_id),
            ("accepted count", &exact_receipt.accepted_count),
            ("image boundary", &exact_receipt.image_boundary),
        ] {
            decimal(value, label)?;
            if value.len() > 80 {
                return Err(format!("lifetime {label} exceeds native bound"));
            }
        }
        let ingress = dispatch_custody::decode_hex(ingress_hex)?;
        let committed = dispatch_custody::decode_hex(committed_frame_hex)?;
        if ingress.is_empty()
            || ingress.len() > 10 * 1024 * 1024
            || committed.is_empty()
            || committed.len() > 10 * 1024 * 1024
        {
            return Err("lifetime committed custody bytes exceed native bound".into());
        }
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("lifetime dispatch attempt absent")?
            .clone();
        let lifetime = attempt
            .lifetime
            .as_ref()
            .ok_or("mark-send-v3 requires event26 lifetime custody")?;
        let forward = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("lifetime forward attempt absent")?;
        if attempt.id != id
            || attempt.send_started
            || attempt.no_send_release_started
            || attempt.audited_charge.is_some()
            || attempt.request_sha256 != request_sha256
            || forward.operation_id.to_string() != attempt.http_operation_id
            || forward.binding_sha256.as_deref() != Some(binding_sha256)
            || forward.operation_fingerprint.as_deref() != Some(operation_fingerprint)
            || forward.lifetime_committed_receipt.is_some()
            || forward.lifetime_settled_response_sha256.is_some()
            || lifetime.paid_ingress_sha256.is_some()
            || lifetime.committed_frame_sha256.is_some()
            || lifetime.committed_receipt.is_some()
            || lifetime.paid_dir.is_none()
            || self.journal.dispatch_pending.is_some()
            || !self
                .journal
                .dispatch_hold
                .as_ref()
                .is_some_and(|hold| hold.reserve_confirmed && hold.reserve_anchor.is_some())
        {
            return Err("lifetime attempt is not an exact confirmed unsent reserve".into());
        }
        if sha256_file(&attempt.request_path)? != request_sha256 {
            return Err("lifetime retained HTTP request changed".into());
        }
        let paid_dir = lifetime
            .paid_dir
            .as_ref()
            .ok_or("lifetime paid plan absent")?;
        let paid_path = paid_dir.join("plan.bin");
        if sha256_file(&paid_path)?
            != lifetime
                .paid_plan_sha256
                .as_deref()
                .ok_or("lifetime paid plan hash absent")?
        {
            return Err("lifetime paid plan changed after payer signing".into());
        }
        let paid: Value = serde_json::from_slice(&bounded_regular_file(
            &paid_dir.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("lifetime paid plan inspection: {error}"))?;
        let (_, reserve_receipt) = self.verified_dispatch_reserve_hold(
            &attempt,
            self.journal
                .dispatch_hold
                .as_ref()
                .ok_or("lifetime hold absent")?,
        )?;
        if paid.get("reserveReceipt") != Some(&json!(reserve_receipt)) {
            return Err("lifetime paid plan reserve receipt differs".into());
        }
        let ingress_path = self
            .config
            .state_dir
            .join(format!("dispatch-lifetime-ingress-{id:016}.bin"));
        let committed_path = self
            .config
            .state_dir
            .join(format!("dispatch-lifetime-committed-{id:016}.bin"));
        let ingress_view_path = self
            .config
            .state_dir
            .join(format!("dispatch-lifetime-ingress-{id:016}.json"));
        let committed_view_path = self
            .config
            .state_dir
            .join(format!("dispatch-lifetime-committed-{id:016}.json"));
        if ingress_view_path.exists() || committed_view_path.exists() {
            return Err("lifetime mark-send inspection already attempted".into());
        }
        retain_exact_private(&ingress_path, &ingress, 10 * 1024 * 1024)?;
        retain_exact_private(&committed_path, &committed, 10 * 1024 * 1024)?;
        let host = self
            .config
            .host
            .to_str()
            .ok_or("lifetime Host path UTF-8")?;
        let config = self
            .config
            .host_config
            .to_str()
            .ok_or("lifetime config path UTF-8")?;
        let plan_arg = paid_path.to_str().ok_or("lifetime plan path UTF-8")?;
        let ingress_arg = ingress_path.to_str().ok_or("lifetime ingress path UTF-8")?;
        let ingress_view_arg = ingress_view_path
            .to_str()
            .ok_or("lifetime ingress inspection path UTF-8")?;
        let mut inspect_ingress = Command::new(host);
        inspect_ingress.args([
            config,
            "inspect-agent-lifetime-paid-ingress",
            plan_arg,
            ingress_arg,
            ingress_view_arg,
        ]);
        let inspected = self
            .custody_gate
            .run_capture(&self.cancelled, &mut inspect_ingress)
            .map_err(|error| format!("lifetime ingress source inspection: {error}"))?;
        if !inspected.status.success() {
            return Err(format!(
                "lifetime ingress source inspection refused: {}",
                inspected.status
            ));
        }
        let ingress_view: Value =
            serde_json::from_slice(&bounded_regular_file(&ingress_view_path, 2_097_152)?)
                .map_err(|error| format!("lifetime ingress inspection JSON: {error}"))?;
        if ingress_view.get("type").and_then(Value::as_str)
            != Some("application-agent-lifetime-paid-ingress-inspection-v3")
            || ingress_view.get("authority").and_then(Value::as_str)
                != Some("structural-only-not-fresh-admission")
            || ingress_view
                .get("canonicalIngressHex")
                .and_then(Value::as_str)
                != Some(ingress_hex)
            || ingress_view.get("canonicalPlanHex") != paid.get("canonicalPlanHex")
            || ingress_view.get("context") != paid.get("context")
            || ingress_view.get("bindings") != paid.get("bindings")
            || ingress_view.get("fixedSelectors") != paid.get("fixedSelectors")
            || ingress_view.get("canonicalHttpHex") != paid.get("canonicalHttpHex")
            || ingress_view.get("reserveReceipt") != paid.get("reserveReceipt")
            || ingress_view.get("reserveIndex") != paid.get("reserveIndex")
            || ingress_view.get("grantRoot") != paid.get("grantRoot")
            || ingress_view.get("appSlots") != paid.get("appSlots")
            || ingress_view.get("grantObservationSlot") != paid.get("grantObservationSlot")
            || ingress_view.get("payerSlots") != paid.get("payerSlots")
            || ingress_view
                .get("reserveContextHex")
                .and_then(Value::as_str)
                != Some(lifetime.context_hex.as_str())
        {
            return Err("lifetime ingress differs from exact source paid plan".into());
        }
        let committed_arg = committed_path.to_str().ok_or("lifetime frame path UTF-8")?;
        let committed_view_arg = committed_view_path
            .to_str()
            .ok_or("lifetime committed inspection path UTF-8")?;
        let mut inspect_committed = Command::new(host);
        inspect_committed.args([
            config,
            "inspect",
            "application-agent-lifetime-dispatch-committed",
            committed_arg,
            committed_view_arg,
        ]);
        let inspected = self
            .custody_gate
            .run_capture(&self.cancelled, &mut inspect_committed)
            .map_err(|error| format!("lifetime committed source inspection: {error}"))?;
        if !inspected.status.success() {
            return Err(format!(
                "lifetime committed source inspection refused: {}",
                inspected.status
            ));
        }
        let committed_view: Value =
            serde_json::from_slice(&bounded_regular_file(&committed_view_path, 2_097_152)?)
                .map_err(|error| format!("lifetime committed inspection JSON: {error}"))?;
        if committed_view.get("type").and_then(Value::as_str)
            != Some("application-agent-lifetime-dispatch-committed-inspection-v3")
            || committed_view.get("frameHex").and_then(Value::as_str) != Some(committed_frame_hex)
            || committed_view.get("dispatchReceipt") != Some(&json!(exact_receipt))
            || committed_view.pointer("/originalIssue/receipt")
                != Some(&json!(lifetime.original_issue_receipt))
            || committed_view
                .pointer("/originalIssue/index")
                .and_then(Value::as_str)
                != Some(lifetime.original_issue_index.as_str())
            || committed_view.pointer("/grant/issueReceipt")
                != Some(&json!(lifetime.grant_issue_receipt))
            || committed_view
                .pointer("/grant/resource")
                .and_then(Value::as_str)
                != Some(lifetime.grant_resource.as_str())
            || committed_view
                .pointer("/grant/issueIndex")
                .and_then(Value::as_str)
                != Some(lifetime.grant_issue_index.as_str())
            || committed_view
                .pointer("/grant/digest")
                .and_then(Value::as_str)
                != Some(lifetime.grant_digest.as_str())
            || committed_view
                .pointer("/grant/initializedRoot")
                .and_then(Value::as_str)
                != Some(lifetime.grant_initialized_root.as_str())
            || committed_view.pointer("/grant/currentPhysicalRoot")
                != paid.pointer("/bindings/grantPhysicalRoot")
            || committed_view.pointer("/purse/reserveReceipt") != paid.get("reserveReceipt")
            || committed_view.pointer("/purse/reserveIndex") != paid.get("reserveIndex")
            || committed_view.pointer("/request/canonicalHex") != paid.get("canonicalHttpHex")
            || committed_view
                .pointer("/request/operationId")
                .and_then(Value::as_str)
                != Some(attempt.http_operation_id.as_str())
            || committed_view.pointer("/app/resource") != paid.pointer("/context/appResource")
            || committed_view
                .pointer("/app/generation")
                .and_then(Value::as_str)
                != Some(lifetime.app_generation.as_str())
            || committed_view.pointer("/session/resource")
                != paid.pointer("/context/sessionResource")
            || committed_view
                .pointer("/session/generation")
                .and_then(Value::as_str)
                != Some(lifetime.session_generation.as_str())
            || committed_view.pointer("/session/originalOrigin")
                != paid.pointer("/context/sessionOrigin")
            || committed_view.pointer("/parent/physicalRoot")
                != paid.pointer("/bindings/parentPhysicalRoot")
            || committed_view.pointer("/purse/physicalRoot")
                != paid.pointer("/bindings/pursePhysicalRoot")
        {
            return Err("lifetime committed frame differs from paid ingress custody".into());
        }
        if self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || (!self.prompt_active && self.foreground_operation.is_none())
        {
            return Err("lifetime parent no longer permits fd3 handoff".into());
        }
        let ingress_sha256 = sha256_bytes(&ingress)?;
        let committed_sha256 = sha256_bytes(&committed)?;
        let attempt = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("lifetime attempt disappeared before mark-send")?;
        let lifetime = attempt
            .lifetime
            .as_mut()
            .ok_or("lifetime custody disappeared before mark-send")?;
        lifetime.paid_ingress_sha256 = Some(ingress_sha256.clone());
        lifetime.committed_frame_sha256 = Some(committed_sha256.clone());
        lifetime.committed_receipt = Some(exact_receipt.clone());
        attempt.committed_dispatch_transaction = Some(exact_receipt.transaction_id.clone());
        attempt.committed_dispatch_event = Some(exact_receipt.event_id.clone());
        attempt.committed_permit_sha256 = Some(committed_sha256.clone());
        attempt.send_started = true;
        self.journal
            .application_api_attempt
            .as_mut()
            .unwrap()
            .lifetime_committed_receipt = Some(exact_receipt.clone());
        self.save()?;
        if self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
        {
            return Err("lifetime hard fence crossed after durable mark-send".into());
        }
        Ok(json!({"type":"dispatch-send-marked-v3",
            "attemptId":attempt_id,"bindingSha256":binding_sha256,
            "operationFingerprint":operation_fingerprint,
            "requestSha256":request_sha256,
            "ingressSha256":ingress_sha256,
            "committedFrameSha256":committed_sha256,
            "receipt":exact_receipt}))
    }

    /// Only a definite response to this exact marked attempt permits the
    /// fixed operator charge. A lost fd3 reply leaves the reservation held.
    fn dispatch_settle_definite(
        &mut self,
        attempt_id: u64,
        response_sha256: &str,
    ) -> Result<Value> {
        if self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
        {
            return Err("agent hard EOF requires audited dispatch reconciliation".into());
        }
        if response_sha256.len() != 64
            || !response_sha256
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err("response SHA-256 must be 32 lowercase hex bytes".into());
        }
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("no dispatch attempt")?;
        if attempt.id != attempt_id
            || !attempt.send_started
            || attempt.response_sha256.is_some()
            || self.journal.dispatch_pending.is_some()
            || !self
                .journal
                .dispatch_hold
                .as_ref()
                .is_some_and(|hold| hold.reserve_confirmed)
        {
            return Err("dispatch attempt lacks definite held send".into());
        }
        let lifetime_forward = if attempt.lifetime.is_some() {
            let forward = self
                .journal
                .application_api_attempt
                .as_ref()
                .ok_or("lifetime settled forward attempt absent")?;
            if forward.operation_id.to_string() != attempt.http_operation_id
                || forward.lifetime_committed_receipt.as_ref()
                    != attempt
                        .lifetime
                        .as_ref()
                        .and_then(|state| state.committed_receipt.as_ref())
                || forward.lifetime_settled_response_sha256.is_some()
            {
                return Err("lifetime definite settlement lacks exact committed lineage".into());
            }
            true
        } else {
            false
        };
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let authority = self.dispatch()?;
        self.journal
            .dispatch_attempt
            .as_mut()
            .ok_or("dispatch attempt disappeared")?
            .response_sha256 = Some(response_sha256.into());
        self.save()?;
        self.transition_as(
            &authority,
            json!({"type":"settle","charge":task.charge}),
            "dispatch settle",
            "definite app response to retained dispatch attempt",
            vec![],
        )?;
        if lifetime_forward {
            let settled = self
                .journal
                .dispatch_attempt
                .as_ref()
                .and_then(|attempt| attempt.settlement.clone())
                .ok_or("lifetime native settlement record absent")?;
            if settled.operation != "dispatch settle" || settled.charge != task.charge {
                return Err("lifetime native settlement differs from definite charge".into());
            }
            let forward = self
                .journal
                .application_api_attempt
                .as_mut()
                .ok_or("lifetime forward disappeared after settlement")?;
            forward.lifetime_settled_response_sha256 = Some(response_sha256.into());
            forward.lifetime_settlement = Some(LifetimeDefiniteSettlement {
                dispatch_attempt_id: attempt_id,
                forward_operation_id: forward.operation_id,
                settlement: settled,
            });
        }
        self.journal.dispatch_attempt = None;
        self.save()?;
        Ok(
            json!({"type":"dispatch-settled-v1","attemptId":attempt_id.to_string(),
            "responseSha256":response_sha256,"charge":task.charge}),
        )
    }
    fn dispatch_inspect_settlement_v3(
        &mut self,
        attempt_id: u64,
        binding_sha256: &str,
        operation_fingerprint: &str,
    ) -> Result<Value> {
        for (label, value) in [
            ("binding SHA-256", binding_sha256),
            ("operation fingerprint", operation_fingerprint),
        ] {
            if value.len() != 64
                || !value
                    .bytes()
                    .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
            {
                return Err(format!("{label} must be 32 lowercase hex bytes"));
            }
        }
        let uncertain = || {
            json!({"type":"dispatch-settlement-uncertain-v3",
            "attemptId":attempt_id.to_string(),
            "bindingSha256":binding_sha256,
            "operationFingerprint":operation_fingerprint})
        };
        let Some(forward) = self.journal.application_api_attempt.clone() else {
            return Ok(uncertain());
        };
        if forward.binding_sha256.as_deref() != Some(binding_sha256)
            || forward.operation_fingerprint.as_deref() != Some(operation_fingerprint)
        {
            return Err("lifetime settlement inspection differs from forward binding".into());
        }
        let Some(saved) = forward.lifetime_settlement.as_ref() else {
            return Ok(uncertain());
        };
        if saved.dispatch_attempt_id != attempt_id
            || saved.forward_operation_id != forward.operation_id
            || saved.settlement.operation != "dispatch settle"
            || saved.settlement.charge
                != self
                    .config
                    .dispatch_task
                    .as_ref()
                    .ok_or("dispatchTask absent")?
                    .charge
            || forward.lifetime_settled_response_sha256.is_none()
            || forward.lifetime_committed_receipt.is_none()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Ok(uncertain());
        }
        let verified = (|| -> Result<()> {
            self.verified_dispatch_settlement_record(&saved.settlement)?;
            let state = self.query_as(&self.dispatch()?)?;
            if !matches!(
                state.pointer("/grain/status").and_then(Value::as_str),
                Some("1" | "6")
            ) || state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            {
                return Err("lifetime dispatch purse is not signed terminal".into());
            }
            Ok(())
        })();
        if verified.is_err() {
            return Ok(uncertain());
        }
        Ok(json!({"type":"settled-v3",
            "attemptId":attempt_id.to_string(),
            "bindingSha256":binding_sha256,
            "operationFingerprint":operation_fingerprint,
            "responseSha256":forward.lifetime_settled_response_sha256,
            "committedReceipt":forward.lifetime_committed_receipt}))
    }
    /// A definite pre-send refusal releases this one purse at zero. Once the
    /// send marker exists, only a definite response or audited reconciliation
    /// may settle it; an old HTTP operation cannot obtain a second attempt.
    fn dispatch_abort_no_send(&mut self, attempt_id: u64) -> Result<Value> {
        if self.cancelled.load(Ordering::SeqCst)
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
        {
            return Err("agent hard EOF requires audited dispatch reconciliation".into());
        }
        let attempt = self
            .journal
            .dispatch_attempt
            .as_ref()
            .ok_or("no dispatch attempt")?;
        if attempt.id != attempt_id
            || attempt.send_started
            || self.journal.dispatch_pending.is_some()
        {
            return Err("dispatch may have crossed an external boundary".into());
        }
        if let Some(hold) = self.journal.dispatch_hold.clone() {
            let authority = self.dispatch()?;
            if hold.reserve_confirmed && hold.reserve_anchor.is_some() {
                self.journal
                    .dispatch_attempt
                    .as_mut()
                    .ok_or("dispatch attempt disappeared before release")?
                    .no_send_release_started = true;
                self.save()?;
                self.transition_as(
                    &authority,
                    json!({"type":"settle","charge":"0"}),
                    "dispatch release",
                    "definite refusal before app send",
                    vec![],
                )?;
            } else if hold.reserve_refused || hold.reserve_attempt.is_none() {
                let current = self.query_as(&authority)?;
                if current.pointer("/grain/status").and_then(Value::as_str) != Some("1")
                    || current.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
                    || current.get("targetRoot").and_then(Value::as_str)
                        != Some(hold.before_target_root.as_str())
                {
                    return Err("unsubmitted dispatch reserve differs from held origin".into());
                }
                self.journal.dispatch_hold = None;
                self.save()?;
            } else {
                return Err("dispatch reserve may have committed; exact lookup required".into());
            }
        } else if attempt.reserve_operation_id.is_some() {
            return Err("dispatch reserve marker disappeared without settlement".into());
        }
        self.journal.dispatch_attempt = None;
        self.save()?;
        Ok(json!({"type":"dispatch-aborted-before-send-v1",
            "attemptId":attempt_id.to_string(),"charge":"0"}))
    }
    fn dispatch_rpc(&mut self, command: dispatch_custody::Command) -> Result<Value> {
        use dispatch_custody::Command as C;
        let attempt_id = |value: &str| -> Result<u64> {
            decimal(value, "dispatch attempt ID")?;
            value
                .parse::<u64>()
                .map_err(|_| "dispatch attempt ID exceeds u64".into())
        };
        match command {
            C::Reserve {
                http_operation_id,
                source_request_digest,
                canonical_request_hex,
            } => {
                let request = dispatch_custody::decode_hex(&canonical_request_hex)?;
                self.dispatch_reserve(&request, &source_request_digest, &http_operation_id)
            }
            C::ReserveV2 {
                route_name,
                forward_operation_id,
                fixed_request,
            } => self.dispatch_reserve_v2(&route_name, &forward_operation_id, &fixed_request),
            C::ReserveV3 {
                route_name,
                forward_operation_id,
                binding_sha256,
                worker_wall_seconds,
                fixed_request,
            } => self.dispatch_reserve_v3(
                &route_name,
                &forward_operation_id,
                &binding_sha256,
                worker_wall_seconds,
                &fixed_request,
            ),
            C::InspectV2 {
                route_name,
                forward_operation_id,
            } => self.dispatch_inspect_v2(&route_name, &forward_operation_id),
            C::InspectV3 {
                route_name,
                forward_operation_id,
            } => self.dispatch_inspect_v3(&route_name, &forward_operation_id),
            C::InspectSettlementV3 {
                attempt_id: id,
                binding_sha256,
                operation_fingerprint,
            } => self.dispatch_inspect_settlement_v3(
                attempt_id(&id)?,
                &binding_sha256,
                &operation_fingerprint,
            ),
            C::SignPayerV2 {
                route_name,
                forward_operation_id,
                attempt_id,
                paid_plan_hex,
                source_inspection_json,
            } => self.dispatch_sign_payer_v2(
                &route_name,
                &forward_operation_id,
                &attempt_id,
                &paid_plan_hex,
                &source_inspection_json,
            ),
            C::SignPayerV3 {
                route_name,
                forward_operation_id,
                attempt_id,
                paid_plan_hex,
                source_inspection_json,
                operation_fingerprint,
            } => self.dispatch_sign_payer_v3(
                &route_name,
                &forward_operation_id,
                &attempt_id,
                &paid_plan_hex,
                &source_inspection_json,
                &operation_fingerprint,
            ),
            C::MarkSend {
                attempt_id: id,
                request_sha256,
                transaction_id,
                event_id,
                permit_sha256,
            } => self.dispatch_mark_send(
                attempt_id(&id)?,
                &request_sha256,
                &transaction_id,
                &event_id,
                &permit_sha256,
            ),
            C::MarkSendV3 {
                attempt_id,
                binding_sha256,
                operation_fingerprint,
                request_sha256,
                ingress_hex,
                committed_frame_hex,
                receipt,
            } => self.dispatch_mark_send_v3(
                &attempt_id,
                &binding_sha256,
                &operation_fingerprint,
                &request_sha256,
                &ingress_hex,
                &committed_frame_hex,
                &receipt,
            ),
            C::SettleDefinite {
                attempt_id: id,
                response_sha256,
            } => self.dispatch_settle_definite(attempt_id(&id)?, &response_sha256),
            C::AbortNoSend { attempt_id: id } => self.dispatch_abort_no_send(attempt_id(&id)?),
            C::Inspect { attempt_id: id } => {
                let id = attempt_id(&id)?;
                let attempt = self
                    .journal
                    .dispatch_attempt
                    .as_ref()
                    .ok_or("no dispatch attempt")?;
                if attempt.id != id {
                    return Err("dispatch attempt ID differs".into());
                }
                let hold = self.journal.dispatch_hold.as_ref();
                Ok(json!({"type":"dispatch-attempt-v1",
                    "attemptId":id.to_string(),
                    "httpOperationId":attempt.http_operation_id,
                    "sourceRequestDigest":attempt.source_request_digest,
                    "requestSha256":attempt.request_sha256,
                    "parentGeneration":attempt.parent_generation,
                    "reserveOperationId":attempt.reserve_operation_id.map(|n| n.to_string()),
                    "reserveConfirmed":hold.is_some_and(|h| h.reserve_confirmed),
                    "reserveReceipt":hold.and_then(|h| h.reserve_anchor.as_ref()),
                    "sendStarted":attempt.send_started,
                    "dispatchTransaction":attempt.committed_dispatch_transaction,
                    "dispatchEvent":attempt.committed_dispatch_event,
                    "permitSha256":attempt.committed_permit_sha256,
                    "responseSha256":attempt.response_sha256}))
            }
        }
    }
    fn answer_dispatch(&mut self, request: dispatch_custody::Request) {
        if Instant::now() >= request.deadline
            || request
                .phase
                .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst)
                .is_err()
        {
            let _ = request.reply.send(json!({"type":"refused",
                "detail":"dispatch RPC expired before execution"}));
            return;
        }
        let response = match self.dispatch_rpc(request.command) {
            Ok(value) => value,
            Err(detail) => json!({"type":"refused","detail":detail}),
        };
        request.phase.store(2, Ordering::SeqCst);
        let _ = request.reply.send(response);
    }
    fn provider(&self) -> Result<Authority> {
        let p = self
            .config
            .provider_task
            .as_ref()
            .ok_or("providerTask is not configured")?;
        Ok(Authority {
            task: p.task.clone(),
            subject: p.subject.clone(),
            capability: p.capability.clone(),
            query_capability: p.query_capability.clone(),
            custody_key: p.custody_key.clone(),
        })
    }
    fn open(config: Config, config_path: PathBuf) -> Result<Self> {
        validate(&config)?;
        if !config_path.is_absolute() {
            return Err("controller config path must be absolute".into());
        }
        let binding = json!({"config":config,"configPath":config_path});
        fs::create_dir_all(&config.state_dir).map_err(|e| format!("state directory: {e}"))?;
        let state_meta = fs::symlink_metadata(&config.state_dir).map_err(|e| e.to_string())?;
        if !state_meta.file_type().is_dir()
            || state_meta.file_type().is_symlink()
            || state_meta.uid() != unsafe { libc::geteuid() }
        {
            return Err("stateDir must be an owned real directory".into());
        }
        fs::set_permissions(&config.state_dir, fs::Permissions::from_mode(0o700))
            .map_err(|e| format!("state directory mode: {e}"))?;
        let lock_path = config.state_dir.join("controller.lock");
        let lock = OpenOptions::new()
            .create(true)
            .truncate(false)
            .read(true)
            .write(true)
            .mode(0o600)
            .open(&lock_path)
            .map_err(|e| format!("controller lock: {e}"))?;
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err("another controller owns this task".into());
        }
        let path = config.state_dir.join("journal.json");
        let journal = if path.exists() {
            let bytes = fs::read(&path).map_err(|e| format!("journal read: {e}"))?;
            let j: Journal =
                serde_json::from_slice(&bytes).map_err(|e| format!("journal decode: {e}"))?;
            if j.format != "minidregg-grain-runtime-v1" {
                return Err("journal format mismatch".into());
            }
            if j.binding != binding {
                return Err("controller config differs from journal binding".into());
            }
            j.validate_birth_registry()?;
            j.validate_application_api(&config.state_dir)?;
            j.validate_foreground(&config.state_dir)?;
            j.validate_workspace(&config)?;
            j
        } else {
            let j = Journal::fresh(binding);
            atomic_json(&path, &j)?;
            j
        };
        let process_first_operation_id = journal.next_operation_id;
        let mut rt = Self {
            config,
            config_path,
            journal,
            child: None,
            _lock: lock,
            stdin_gone: false,
            current_pgid: Arc::new(AtomicI32::new(0)),
            hard_connection: Arc::new(AtomicBool::new(false)),
            signal_lock: Arc::new(Mutex::new(())),
            cancelled: Arc::new(AtomicBool::new(false)),
            custody_gate: Arc::new(custody_gate::CustodyGate::new()),
            application_api_send_gate: Arc::new(application_api_tools::ForwardSendGate::new()),
            completion_phase: Arc::new(AtomicU8::new(PHASE_IDLE)),
            current_unit: Arc::new(Mutex::new(None)),
            provider_control: Arc::new(Mutex::new(None)),
            provider_lease: None,
            prompt_active: false,
            foreground_operation: None,
            output: None,
            process_first_operation_id,
            startup_recovery_active: false,
            prior_run_stopped: false,
        };
        // We have no live Child handle after a controller crash. A recycled
        // PID/PGID must never be killed. Fence the task and refuse new work.
        if rt.journal.child.is_some()
            || rt.journal.foreground_attempt.is_some()
            || rt.journal.connection == Connection::Hard
            || rt.journal.hard_reconnect_pending
        {
            rt.journal.connection = Connection::Fenced;
            rt.save()?;
        }
        Ok(rt)
    }
    fn save(&self) -> Result<()> {
        atomic_json(&self.config.state_dir.join("journal.json"), &self.journal)
    }
    fn confirmed_publication_receipt(
        &self,
        pending: &Pending,
        outcome_path: &Path,
    ) -> Result<Option<PublicationReceipt>> {
        let Some(origin) = &pending.publication else {
            return Ok(None);
        };
        let tool = self.config.tool_task.as_ref().ok_or("tool task absent")?;
        if pending.operation != "tool settle"
            || pending.attempt
                != self
                    .config
                    .state_dir
                    .join(format!("attempt-{:016}", pending.operation_id))
            || origin.targets.is_empty()
            || origin.targets.len() > 8
        {
            return Err("publication pending origin is inconsistent".into());
        }
        match &origin.work_origin {
            None if origin.session_id.is_empty() => {
                return Err("publication Hermes origin lacks its session".into());
            }
            Some(WorkOrigin::ForegroundTool { operation_id })
                if *operation_id != origin.prompt_operation_id || !origin.session_id.is_empty() =>
            {
                return Err("publication foreground origin differs from its operation".into());
            }
            _ => {}
        }
        let source_path = self
            .config
            .state_dir
            .join(format!("source-{:016}.json", pending.operation_id));
        if sha256_file(&source_path)? != origin.source_sha256 {
            return Err("retained publication source changed".into());
        }
        let source: Value =
            serde_json::from_slice(&fs::read(&source_path).map_err(|e| e.to_string())?)
                .map_err(|e| format!("publication source: {e}"))?;
        let grain = &source["grain"];
        if grain["task"] != tool.task
            || grain["subject"] != tool.subject
            || grain["operation"]["type"] != "settle"
            || !grain["parentWitness"].is_object()
        {
            return Err("retained publication source is not a delegated tool settlement".into());
        }
        let targets = grain["publications"]
            .as_array()
            .ok_or("retained publication target list absent")?;
        if targets.len() != origin.targets.len() {
            return Err("retained publication source targets differ from delegated origin".into());
        }
        for (target, id) in targets.iter().zip(&origin.targets) {
            let kind = target["kind"]
                .as_str()
                .ok_or("retained publication kind absent")?;
            if target["target"].as_str() != Some(id.as_str())
                || !(tool
                    .allowed_publications
                    .iter()
                    .any(|allowed| allowed.kind == kind && allowed.target == *id)
                    || self.verified_born_target(kind, id)?.is_some())
            {
                return Err("retained publication target is not delegated".into());
            }
        }
        let outcome: Value =
            serde_json::from_slice(&fs::read(outcome_path).map_err(|e| e.to_string())?)
                .map_err(|e| format!("publication outcome: {e}"))?;
        if outcome["type"] != "confirmed"
            || !matches!(
                outcome["confirmation"].as_str(),
                Some("installed" | "replayed")
            )
        {
            return Err("publication has no confirmed Mini receipt".into());
        }
        let field = |name: &str| -> Result<String> {
            let value = outcome[name]
                .as_str()
                .ok_or_else(|| format!("publication receipt lacks {name}"))?;
            decimal(value, name)?;
            Ok(value.to_owned())
        };
        let call = pending.attempt.join("call.bin");
        let binary = outcome_path.with_extension("bin");
        if fs::metadata(&call).map_err(|e| e.to_string())?.len() > 4_194_304
            || fs::metadata(&binary).map_err(|e| e.to_string())?.len() > 4_194_304
        {
            return Err("publication native evidence exceeds bound".into());
        }
        Ok(Some(PublicationReceipt {
            prompt_operation_id: origin.prompt_operation_id,
            session_id: origin.session_id.clone(),
            work_origin: origin.work_origin.clone(),
            operation_id: pending.operation_id,
            attempt: pending.attempt.clone(),
            source_sha256: origin.source_sha256.clone(),
            call_sha256: sha256_file(&call)?,
            outcome_path: outcome_path.to_owned(),
            outcome_sha256: sha256_file(&binary)?,
            targets: origin.targets.clone(),
            transaction_id: field("transactionId")?,
            event_id: field("eventId")?,
            accepted_count: field("acceptedCount")?,
            image_boundary: field("imageBoundary")?,
            reported: false,
        }))
    }
    fn confirmed_birth_record(
        &self,
        pending: &Pending,
        origin: &BirthPending,
        outcome_path: &Path,
    ) -> Result<Option<BornResourceRecord>> {
        if pending.operation != "tool birth" {
            return Ok(None);
        }
        origin.validate_members()?;
        let tool = self.config.tool_task.as_ref().ok_or("tool task absent")?;
        if pending.operation_id != origin.operation_id
            || pending.attempt
                != self
                    .config
                    .state_dir
                    .join(format!("attempt-{:016}", pending.operation_id))
        {
            return Err("resource birth attempt differs from durable origin".into());
        }
        let source_path = self
            .config
            .state_dir
            .join(format!("source-{:016}.json", pending.operation_id));
        let source_bytes = bounded_regular_file(&source_path, 262_144)?;
        if sha256_bytes(&source_bytes)? != origin.source_sha256 {
            return Err("retained resource birth source changed".into());
        }
        let source: Value = serde_json::from_slice(&source_bytes)
            .map_err(|e| format!("resource birth source: {e}"))?;
        let (expected, born) = match origin.route {
            None => {
                let family = tool
                    .allowed_birth_families
                    .iter()
                    .find(|family| family.name == origin.family)
                    .ok_or("resource birth family changed")?;
                let (source, born) = resource_tools::plan_content_birth(
                    family,
                    tool,
                    &self.config.task,
                    pending.operation_id,
                    origin.ordinal,
                    &origin.tool_view,
                    &origin.parent_view,
                )?;
                (source, vec![born])
            }
            Some(ApplicationBirthRoute::Application) => {
                let family = tool
                    .allowed_application_families
                    .iter()
                    .find(|family| family.name == origin.family)
                    .ok_or("application birth family changed")?;
                application_tools::plan_application_birth(
                    family,
                    tool,
                    &self.config.task,
                    pending.operation_id,
                    origin.ordinal,
                    &origin.tool_view,
                    &origin.parent_view,
                )?
            }
            Some(ApplicationBirthRoute::Session) => {
                let family = tool
                    .allowed_session_families
                    .iter()
                    .find(|family| family.name == origin.family)
                    .ok_or("session birth family changed")?;
                let app_name = origin
                    .selected_application
                    .as_deref()
                    .ok_or("session birth has no retained application selector")?;
                let app_target = if let Some(shared) = origin.selected_shared.as_ref() {
                    let reference = tool
                        .registered_shared_applications
                        .iter()
                        .find(|reference| {
                            reference.name == app_name
                                && reference.application_family == family.application_family
                        })
                        .ok_or("session birth shared reference is no longer configured")?;
                    shared_app_refs::validate_selected(reference, shared)?;
                    shared.app_target.as_str()
                } else {
                    let app_record = self
                        .journal
                        .born_resources
                        .iter()
                        .find(|record| {
                            record.pending.route == Some(ApplicationBirthRoute::Application)
                                && record.pending.family == family.application_family
                                && record.pending.born.name == app_name
                        })
                        .ok_or("session birth selected application is not retained")?;
                    self.verify_born_record(app_record)?;
                    app_record.pending.born.target.as_str()
                };
                application_tools::plan_session_birth(
                    family,
                    tool,
                    &self.config.task,
                    app_target,
                    application_tools::BirthIndex {
                        nonce: pending.operation_id,
                        ordinal: origin.ordinal,
                    },
                    &origin.tool_view,
                    &origin.parent_view,
                )?
            }
        };
        if source != expected || born != origin.members() {
            return Err("retained resource birth differs from operator family".into());
        }
        if let Some(route) = origin.route {
            let author = self
                .config
                .state_dir
                .join(format!("current-author-{:016}", pending.operation_id));
            if bounded_regular_file(&author.join("source.json"), 262_144)? != source_bytes
                || bounded_regular_file(&author.join("config.json"), 65_536)?
                    != bounded_regular_file(&pending.attempt.join("config.json"), 65_536)?
            {
                return Err(
                    "current birth author source or config differs from signed submit".into(),
                );
            }
            let frame = bounded_regular_file(&author.join("reply.frame"), 4_194_305)?;
            let opcode = match route {
                ApplicationBirthRoute::Application => 30,
                ApplicationBirthRoute::Session => 31,
            };
            if frame.first() != Some(&opcode) || frame.len() < 2 {
                return Err("retained current birth author reply is not successful".into());
            }
            let intent = bounded_regular_file(&author.join("intent.bin"), 4_194_304)?;
            if frame[1..] != intent
                || sha256_bytes(&intent)?
                    != origin
                        .authored_intent_sha256
                        .as_deref()
                        .ok_or("current birth intent digest absent")?
                || bounded_regular_file(&pending.attempt.join("intent-source.bin"), 4_194_304)?
                    != intent
            {
                return Err(
                    "retained current birth intent differs from signed submit input".into(),
                );
            }
        }
        let outcome_bytes = bounded_regular_file(outcome_path, 131_072)?;
        let outcome: Value = serde_json::from_slice(&outcome_bytes)
            .map_err(|e| format!("resource birth outcome: {e}"))?;
        if outcome["type"] != "confirmed"
            || !matches!(
                outcome["confirmation"].as_str(),
                Some("installed" | "replayed")
            )
        {
            return Err("resource birth has no confirmed Mini receipt".into());
        }
        let field = |name: &str| -> Result<String> {
            let value = outcome[name]
                .as_str()
                .ok_or_else(|| format!("resource birth receipt lacks {name}"))?;
            decimal(value, name)?;
            Ok(value.to_owned())
        };
        let call = pending.attempt.join("call.bin");
        let binary = outcome_path.with_extension("bin");
        Ok(Some(BornResourceRecord {
            pending: origin.clone(),
            attempt: pending.attempt.clone(),
            call_sha256: sha256_bytes(&bounded_regular_file(&call, 4_194_304)?)?,
            outcome_path: outcome_path.to_owned(),
            outcome_sha256: sha256_bytes(&bounded_regular_file(&binary, 4_194_304)?)?,
            transaction_id: field("transactionId")?,
            event_id: field("eventId")?,
            accepted_count: field("acceptedCount")?,
            image_boundary: field("imageBoundary")?,
            reported: false,
        }))
    }
    fn verify_born_record(&self, record: &BornResourceRecord) -> Result<()> {
        let pending = Pending {
            operation_id: record.pending.operation_id,
            operation: "tool birth".into(),
            attempt: record.attempt.clone(),
            uncertain: false,
            publication: None,
        };
        let mut actual = self
            .confirmed_birth_record(&pending, &record.pending, &record.outcome_path)?
            .ok_or("born resource has no retained native receipt")?;
        actual.reported = record.reported;
        if &actual != record
            || self
                .journal
                .birth_next_ordinal
                .get(&record.pending.family)
                .is_none_or(|next| *next <= record.pending.ordinal)
        {
            return Err("born resource registry differs from retained native evidence".into());
        }
        Ok(())
    }
    fn verified_born_named(&self, name: &str) -> Result<Option<resource_tools::BornResource>> {
        let Some(record) = self.journal.born_resources.iter().find(|record| {
            record
                .pending
                .members()
                .iter()
                .any(|born| born.name == name)
        }) else {
            return Ok(None);
        };
        self.verify_born_record(record)?;
        Ok(record
            .pending
            .members()
            .iter()
            .find(|born| born.name == name)
            .cloned())
    }
    fn verified_born_target(
        &self,
        kind: &str,
        target: &str,
    ) -> Result<Option<resource_tools::BornResource>> {
        let Some(record) = self.journal.born_resources.iter().find(|record| {
            record
                .pending
                .members()
                .iter()
                .any(|born| born.kind == kind && born.target == target)
        }) else {
            return Ok(None);
        };
        self.verify_born_record(record)?;
        Ok(record
            .pending
            .members()
            .iter()
            .find(|born| born.kind == kind && born.target == target)
            .cloned())
    }
    fn provider_settlement_record(
        &self,
        pending: &Pending,
        outcome_path: &Path,
    ) -> Result<ProviderSettlement> {
        let task = self
            .config
            .provider_task
            .as_ref()
            .ok_or("providerTask absent")?;
        let provider_attempt = self
            .journal
            .provider_attempt
            .as_ref()
            .ok_or("provider settlement has no retained request")?;
        if !matches!(
            pending.operation.as_str(),
            "provider settle" | "provider audit settle"
        ) || pending.attempt
            != self
                .config
                .state_dir
                .join(format!("attempt-{:016}", pending.operation_id))
        {
            return Err("provider settlement has no exact pending operation".into());
        }
        let source_path = self
            .config
            .state_dir
            .join(format!("source-{:016}.json", pending.operation_id));
        let source_bytes = bounded_regular_file(&source_path, 131_072)?;
        let source: Value = serde_json::from_slice(&source_bytes)
            .map_err(|e| format!("provider settlement source: {e}"))?;
        let charge = source
            .pointer("/grain/operation/charge")
            .and_then(Value::as_str)
            .ok_or("provider settlement charge absent")?;
        decimal(charge, "provider settlement charge")?;
        if source.pointer("/grain/task").and_then(Value::as_str) != Some(task.task.as_str())
            || source.pointer("/grain/subject").and_then(Value::as_str)
                != Some(task.subject.as_str())
            || source
                .pointer("/grain/operation/type")
                .and_then(Value::as_str)
                != Some("settle")
            || source
                .pointer("/grain/context/operationId")
                .and_then(Value::as_str)
                != Some(pending.operation_id.to_string().as_str())
        {
            return Err("provider settlement source differs from pinned operation".into());
        }
        let outcome_bytes = bounded_regular_file(outcome_path, 131_072)?;
        let outcome: Value = serde_json::from_slice(&outcome_bytes)
            .map_err(|e| format!("provider settlement outcome: {e}"))?;
        if outcome.get("type").and_then(Value::as_str) != Some("confirmed")
            || !matches!(
                outcome.get("confirmation").and_then(Value::as_str),
                Some("installed" | "replayed")
            )
        {
            return Err("provider settlement has no confirmed native outcome".into());
        }
        let call = pending.attempt.join("call.bin");
        let outcome_binary = outcome_path.with_extension("bin");
        Ok(ProviderSettlement {
            provider_attempt_id: provider_attempt.id,
            operation_id: pending.operation_id,
            operation: pending.operation.clone(),
            attempt: pending.attempt.clone(),
            charge: charge.to_owned(),
            source_sha256: sha256_bytes(&source_bytes)?,
            call_sha256: sha256_bytes(&bounded_regular_file(&call, 4_194_304)?)?,
            outcome_path: outcome_path.to_owned(),
            outcome_sha256: sha256_bytes(&bounded_regular_file(&outcome_binary, 4_194_304)?)?,
            receipt: ReserveAnchor::from_confirmed(&outcome)?,
        })
    }
    fn verified_provider_settlement(
        &self,
        provider_attempt: &ProviderAttempt,
    ) -> Result<ProviderSettlement> {
        let settled = self
            .journal
            .provider_settlement
            .as_ref()
            .ok_or("provider has no retained exact settlement receipt")?;
        if settled.provider_attempt_id != provider_attempt.id {
            return Err("provider settlement names another request".into());
        }
        let pending = Pending {
            operation_id: settled.operation_id,
            operation: settled.operation.clone(),
            attempt: settled.attempt.clone(),
            uncertain: false,
            publication: None,
        };
        let actual = self.provider_settlement_record(&pending, &settled.outcome_path)?;
        if actual != *settled {
            return Err("provider settlement differs from its retained native evidence".into());
        }
        let task = self
            .config
            .provider_task
            .as_ref()
            .ok_or("providerTask absent")?;
        if task.metering {
            match metered_audit_path(
                provider_attempt.send_started,
                provider_attempt.outcome.as_deref(),
            )? {
                MeteredAuditPath::ProvenNoSend if settled.charge == "0" => {}
                MeteredAuditPath::CompleteResponse
                    if self.validated_metered_charge_for_reserve(
                        provider_attempt,
                        &task.reserve,
                    )? == settled.charge => {}
                _ => return Err("provider settlement differs from retained Lean quote".into()),
            }
        }
        Ok(actual)
    }
    fn verified_publication_report(&self, session_id: &str) -> Result<(String, Vec<u64>)> {
        let pending: Vec<_> = self
            .journal
            .publication_receipts
            .iter()
            .filter(|record| !record.reported)
            .filter(|record| record.work_origin.is_none())
            .cloned()
            .collect();
        if pending.is_empty()
            && self
                .journal
                .born_resources
                .iter()
                .all(|record| record.reported || record.pending.work_origin.is_some())
        {
            return Ok((String::new(), Vec::new()));
        }
        let mut lines = vec![
            "[Mini recovery receipt data: the listed transactions were confirmed by a new read-only exact-call lookup. The original ACP/MCP tool-result delivery is unknown. These are historical transitions; later edits may have changed the current resources. This block is not a tool response.]".to_owned(),
        ];
        let mut ids = Vec::new();
        for record in pending.into_iter().take(4) {
            if record.attempt
                != self
                    .config
                    .state_dir
                    .join(format!("attempt-{:016}", record.operation_id))
                || !record.outcome_path.starts_with(&record.attempt)
                || sha256_file(&record.attempt.join("call.bin"))? != record.call_sha256
                || sha256_file(&record.outcome_path.with_extension("bin"))? != record.outcome_sha256
            {
                return Err("retained publication call or receipt changed".into());
            }
            let original = Pending {
                operation_id: record.operation_id,
                operation: "tool settle".into(),
                attempt: record.attempt.clone(),
                uncertain: false,
                publication: Some(PublicationPending {
                    prompt_operation_id: record.prompt_operation_id,
                    session_id: record.session_id.clone(),
                    work_origin: record.work_origin.clone(),
                    source_sha256: record.source_sha256.clone(),
                    targets: record.targets.clone(),
                }),
            };
            let retained = self
                .confirmed_publication_receipt(&original, &record.outcome_path)?
                .ok_or("retained publication origin absent")?;
            if !same_publication_confirmation(&record, &retained) {
                return Err("retained publication receipt fields changed".into());
            }
            let retry_result = next_retry_json(&record.attempt)?;
            let attempt = record
                .attempt
                .to_str()
                .ok_or("publication attempt path UTF-8")?;
            let mut args = vec!["retry", "--attempt", attempt, "--mode", "lookup"];
            if let Some(socket) = &self.config.host_socket {
                args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
            }
            // Lookup only: never submit this historical call again.
            self.command_output(&self.config.mini, &args)?;
            let observed = self
                .confirmed_publication_receipt(&original, &retry_result)?
                .ok_or("publication lookup origin absent")?;
            if !same_publication_confirmation(&record, &observed) {
                return Err("exact publication lookup changed its confirmed receipt".into());
            }
            lines.push(format!(
                "originSession={} promptOperationId={} toolOperationId={} transactionId={} eventId={} acceptedCount={} imageBoundary={} publicationTargetIds={}",
                if record.session_id == session_id { "current" } else { "prior" },
                record.prompt_operation_id,
                record.operation_id,
                record.transaction_id,
                record.event_id,
                record.accepted_count,
                record.image_boundary,
                record.targets.join(",")
            ));
            ids.push(record.operation_id);
        }
        for record in self
            .journal
            .born_resources
            .iter()
            .filter(|record| !record.reported && record.pending.work_origin.is_none())
            .take(4usize.saturating_sub(ids.len()))
        {
            self.verify_born_record(record)?;
            let retry_result = next_retry_json(&record.attempt)?;
            let attempt = record
                .attempt
                .to_str()
                .ok_or("resource birth attempt path UTF-8")?;
            let mut args = vec!["retry", "--attempt", attempt, "--mode", "lookup"];
            if let Some(socket) = &self.config.host_socket {
                args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
            }
            self.command_output(&self.config.mini, &args)?;
            let mut observed = self
                .confirmed_birth_record(
                    &Pending {
                        operation_id: record.pending.operation_id,
                        operation: "tool birth".into(),
                        attempt: record.attempt.clone(),
                        uncertain: false,
                        publication: None,
                    },
                    &record.pending,
                    &retry_result,
                )?
                .ok_or("resource birth lookup has no confirmed receipt")?;
            observed.reported = record.reported;
            if observed.pending != record.pending
                || observed.call_sha256 != record.call_sha256
                || observed.transaction_id != record.transaction_id
                || observed.event_id != record.event_id
                || observed.accepted_count != record.accepted_count
                || observed.image_boundary != record.image_boundary
            {
                return Err("exact resource birth lookup changed its confirmed receipt".into());
            }
            let member_summary = if let Some(route) = record.pending.route {
                let members = record
                    .pending
                    .members()
                    .iter()
                    .map(|member| json!({"name":member.name,"target":member.target}))
                    .collect::<Vec<_>>();
                format!(
                    "route={} bornResources={}",
                    serde_json::to_string(&route).map_err(|e| e.to_string())?,
                    serde_json::to_string(&members).map_err(|e| e.to_string())?
                )
            } else {
                format!(
                    "bornResourceName={} bornTargetId={}",
                    record.pending.born.name, record.pending.born.target
                )
            };
            lines.push(format!(
                "originSession={} promptOperationId={} toolOperationId={} transactionId={} eventId={} acceptedCount={} imageBoundary={} {}",
                if record.pending.session_id == session_id { "current" } else { "prior" },
                record.pending.prompt_operation_id,
                record.pending.operation_id,
                record.transaction_id,
                record.event_id,
                record.accepted_count,
                record.image_boundary,
                member_summary,
            ));
            ids.push(record.pending.operation_id);
        }
        let report = lines.join("\n");
        if report.len() > 4096 {
            return Err("Mini publication recovery report exceeds 4 KiB".into());
        }
        Ok((report, ids))
    }
    fn next_id(&mut self) -> Result<u64> {
        let id = self.journal.next_operation_id;
        self.journal.next_operation_id = id.checked_add(1).ok_or("operation ID exhausted")?;
        self.save()?;
        Ok(id)
    }
    fn command_output(&self, program: &Path, args: &[&str]) -> Result<()> {
        let output = Command::new(program)
            .args(args)
            .output()
            .map_err(|e| format!("{}: {e}", program.display()))?;
        if !output.status.success() {
            return Err(format!(
                "{} exited {}: {}",
                program.display(),
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        Ok(())
    }
    fn work_output(
        &self,
        program: &Path,
        args: &[&str],
    ) -> std::result::Result<(), custody_gate::CustodyError> {
        let mut command = Command::new(program);
        command.args(args);
        unsafe {
            command.pre_exec(|| {
                libc::umask(0o077);
                Ok(())
            });
        }
        let output = self
            .custody_gate
            .run_capture(&self.cancelled, &mut command)?;
        if !output.status.success() {
            return Err(custody_gate::CustodyError::Uncertain(io::Error::other(
                format!(
                    "{} exited {}: {}",
                    program.display(),
                    output.status,
                    String::from_utf8_lossy(&output.stderr).trim()
                ),
            )));
        }
        Ok(())
    }
    fn supervised_resource_read(
        &self,
        tool: &ToolTask,
        read: &resource_tools::AllowedResourceRead,
        nonce: u64,
    ) -> Result<Value> {
        resource_tools::read_resource_with(&self.config, tool, read, nonce, |command| {
            let output = self
                .custody_gate
                .run_capture(&self.cancelled, command)
                .map_err(|error| format!("supervised native resource read: {error}"))?;
            if !output.status.success() {
                return Err(format!(
                    "native resource read exited {}: {}",
                    output.status,
                    String::from_utf8_lossy(&output.stderr).trim()
                ));
            }
            Ok(())
        })
    }
    fn supervised_json_command(&self, mut command: Command) -> Result<Value> {
        unsafe {
            command.pre_exec(|| {
                libc::umask(0o077);
                Ok(())
            });
        }
        let output = self
            .custody_gate
            .run_capture(&self.cancelled, &mut command)
            .map_err(|error| format!("supervised native lookup: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "native historical lookup exited {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        serde_json::from_slice(&output.stdout)
            .map_err(|error| format!("native historical lookup JSON: {error}"))
    }
    fn resolve_shared_app(
        &mut self,
        tool: &ToolTask,
        reference: &shared_app_refs::SharedApplicationRef,
    ) -> Result<shared_app_refs::CurrentSharedApplication> {
        let mut nonces = [0u64; 4];
        for nonce in &mut nonces {
            *nonce = self.next_id()?;
        }
        shared_app_refs::resolve_with(&self.config, tool, reference, nonces, |operation| {
            match operation {
                shared_app_refs::NativeOperation::BirthLookup { call } => {
                    let socket = self
                        .config
                        .host_socket
                        .as_ref()
                        .ok_or("shared app birth lookup requires pinned hostSocket")?;
                    let mut command = Command::new(&self.config.mini);
                    command
                        .arg("historical-call-receipt-lookup")
                        .arg("--host")
                        .arg(&self.config.host)
                        .arg("--config")
                        .arg(&self.config.host_config)
                        .arg("--socket")
                        .arg(socket)
                        .arg("--call")
                        .arg(call)
                        .arg("--transaction-id")
                        .arg(&reference.birth.transaction_id)
                        .arg("--event-id")
                        .arg(&reference.birth.event_id)
                        .arg("--accepted-count")
                        .arg(&reference.birth.accepted_count)
                        .arg("--image-boundary")
                        .arg(&reference.birth.image_boundary)
                        .arg("--dir")
                        .arg(
                            self.config
                                .state_dir
                                .join(format!("shared-app-refs/birth-lookup-{:016}", nonces[0])),
                        );
                    self.supervised_json_command(command)
                }
                shared_app_refs::NativeOperation::IssueLookup { kind, ingress } => {
                    let socket = self
                        .config
                        .host_socket
                        .as_ref()
                        .ok_or("shared app issue lookup requires pinned hostSocket")?;
                    let mut command = Command::new(&self.config.mini);
                    command
                        .arg(kind.recipient_lookup_command())
                        .arg("--host")
                        .arg(&self.config.host)
                        .arg("--config")
                        .arg(&self.config.host_config)
                        .arg("--socket")
                        .arg(socket)
                        .arg("--ingress")
                        .arg(ingress)
                        .arg("--transaction-id")
                        .arg(&reference.issue.transaction_id)
                        .arg("--event-id")
                        .arg(&reference.issue.event_id)
                        .arg("--accepted-count")
                        .arg(&reference.issue.accepted_count)
                        .arg("--image-boundary")
                        .arg(&reference.issue.image_boundary)
                        .arg("--dir")
                        .arg(
                            self.config
                                .state_dir
                                .join(format!("shared-app-refs/issue-lookup-{:016}", nonces[1])),
                        );
                    self.supervised_json_command(command)
                }
                shared_app_refs::NativeOperation::SignedRead { read, nonce } => {
                    self.supervised_resource_read(tool, &read, nonce)
                }
            }
        })
    }
    fn query(&mut self) -> Result<Value> {
        let a = self.parent();
        self.query_as(&a)
    }
    fn query_as(&mut self, authority: &Authority) -> Result<Value> {
        let id = self.next_id()?;
        let dir = self.config.state_dir.join(format!("query-{id:016}"));
        fs::create_dir(&dir).map_err(|e| format!("query directory: {e}"))?;
        let intent = json!({"subject": authority.subject, "nonce": id.to_string(),
            "purpose": {"type":"query","kind":"object","target":authority.task,"view":"resource"},
            "grants":[{"kind":"object","target":authority.task,"capability":authority.query_capability}]});
        let intent_path = dir.join("intent-source.json");
        write_new(
            &intent_path,
            serde_json::to_string_pretty(&intent).unwrap().as_bytes(),
        )?;
        let cfg = &self.config;
        let query_attempt = dir.join("attempt");
        let mut args = vec![
            "query",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--intent",
            intent_path.to_str().ok_or("intent path UTF-8")?,
            "--key",
            authority.custody_key.to_str().ok_or("key path UTF-8")?,
            "--view",
            "resource",
            "--dir",
            query_attempt.to_str().ok_or("attempt path UTF-8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        self.command_output(&cfg.mini, &args)?;
        let attempt = dir.join("attempt");
        let view: Value = serde_json::from_slice(
            &fs::read(attempt.join("view.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        let challenge: Value = serde_json::from_slice(
            &fs::read(attempt.join("challenge.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        let grain = view
            .pointer("/page/grain")
            .ok_or("signed resource view has no grain")?;
        if grain.get("task").and_then(Value::as_str) != Some(authority.task.as_str()) {
            return Err("signed resource view names another task".into());
        }
        Ok(
            json!({"grain":grain, "targetRoot":view.pointer("/page/root"),
            "authorityRoot":challenge.pointer("/signing/0/authorityRoot"),
            "imageBoundary":challenge.get("imageBoundary"),
            "height":challenge.get("height")}),
        )
    }
    fn query_policy(&mut self) -> Result<Value> {
        let id = self.next_id()?;
        let dir = self.config.state_dir.join(format!("policy-query-{id:016}"));
        fs::create_dir(&dir).map_err(|e| format!("policy query directory: {e}"))?;
        let source = json!({"subject":self.config.subject,"nonce":id.to_string(),
            "purpose":{"type":"query","kind":"object","target":self.config.task,"view":"policy"},
            "grants":[{"kind":"object","target":self.config.task,
                "capability":self.config.query_capability}]});
        let path = dir.join("intent-source.json");
        write_new(&path, serde_json::to_string(&source).unwrap().as_bytes())?;
        let attempt = dir.join("attempt");
        let cfg = &self.config;
        let mut args = vec![
            "query",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--intent",
            path.to_str().ok_or("intent path UTF-8")?,
            "--key",
            cfg.custody_key.to_str().ok_or("key path UTF-8")?,
            "--view",
            "policy",
            "--dir",
            attempt.to_str().ok_or("attempt path UTF-8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        self.command_output(&cfg.mini, &args)?;
        let view: Value = serde_json::from_slice(
            &fs::read(attempt.join("view.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        let challenge: Value = serde_json::from_slice(
            &fs::read(attempt.join("challenge.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        if view.get("policyId").and_then(Value::as_str) != Some(cfg.task.as_str()) {
            return Err("signed policy view names another task".into());
        }
        Ok(json!({"view":view,"authorityRoot":challenge.pointer("/signing/0/authorityRoot")}))
    }
    fn managed_worker_subjects(&self) -> Result<Vec<String>> {
        let mut workers = Vec::new();
        if let Some(tool) = &self.config.tool_task {
            workers.push(tool.subject.clone());
        }
        if let Some(dispatch) = &self.config.dispatch_task {
            if workers.iter().any(|subject| subject == &dispatch.subject) {
                return Err("dispatch and tool witness subjects must be distinct".into());
            }
            workers.push(dispatch.subject.clone());
        }
        if let Some(provider) = &self.config.provider_task {
            if workers.iter().any(|subject| subject == &provider.subject) {
                return Err(
                    "provider witness subject must be distinct from tool and dispatch".into(),
                );
            }
            workers.push(provider.subject.clone());
        }
        Ok(workers)
    }
    fn renew_worker_policy(&mut self, attaching_from_paused: bool) -> Result<()> {
        let workers = self.managed_worker_subjects()?;
        if workers.is_empty() {
            return Ok(());
        }
        if self.journal.pending.is_some() {
            return Err("parent authority has an unresolved transition".into());
        }
        let parent = self.query()?;
        let generation = parent
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("signed parent generation absent")?;
        let status = parent
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("signed parent status absent")?;
        if (attaching_from_paused && status != "0") || (!attaching_from_paused && status != "2") {
            return Err("signed parent status does not match policy renewal phase".into());
        }
        // Fresh attach advances the grain generation. Install the new source
        // predicate before that transition, pinned to the generation it will
        // enter, so a controller crash after attach still admits interrupt.
        let generation = if attaching_from_paused {
            generation
                .parse::<u64>()
                .map_err(|_| "signed parent generation invalid")?
                .checked_add(1)
                .ok_or("signed parent generation overflow")?
                .to_string()
        } else {
            generation.to_owned()
        };
        let policy = self.query_policy()?;
        let view = policy.get("view").ok_or("signed policy view absent")?;
        self.require_managed_worker_policy(view, &workers, status, generation.as_str())?;
        let id = self.next_id()?;
        let mut source = json!({"subject":self.config.subject,"intentNonce":id.to_string(),
            "declarationNonce":id.to_string(),"task":self.config.task,
            "owner":self.config.subject,
            "workerGeneration":generation,
            "control":self.config.policy_control_capability.as_ref().ok_or("policy control capability absent")?,
            "domain":view.get("domain").ok_or("policy domain absent")?,
            "semantics":view.get("semantics").ok_or("policy semantics absent")?,
            "expectedPreRoot":policy.get("authorityRoot").ok_or("policy authority root absent")?,
            "expectedVersion":view.get("version").ok_or("policy version absent")?,
            "expectedAddress":view.get("address").ok_or("policy address absent")?,
            "grants":[{"kind":"object","target":self.config.task,
                "capability":self.config.query_capability}]});
        if workers.len() == 1 {
            source["workerSubject"] = json!(workers[0]);
        } else {
            source["workerSubjects"] = json!(workers);
        }
        let path = self
            .config
            .state_dir
            .join(format!("policy-source-{id:016}.json"));
        write_new(
            &path,
            serde_json::to_string_pretty(&source).unwrap().as_bytes(),
        )?;
        let attempt = self
            .config
            .state_dir
            .join(format!("policy-attempt-{id:016}"));
        self.journal.pending = Some(Pending {
            operation_id: id,
            operation: "policy install".into(),
            attempt: attempt.clone(),
            uncertain: false,
            publication: None,
        });
        self.save()?;
        let cfg = &self.config;
        let mut args = vec![
            "submit",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--intent",
            path.to_str().ok_or("policy source path UTF-8")?,
            "--intent-kind",
            "grain-policy-install-intent",
            "--key",
            cfg.custody_key.to_str().ok_or("key path UTF-8")?,
            "--dir",
            attempt.to_str().ok_or("attempt path UTF-8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        let result = self.command_output(&cfg.mini, &args);
        match result {
            Ok(()) => {
                self.journal.pending = None;
                self.journal.managed_law_generation = Some(generation.clone());
                self.save()
            }
            Err(error) => {
                let refusal = fs::read(attempt.join("outcome.json"))
                    .ok()
                    .and_then(|b| serde_json::from_slice::<Value>(&b).ok())
                    .is_some_and(|v| v.get("type").and_then(Value::as_str) == Some("refused"));
                if refusal {
                    self.journal.pending = None;
                } else if let Some(p) = &mut self.journal.pending {
                    p.uncertain = true;
                }
                self.save()?;
                Err(format!(
                    "worker policy renewal unresolved or refused: {error}"
                ))
            }
        }
    }
    fn require_managed_worker_policy(
        &mut self,
        view: &Value,
        workers: &[String],
        status: &str,
        desired_generation: &str,
    ) -> Result<()> {
        let predicate = view
            .get("predicate")
            .ok_or("signed policy has no predicate")?;
        let current_generation = desired_generation
            .parse::<u64>()
            .map_err(|_| "desired worker generation invalid")?;
        let own = self
            .journal
            .managed_law_generation
            .as_deref()
            .and_then(|value| value.parse::<u64>().ok());
        let candidates = managed_law_candidates(status, current_generation, own)?;
        let id = self.next_id()?;
        let dir = self.config.state_dir.join(format!("policy-check-{id:016}"));
        fs::create_dir(&dir).map_err(|e| format!("policy check directory: {e}"))?;
        let observed_source = dir.join("signed-predicate.json");
        write_new(
            &observed_source,
            &serde_json::to_vec(predicate).map_err(|e| e.to_string())?,
        )?;
        let observed_bytes = dir.join("signed-predicate.bin");
        self.author_grain_policy_bytes("predicate", &observed_source, &observed_bytes)?;
        let observed = bounded_policy_bytes(&observed_bytes)?;
        for candidate in candidates {
            let source =
                managed_worker_policy_source(&self.config.subject, workers, &candidate.to_string());
            let path = dir.join(format!("managed-{candidate}.json"));
            write_new(
                &path,
                &serde_json::to_vec(&source).map_err(|e| e.to_string())?,
            )?;
            let output = dir.join(format!("managed-{candidate}.bin"));
            self.author_grain_policy_bytes("grain-policy", &path, &output)?;
            if bounded_policy_bytes(&output)? == observed {
                return Ok(());
            }
        }
        Err("signed policy is not a supported exact managed worker law; explicit owner audit and policy upgrade required".into())
    }
    fn author_grain_policy_bytes(&self, kind: &str, input: &Path, output: &Path) -> Result<()> {
        let cfg = &self.config;
        let mut args = vec![
            "author",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--kind",
            kind,
            "--input",
            input.to_str().ok_or("policy source path UTF-8")?,
            "--output",
            output.to_str().ok_or("policy output path UTF-8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        self.command_output(&cfg.mini, &args)
    }
    fn transition(&mut self, op: Value, label: &str, payload: &str) -> Result<()> {
        let authority = self.parent();
        self.transition_as(&authority, op, label, payload, vec![])
    }
    fn mark_hold(&mut self, tool: bool, reserve: &str, charge: &str) -> Result<()> {
        let authority = if tool { self.tool()? } else { self.parent() };
        self.mark_hold_as(
            if tool {
                AuthoritySlot::Tool
            } else {
                AuthoritySlot::Parent
            },
            &authority,
            reserve,
            charge,
        )
    }
    fn mark_hold_as(
        &mut self,
        slot: AuthoritySlot,
        authority: &Authority,
        reserve: &str,
        charge: &str,
    ) -> Result<()> {
        let observed = self.query_as(authority)?;
        let hold = HeldCharge {
            reserve: reserve.to_owned(),
            charge: charge.to_owned(),
            before_generation: observed
                .pointer("/grain/generation")
                .and_then(Value::as_str)
                .ok_or("pre-reserve generation absent")?
                .to_owned(),
            before_target_root: observed
                .get("targetRoot")
                .and_then(Value::as_str)
                .ok_or("pre-reserve target root absent")?
                .to_owned(),
            reserve_attempt: None,
            reserve_confirmed: false,
            reserve_refused: false,
            reserve_boundary: None,
            reserve_call_sha256: None,
            reserve_source_sha256: None,
            reserve_outcome_path: None,
            reserve_outcome_sha256: None,
            reserve_anchor: None,
        };
        *self.journal.hold_for_mut(slot) = Some(hold);
        self.save()
    }
    fn record_reserve_confirmation(
        &mut self,
        slot: AuthoritySlot,
        attempt: &Path,
        outcome_json: &Path,
    ) -> Result<()> {
        let receipt: Value = serde_json::from_slice(
            &fs::read(outcome_json).map_err(|e| format!("reserve receipt missing: {e}"))?,
        )
        .map_err(|e| format!("reserve receipt invalid: {e}"))?;
        if receipt.get("type").and_then(Value::as_str) != Some("confirmed") {
            return Err("reserve has no confirmed native receipt".into());
        }
        let boundary = receipt
            .get("imageBoundary")
            .and_then(Value::as_str)
            .ok_or("confirmed reserve lacks image boundary")?
            .to_owned();
        let provider_evidence = if matches!(slot, AuthoritySlot::Provider | AuthoritySlot::Dispatch)
        {
            let anchor = ReserveAnchor::from_confirmed(&receipt)?;
            let call = attempt.join("call.bin");
            let outcome = outcome_json.with_extension("bin");
            for file in [&call, &outcome] {
                if !fs::symlink_metadata(file)
                    .map_err(|e| format!("{}: {e}", file.display()))?
                    .file_type()
                    .is_file()
                {
                    return Err(format!(
                        "reserve evidence is not a regular file: {}",
                        file.display()
                    ));
                }
            }
            Some((
                sha256_file(&call)?,
                outcome.clone(),
                sha256_file(&outcome)?,
                anchor,
            ))
        } else {
            None
        };
        let dispatch_source_hash = if slot == AuthoritySlot::Dispatch {
            let name = attempt
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or("dispatch reserve attempt name invalid")?;
            let encoded = name
                .strip_prefix("attempt-")
                .ok_or("dispatch reserve attempt name differs")?;
            let id = encoded
                .parse::<u64>()
                .map_err(|_| "dispatch reserve operation ID malformed")?;
            if encoded.len() != 16
                || attempt != self.config.state_dir.join(format!("attempt-{id:016}"))
            {
                return Err("dispatch reserve attempt path differs from source".into());
            }
            Some(sha256_file(
                &self.config.state_dir.join(format!("source-{id:016}.json")),
            )?)
        } else {
            None
        };
        let hold = self
            .journal
            .hold_for_mut(slot)
            .as_mut()
            .ok_or("reserve marker disappeared")?;
        if hold.reserve_attempt.as_deref() != Some(attempt) {
            return Err("confirmed reserve attempt differs from durable held origin".into());
        }
        hold.reserve_confirmed = true;
        hold.reserve_boundary = Some(boundary);
        hold.reserve_source_sha256 = dispatch_source_hash;
        if let Some((call_hash, outcome, outcome_hash, anchor)) = provider_evidence {
            hold.reserve_call_sha256 = Some(call_hash);
            hold.reserve_outcome_path = Some(outcome);
            hold.reserve_outcome_sha256 = Some(outcome_hash);
            hold.reserve_anchor = Some(anchor);
        }
        Ok(())
    }
    fn transition_as(
        &mut self,
        authority: &Authority,
        op: Value,
        label: &str,
        payload: &str,
        publications: Vec<Value>,
    ) -> Result<()> {
        self.transition_as_with_witness(authority, op, label, payload, publications, None)
    }
    fn transition_as_with_witness(
        &mut self,
        authority: &Authority,
        op: Value,
        label: &str,
        payload: &str,
        publications: Vec<Value>,
        witness_capabilities: Option<(String, String)>,
    ) -> Result<()> {
        let work_submit = label == "reserve"
            || label == "tool attach"
            || label == "tool reserve"
            || label == "dispatch attach"
            || label == "dispatch reserve"
            || label == "provider attach"
            || label == "provider reserve"
            || (label == "tool settle" && !publications.is_empty());
        let slot = if authority.task == self.config.task {
            AuthoritySlot::Parent
        } else if self
            .config
            .tool_task
            .as_ref()
            .is_some_and(|tool| tool.task == authority.task)
        {
            AuthoritySlot::Tool
        } else if self
            .config
            .dispatch_task
            .as_ref()
            .is_some_and(|dispatch| dispatch.task == authority.task)
        {
            AuthoritySlot::Dispatch
        } else if self
            .config
            .provider_task
            .as_ref()
            .is_some_and(|provider| provider.task == authority.task)
        {
            AuthoritySlot::Provider
        } else {
            return Err("transition authority is not configured".into());
        };
        if self.journal.pending_for(slot).is_some() {
            return Err("this Mini authority has an unresolved transition".into());
        }
        let observed = self.query_as(authority)?;
        let before = observed.get("grain").ok_or("missing observed grain")?;
        let reserving = op.get("type").and_then(Value::as_str) == Some("reserve");
        if reserving {
            let hold = self
                .journal
                .hold_for(slot)
                .as_ref()
                .ok_or("reserve has no durable charge marker")?;
            if observed.get("targetRoot").and_then(Value::as_str)
                != Some(hold.before_target_root.as_str())
                || before.get("generation").and_then(Value::as_str)
                    != Some(hold.before_generation.as_str())
            {
                return Err("signed pre-reserve grain differs from held operation origin".into());
            }
        }
        let id = self.next_id()?;
        let joint = !publications.is_empty() || witness_capabilities.is_some();
        let parent_witness = if joint {
            let (parent_capability, parent_observe_capability) =
                if let Some(caps) = witness_capabilities {
                    caps
                } else {
                    let t = self
                        .config
                        .tool_task
                        .as_ref()
                        .ok_or("tool task absent for joint publication")?;
                    (
                        t.parent_capability.clone(),
                        t.parent_observe_capability.clone(),
                    )
                };
            let mut witness = self
                .journal
                .prompt_witness
                .clone()
                .ok_or("parent prompt witness absent")?;
            witness["capability"] = json!(parent_capability);
            witness["observeCapability"] = json!(parent_observe_capability);
            Some(witness)
        } else {
            None
        };
        // The native observation footprint is exact: primary target, optional
        // prepended parent witness, then publications, one observe grant each.
        let parent_observation = parent_witness
            .as_ref()
            .map(|witness| {
                witness["observeCapability"]
                    .as_str()
                    .map(|capability| (self.config.task.as_str(), capability))
                    .ok_or("parent witness observe capability absent")
            })
            .transpose()?;
        let grants = grain_observation_grants(authority, parent_observation, &publications)?;
        let mut grain = json!({"task":authority.task,"subject":authority.subject,
            "capability":authority.capability,"schemaVersion":"1",
            "expectedAuthorityRoot":observed.get("authorityRoot").ok_or("missing authority root")?,
            "expectedTargetRoot":observed.get("targetRoot").ok_or("missing target root")?,
            "context":{"operationId":id.to_string(),"payload":payload},
            "before":{"generation":before.get("generation"),"status":before.get("status"),
                "remaining":before.get("remaining"),"reserved":before.get("reserved")},
            "operation":op,"publications":publications,
            "observeCapability":authority.query_capability});
        if let Some(witness) = parent_witness {
            grain["parentWitness"] = witness;
        }
        let source = json!({"grain":grain,"grants":grants,"intentNonce":id.to_string()});
        let publication = if slot == AuthoritySlot::Tool
            && label == "tool settle"
            && source["grain"]["publications"]
                .as_array()
                .is_some_and(|targets| !targets.is_empty())
        {
            while self.journal.publication_receipts.len() >= 32 {
                let Some(index) = self
                    .journal
                    .publication_receipts
                    .iter()
                    .position(|record| record.reported)
                else {
                    return Err(
                        "publication recovery journal is full of unreported receipts".into(),
                    );
                };
                self.journal.publication_receipts.remove(index);
            }
            let (work_operation_id, session_id, work_origin) = self.current_work_origin()?;
            let targets = source["grain"]["publications"]
                .as_array()
                .ok_or("publication targets absent")?
                .iter()
                .map(|target| {
                    let id = target["target"]
                        .as_str()
                        .ok_or("publication target absent")?;
                    decimal(id, "publication target")?;
                    Ok(id.to_owned())
                })
                .collect::<Result<Vec<_>>>()?;
            Some((work_operation_id, session_id, work_origin, targets))
        } else {
            None
        };
        let attempt = self.config.state_dir.join(format!("attempt-{id:016}"));
        let source_path = self.config.state_dir.join(format!("source-{id:016}.json"));
        write_new(
            &source_path,
            serde_json::to_string_pretty(&source).unwrap().as_bytes(),
        )?;
        let publication = publication
            .map(
                |(prompt_operation_id, session_id, work_origin, targets)| -> Result<PublicationPending> {
                    Ok(PublicationPending {
                        prompt_operation_id,
                        session_id,
                        work_origin,
                        source_sha256: sha256_file(&source_path)?,
                        targets,
                    })
                },
            )
            .transpose()?;
        let pending = Some(Pending {
            operation_id: id,
            operation: label.into(),
            attempt: attempt.clone(),
            uncertain: false,
            publication,
        });
        *self.journal.pending_for_mut(slot) = pending;
        if reserving {
            self.journal
                .hold_for_mut(slot)
                .as_mut()
                .ok_or("reserve marker disappeared")?
                .reserve_attempt = Some(attempt.clone());
        }
        self.save()?;
        let cfg = &self.config;
        let mut args = vec![
            "submit",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--intent",
            source_path.to_str().ok_or("source path UTF-8")?,
            "--intent-kind",
            "grain-intent",
            "--key",
            authority.custody_key.to_str().ok_or("key path UTF-8")?,
            "--dir",
            attempt.to_str().ok_or("attempt path UTF-8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        let result = if work_submit {
            match self.work_output(&cfg.mini, &args) {
                Ok(()) => Ok(()),
                Err(custody_gate::CustodyError::BeforeSpawn) => {
                    // The short spawn gate proves there was no Mini child.
                    // Do not leave a phantom pending call or bill a held
                    // delegated allowance for an unsubmitted tool action.
                    *self.journal.pending_for_mut(slot) = None;
                    if let Some(hold) = self.journal.hold_for_mut(slot).as_mut() {
                        hold.charge = "0".into();
                        if reserving {
                            hold.reserve_attempt = None;
                        }
                    }
                    self.save()?;
                    return Err(format!("{label} canceled before Mini custody spawn"));
                }
                Err(error) => Err(error.to_string()),
            }
        } else {
            self.command_output(&cfg.mini, &args)
        };
        match result {
            Ok(()) => {
                if let Some(record) = self.confirmed_publication_receipt(
                    self.journal
                        .pending_for(slot)
                        .as_ref()
                        .ok_or("pending attempt absent")?,
                    &attempt.join("outcome.json"),
                )? {
                    self.journal.publication_receipts.push(record);
                }
                if reserving {
                    self.record_reserve_confirmation(
                        slot,
                        &attempt,
                        &attempt.join("outcome.json"),
                    )?;
                }
                if slot == AuthoritySlot::Provider
                    && op.get("type").and_then(Value::as_str) == Some("settle")
                {
                    let pending = self
                        .journal
                        .pending_for(slot)
                        .as_ref()
                        .ok_or("provider settlement pending disappeared")?;
                    self.journal.provider_settlement = Some(
                        self.provider_settlement_record(pending, &attempt.join("outcome.json"))?,
                    );
                }
                if slot == AuthoritySlot::Dispatch
                    && op.get("type").and_then(Value::as_str) == Some("settle")
                {
                    let pending = self
                        .journal
                        .pending_for(slot)
                        .as_ref()
                        .ok_or("dispatch settlement pending disappeared")?;
                    let settled =
                        self.dispatch_settlement_record(pending, &attempt.join("outcome.json"))?;
                    self.journal
                        .dispatch_attempt
                        .as_mut()
                        .ok_or("dispatch settlement lost retained attempt")?
                        .settlement = Some(settled);
                }
                *self.journal.pending_for_mut(slot) = None;
                if op.get("type").and_then(Value::as_str) == Some("settle") {
                    *self.journal.hold_for_mut(slot) = None;
                    if slot == AuthoritySlot::Parent {
                        self.journal.settlement_due = None;
                    }
                }
                self.save()?;
                Ok(())
            }
            Err(e) => {
                // A source/authorization refusal with an explicit decoded
                // outcome is definitive. Preserve its evidence and allow a
                // fresh read; no child was dispatched for this transition.
                let explicit = fs::read(attempt.join("outcome.json"))
                    .ok()
                    .and_then(|b| serde_json::from_slice::<Value>(&b).ok());
                if explicit
                    .as_ref()
                    .and_then(|v| v.get("type"))
                    .and_then(Value::as_str)
                    == Some("refused")
                {
                    if reserving {
                        self.journal
                            .hold_for_mut(slot)
                            .as_mut()
                            .ok_or("reserve marker disappeared")?
                            .reserve_refused = true;
                    }
                    *self.journal.pending_for_mut(slot) = None;
                    self.save()?;
                    return Err(format!("{label} refused by Mini: {}", explicit.unwrap()));
                }
                if !attempt.join("call.bin").is_file() {
                    let pre_submit = inspected_pre_submit_refusal(&self.config, &attempt);
                    if let Ok(Some(refusal)) = pre_submit.as_ref() {
                        if reserving {
                            self.journal
                                .hold_for_mut(slot)
                                .as_mut()
                                .ok_or("reserve marker disappeared")?
                                .reserve_refused = true;
                        }
                        *self.journal.pending_for_mut(slot) = None;
                        self.save()?;
                        return Err(format!("{label} refused by Mini: {refusal}"));
                    }
                    // A missing file after subprocess exit is still not a
                    // negative native receipt: an older client/host could
                    // have sent the call before its directory entry became
                    // durable. Keep the exact pending attempt and hold.
                    if let Some(p) = self.journal.pending_for_mut(slot) {
                        p.uncertain = true;
                    }
                    self.save()?;
                    let detail = match pre_submit {
                        Ok(None) => "no durable prepare-refusal marker".to_owned(),
                        Ok(Some(_)) => "unexpected prepare-refusal disposition".to_owned(),
                        Err(reason) => reason,
                    };
                    return Err(format!("{label} has no retained call.bin after custody failure; {detail}; disposition requires audit: {e}"));
                }
                if let Some(p) = self.journal.pending_for_mut(slot) {
                    p.uncertain = true;
                }
                self.save()?;
                Err(format!(
                    "{label} unresolved; retained attempt {}: {e}",
                    attempt.display()
                ))
            }
        }
    }
    fn handle_tool(&mut self, request: mcp::BrokerRequest, broker: &mcp::BrokerEndpoint) {
        if request.prompt_epoch != 1 {
            let _ = request.reply.send(json!({"isError":true,
                "text":"tool request was queued outside the active prompt"}));
            return;
        }
        let outcome = self.tool_call(&request.name, &request.arguments);
        if request.name == "mini_create_application" && outcome.is_ok() {
            // Refresh discovery before Hermes sees the successful birth
            // receipt. Session is also advertised from prompt start because
            // this unforked worker may cache its first tools/list response.
            if let Err(error) = self
                .tool_catalog()
                .and_then(|catalog| broker.replace_catalog(catalog))
            {
                self.emit(format!(
                    "MCP catalog refresh failed after retained app birth: {error}\n"
                ));
            }
        }
        let response = match outcome {
            Ok(value) => json!({"isError":false,"text":value.to_string()}),
            Err(error) => json!({"isError":true,"text":error}),
        };
        let _ = request.reply.send(response);
    }
    fn begin_application_api(
        &mut self,
        arguments: &Value,
        reply: mpsc::Sender<Value>,
        prompt_epoch: Option<u64>,
        raw_worker_reply: bool,
    ) -> Result<ActiveApplicationApi> {
        if (self.foreground_operation.is_none() && prompt_epoch != Some(1))
            || (self.foreground_operation.is_some() && prompt_epoch.is_some())
            || (!self.prompt_active && self.foreground_operation.is_none())
            || self.cancelled.load(Ordering::SeqCst)
            || self.journal.connection == Connection::Fenced
            || (self.journal.child.is_none() && self.foreground_operation.is_none())
            || self.journal.application_api_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err(
                "application API caller is busy, fenced, or has an unresolved dispatch".into(),
            );
        }
        let tool = self.config.tool_task.as_ref().ok_or("toolTask absent")?;
        let lifetime_names = tool
            .allowed_application_lifetime_routes
            .iter()
            .map(|route| route.name.clone())
            .collect::<Vec<_>>();
        let mut all_names = tool
            .allowed_application_api_routes
            .iter()
            .map(|route| route.name.clone())
            .collect::<Vec<_>>();
        all_names.extend(lifetime_names);
        let selected = application_api_tools::parse_input(arguments, &all_names)?;
        if let Some(route) = tool
            .allowed_application_lifetime_routes
            .iter()
            .find(|route| route.name == selected.application)
            .cloned()
        {
            return self.begin_application_lifetime_api(selected, route, reply, raw_worker_reply);
        }
        if raw_worker_reply {
            return Err("Git worker raw response requires a lifetime route".into());
        }
        let expected_host = tool
            .agent_api_host_sha256
            .as_deref()
            .ok_or("application API event21 Host pin is absent; agent delivery is unavailable")?;
        if self.config.host_socket.is_none() || sha256_file(&self.config.host)? != expected_host {
            return Err("application API event21 Host image or socket differs from pin".into());
        }
        let routes = &tool.allowed_application_api_routes;
        let allowed = routes
            .iter()
            .map(|route| route.name.clone())
            .collect::<Vec<_>>();
        let input = application_api_tools::parse_input(arguments, &allowed)?;
        let route = routes
            .iter()
            .find(|route| route.name == input.application)
            .ok_or("application API route is absent")?
            .clone();
        // These retained receipts locate the operator-selected app/session.
        // They are not an agent dispatch grant: the resident host must obtain
        // a fresh event21 permit for this exact request and purse before fd3.
        let registered = tool
            .registered_shared_applications
            .iter()
            .find(|reference| reference.name == route.name);
        if let Some(reference) = registered {
            if reference.app_target != route.app_resource
                || reference.ticket_target != route.ticket_resource
            {
                return Err("application API route differs from registered app/ticket".into());
            }
        } else if self
            .verified_born_named(&route.name)?
            .is_none_or(|born| born.target != route.app_resource)
        {
            return Err("application API route has no confirmed local app birth".into());
        }
        if self
            .verified_born_target("object", &route.session_resource)?
            .is_none()
        {
            return Err("application API route has no confirmed local session birth".into());
        }
        let parent = self.query()?;
        if route.parent_task != self.config.task
            || parent.pointer("/grain/generation").and_then(Value::as_str)
                != Some(route.parent_generation.as_str())
            || !matches!(
                parent.pointer("/grain/status").and_then(Value::as_str),
                Some("3" | "4")
            )
        {
            return Err("application API route differs from current signed parent".into());
        }
        let operation_id = self.next_id()?;
        self.application_api_send_gate.reset()?;
        let dispatch = application_api_tools::dispatch_request(operation_id, &input);
        let bytes = serde_json::to_vec(&dispatch).map_err(|error| error.to_string())?;
        let path = self
            .config
            .state_dir
            .join(format!("application-api-{operation_id:016}.json"));
        write_new(&path, &bytes)?;
        self.journal.application_api_attempt = Some(ApplicationApiAttempt {
            operation_id,
            route_name: route.name.clone(),
            request_path: path,
            request_sha256: sha256_bytes(&bytes)?,
            phase: ApplicationApiPhase::Prepared,
            binding_sha256: None,
            host_invocation: None,
            operation_fingerprint: None,
            lifetime_committed_receipt: None,
            lifetime_settled_response_sha256: None,
            lifetime_settlement: None,
            reply_path: None,
            reply_sha256: None,
            reported: false,
        });
        self.save()?;
        let deadline = Instant::now() + Duration::from_secs(1800);
        let hello = match application_api_tools::start_exchange_once(
            &route.socket_path,
            route.host_uid,
            application_api_tools::hello_request(),
            deadline,
            self.cancelled.clone(),
        ) {
            Ok(worker) => worker,
            Err(error) => {
                self.finish_application_api_no_dispatch(operation_id)?;
                return Err(format!("application API hello: {error:?}"));
            }
        };
        Ok(ActiveApplicationApi {
            operation_id,
            route: ApplicationApiRoute::V2(Box::new(route)),
            lifetime_input: None,
            request: dispatch,
            reply,
            step: ApplicationApiStep::Hello(hello),
            deadline,
            raw_worker_reply,
        })
    }

    fn begin_application_lifetime_api(
        &mut self,
        input: application_api_tools::HttpInput,
        route: application_api_tools::LifetimeRoutePin,
        reply: mpsc::Sender<Value>,
        raw_worker_reply: bool,
    ) -> Result<ActiveApplicationApi> {
        let tool = self.config.tool_task.as_ref().ok_or("toolTask absent")?;
        let expected_host = tool
            .lifetime_api_host_sha256
            .as_deref()
            .ok_or("lifetime application Host pin absent")?;
        if self.config.host_socket.is_none() || sha256_file(&self.config.host)? != expected_host {
            return Err("lifetime application Host image or socket differs from pin".into());
        }
        let registered = tool
            .registered_shared_applications
            .iter()
            .find(|reference| reference.name == route.name);
        if let Some(reference) = registered {
            if reference.app_target != route.app_resource
                || reference.ticket_target != route.ticket_resource
            {
                return Err("lifetime route differs from registered app/ticket".into());
            }
        } else if self
            .verified_born_named(&route.name)?
            .is_none_or(|born| born.target != route.app_resource)
        {
            return Err("lifetime route has no confirmed local app birth".into());
        }
        if self
            .verified_born_target("object", &route.session_resource)?
            .is_none()
        {
            return Err("lifetime route has no confirmed local session birth".into());
        }
        let parent = self.query()?;
        if route.parent_task != self.config.task
            || !matches!(
                parent.pointer("/grain/status").and_then(Value::as_str),
                Some("3" | "4")
            )
            || self.journal.prompt_witness.is_none()
        {
            return Err("lifetime API parent is not currently reserved".into());
        }
        let operation_id = self.next_id()?;
        self.application_api_send_gate.reset()?;
        // Hello has no operation effect. The exact dispatch frame, including
        // its stable binding digest, is created and saved only after Hello is
        // checked. A crash during Hello therefore leaves no sendable attempt.
        let deadline = Instant::now() + Duration::from_secs(1800);
        let hello = application_api_tools::start_exchange_once(
            &route.socket_path,
            route.host_uid,
            application_api_tools::lifetime_hello_request(),
            deadline,
            self.cancelled.clone(),
        )
        .map_err(|error| format!("lifetime application Hello: {error:?}"))?;
        Ok(ActiveApplicationApi {
            operation_id,
            route: ApplicationApiRoute::Lifetime(Box::new(route)),
            lifetime_input: Some(input),
            request: Value::Null,
            reply,
            step: ApplicationApiStep::Hello(hello),
            deadline,
            raw_worker_reply,
        })
    }

    fn poll_lifetime_application_api(
        &mut self,
        active: &mut Option<ActiveApplicationApi>,
    ) -> Result<()> {
        let Some(call) = active.as_mut() else {
            return Ok(());
        };
        let ApplicationApiRoute::Lifetime(route) = &call.route else {
            return Err("v2 route entered lifetime API poll".into());
        };
        let Some(result) = (match &call.step {
            ApplicationApiStep::Hello(worker) | ApplicationApiStep::Dispatch(worker) => {
                worker.poll()
            }
        }) else {
            return Ok(());
        };
        let result = match result {
            Ok(value) => value,
            Err(error) => {
                let before_send = matches!(call.step, ApplicationApiStep::Hello(_))
                    || matches!(error, application_api_tools::TransportError::BeforeSend(_));
                if !matches!(call.step, ApplicationApiStep::Hello(_)) {
                    if before_send {
                        self.finish_application_api_no_dispatch(call.operation_id)?;
                    } else if let Some(attempt) = self.journal.application_api_attempt.as_mut() {
                        attempt.phase = ApplicationApiPhase::Uncertain;
                        self.save()?;
                    }
                }
                let _ = call.reply.send(json!({"isError":true,
                    "text":format!("lifetime API transport result: {error:?}")}));
                *active = None;
                return Ok(());
            }
        };
        if matches!(call.step, ApplicationApiStep::Hello(_)) {
            let (binding, invocation) =
                match application_api_tools::verify_lifetime_binding_reply(result, route) {
                    Ok(value) => value,
                    Err(error) => {
                        let _ = call.reply.send(json!({"isError":true,"text":error}));
                        *active = None;
                        return Ok(());
                    }
                };
            let input = call
                .lifetime_input
                .take()
                .ok_or("lifetime HTTP input disappeared before dispatch")?;
            let dispatch = application_api_tools::lifetime_dispatch_request(
                call.operation_id,
                &binding,
                &input,
            )?;
            let bytes = serde_json::to_vec(&dispatch)
                .map_err(|error| format!("lifetime forward JSON: {error}"))?;
            let path = self
                .config
                .state_dir
                .join(format!("application-api-{:016}.json", call.operation_id));
            write_new(&path, &bytes)?;
            self.journal.application_api_attempt = Some(ApplicationApiAttempt {
                operation_id: call.operation_id,
                route_name: route.name.clone(),
                request_path: path,
                request_sha256: sha256_bytes(&bytes)?,
                phase: ApplicationApiPhase::BindingVerified,
                binding_sha256: Some(binding),
                host_invocation: Some(invocation),
                operation_fingerprint: None,
                lifetime_committed_receipt: None,
                lifetime_settled_response_sha256: None,
                lifetime_settlement: None,
                reply_path: None,
                reply_sha256: None,
                reported: false,
            });
            self.save()?;
            self.journal
                .application_api_attempt
                .as_mut()
                .ok_or("lifetime forward attempt disappeared")?
                .phase = ApplicationApiPhase::DispatchStarted;
            self.save()?;
            let worker = match application_api_tools::start_dispatch_once(
                &route.socket_path,
                route.host_uid,
                dispatch.clone(),
                call.deadline,
                self.application_api_send_gate.clone(),
                self.cancelled.clone(),
            ) {
                Ok(worker) => worker,
                Err(error) => {
                    self.finish_application_api_no_dispatch(call.operation_id)?;
                    let _ = call.reply.send(json!({"isError":true,
                        "text":format!("lifetime forward spawn: {error:?}")}));
                    *active = None;
                    return Ok(());
                }
            };
            call.request = dispatch;
            call.step = ApplicationApiStep::Dispatch(worker);
            return Ok(());
        }
        let attempt = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("lifetime forward attempt absent on reply")?;
        let field = |name: &str| -> Result<&str> {
            result
                .get(name)
                .and_then(Value::as_str)
                .ok_or_else(|| format!("lifetime response {name} absent"))
        };
        let kind = field("type")?;
        if field("protocol")? != "mini-spk-agent-api-v3"
            || field("operationId")? != call.operation_id.to_string()
            || Some(field("bindingSha256")?) != attempt.binding_sha256.as_deref()
        {
            return Err("lifetime response differs from retained forward binding".into());
        }
        if kind == "refused-v3" {
            if result.get("operationFingerprint").is_some()
                || attempt.operation_fingerprint.is_some()
                || self.journal.dispatch_attempt.is_some()
                || self.journal.dispatch_hold.is_some()
                || self.journal.dispatch_pending.is_some()
            {
                return Err("lifetime refusal is not proven pre-reserve".into());
            }
            self.finish_application_api_no_dispatch(call.operation_id)?;
            let _ = call
                .reply
                .send(json!({"isError":true,"text":result.to_string()}));
            *active = None;
            return Ok(());
        }
        let fingerprint = attempt
            .operation_fingerprint
            .as_deref()
            .ok_or("lifetime response lacks retained source-derived fingerprint")?;
        if field("operationFingerprint")? != fingerprint
            || !matches!(kind, "http-v3" | "uncertain-v3")
        {
            return Err("lifetime response differs from exact dispatch fingerprint".into());
        }
        if kind == "http-v3" {
            verified_lifetime_definite_reply(
                attempt,
                &result,
                self.journal.dispatch_attempt.is_some()
                    || self.journal.dispatch_hold.is_some()
                    || self.journal.dispatch_pending.is_some(),
            )?;
        }
        let path = self.config.state_dir.join(format!(
            "application-api-reply-{:016}.json",
            call.operation_id
        ));
        let bytes = serde_json::to_vec(&result)
            .map_err(|error| format!("lifetime response JSON: {error}"))?;
        write_new(&path, &bytes)?;
        let definite = kind == "http-v3";
        let saved = self.journal.application_api_attempt.as_mut().unwrap();
        saved.reply_path = Some(path);
        saved.reply_sha256 = Some(sha256_bytes(&bytes)?);
        saved.phase = if definite {
            ApplicationApiPhase::Definite
        } else {
            ApplicationApiPhase::Uncertain
        };
        self.save()?;
        let shown = if definite && !call.raw_worker_reply {
            match application_api_tools::present_lifetime_http(&result) {
                Ok(value) => value,
                Err(error) => {
                    self.journal.application_api_attempt.as_mut().unwrap().phase =
                        ApplicationApiPhase::Uncertain;
                    self.save()?;
                    let _ = call.reply.send(json!({"isError":true,
                        "text":format!("verified lifetime HTTP reply has no safe model presentation: {error}")}));
                    *active = None;
                    return Ok(());
                }
            }
        } else {
            result.clone()
        };
        let delivered = call
            .reply
            .send(json!({"isError":!definite,"text":shown.to_string()}))
            .is_ok();
        if definite && delivered {
            let mut finished = self.journal.application_api_attempt.take().unwrap();
            finished.reported = true;
            if self.journal.application_api_history.len() >= 16 {
                self.journal.application_api_history.remove(0);
            }
            self.journal.application_api_history.push(finished);
            self.save()?;
        }
        *active = None;
        Ok(())
    }

    fn finish_application_api_no_dispatch(&mut self, operation_id: u64) -> Result<()> {
        let attempt = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("application API no-dispatch attempt disappeared")?;
        if attempt.operation_id != operation_id
            || !matches!(
                attempt.phase,
                ApplicationApiPhase::Prepared
                    | ApplicationApiPhase::BindingVerified
                    | ApplicationApiPhase::DispatchStarted
            )
            || attempt.reply_path.is_some()
        {
            return Err("application API no-dispatch phase differs".into());
        }
        let mut finished = self.journal.application_api_attempt.take().unwrap();
        finished.phase = ApplicationApiPhase::NoDispatch;
        finished.reported = true;
        if self.journal.application_api_history.len() >= 16 {
            self.journal.application_api_history.remove(0);
        }
        self.journal.application_api_history.push(finished);
        self.save()
    }

    fn poll_application_api(&mut self, active: &mut Option<ActiveApplicationApi>) -> Result<()> {
        if active
            .as_ref()
            .is_some_and(|call| matches!(call.route, ApplicationApiRoute::Lifetime(_)))
        {
            return self.poll_lifetime_application_api(active);
        }
        let Some(call) = active.as_mut() else {
            return Ok(());
        };
        let completed = match &call.step {
            ApplicationApiStep::Hello(worker) | ApplicationApiStep::Dispatch(worker) => {
                worker.poll()
            }
        };
        let Some(result) = completed else {
            return Ok(());
        };
        let result = match result {
            Ok(value) => value,
            Err(error) => {
                let no_dispatch = matches!(call.step, ApplicationApiStep::Hello(_))
                    || matches!(error, application_api_tools::TransportError::BeforeSend(_));
                let reason = if no_dispatch {
                    self.finish_application_api_no_dispatch(call.operation_id)?;
                    format!("application API request was not dispatched: {error:?}")
                } else {
                    if let Some(attempt) = self.journal.application_api_attempt.as_mut() {
                        attempt.phase = ApplicationApiPhase::Uncertain;
                    }
                    self.save()?;
                    format!("application API forward result is unresolved: {error:?}")
                };
                let _ = call.reply.send(json!({"isError":true,"text":reason}));
                *active = None;
                return Ok(());
            }
        };
        let reply = match application_api_tools::parse_host_reply(result.clone()) {
            Ok(reply) => reply,
            Err(error) if matches!(call.step, ApplicationApiStep::Hello(_)) => {
                self.finish_application_api_no_dispatch(call.operation_id)?;
                let _ = call.reply.send(json!({"isError":true,"text":error}));
                *active = None;
                return Ok(());
            }
            Err(error) => return Err(error),
        };
        if matches!(call.step, ApplicationApiStep::Hello(_)) {
            let ApplicationApiRoute::V2(route) = &call.route else {
                return Err("lifetime route entered v2 binding path".into());
            };
            let (digest, invocation) = match application_api_tools::verify_binding(reply, route) {
                Ok(binding) => binding,
                Err(error) => {
                    self.finish_application_api_no_dispatch(call.operation_id)?;
                    let _ = call.reply.send(json!({"isError":true,"text":error}));
                    *active = None;
                    return Ok(());
                }
            };
            let attempt = self
                .journal
                .application_api_attempt
                .as_mut()
                .ok_or("application API attempt disappeared while hello was pending")?;
            attempt.binding_sha256 = Some(digest);
            attempt.host_invocation = Some(invocation);
            attempt.phase = ApplicationApiPhase::BindingVerified;
            self.save()?;
            // Persist the last pre-dispatch state before the one-shot worker
            // can send any byte. A crash here is inspect-only, never resend.
            self.journal.application_api_attempt.as_mut().unwrap().phase =
                ApplicationApiPhase::DispatchStarted;
            self.save()?;
            let worker = match application_api_tools::start_dispatch_once(
                call.route.socket_path(),
                call.route.host_uid(),
                call.request.clone(),
                call.deadline,
                self.application_api_send_gate.clone(),
                self.cancelled.clone(),
            ) {
                Ok(worker) => worker,
                Err(error) => {
                    self.finish_application_api_no_dispatch(call.operation_id)?;
                    let _ = call.reply.send(json!({"isError":true,
                        "text":format!("application API forward spawn: {error:?}")}));
                    *active = None;
                    return Ok(());
                }
            };
            call.step = ApplicationApiStep::Dispatch(worker);
            return Ok(());
        }
        let attempt = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("application API attempt disappeared before a forward reply")?;
        let digest = attempt
            .binding_sha256
            .as_deref()
            .ok_or("application API attempt lacks a checked host binding")?;
        application_api_tools::verify_operation_reply(&reply, call.operation_id, digest)?;
        let path = self.config.state_dir.join(format!(
            "application-api-reply-{:016}.json",
            call.operation_id
        ));
        let bytes = serde_json::to_vec(&result).map_err(|error| error.to_string())?;
        write_new(&path, &bytes)?;
        let definite = matches!(
            reply,
            application_api_tools::HostReply::Http { .. }
                | application_api_tools::HostReply::Refused { .. }
        );
        let attempt = self.journal.application_api_attempt.as_mut().unwrap();
        attempt.reply_path = Some(path);
        attempt.reply_sha256 = Some(sha256_bytes(&bytes)?);
        attempt.phase = if definite {
            ApplicationApiPhase::Definite
        } else {
            ApplicationApiPhase::Uncertain
        };
        self.save()?;
        let refused = matches!(reply, application_api_tools::HostReply::Refused { .. });
        let delivered = call
            .reply
            .send(json!({"isError":!definite || refused,
            "text":result.to_string()}))
            .is_ok();
        if definite && delivered {
            let mut finished = self.journal.application_api_attempt.take().unwrap();
            finished.reported = true;
            if self.journal.application_api_history.len() >= 16 {
                self.journal.application_api_history.remove(0);
            }
            self.journal.application_api_history.push(finished);
            self.save()?;
        }
        *active = None;
        Ok(())
    }

    /// After a crash, inspect the exact operation ID under the original saved
    /// binding. The current protected socket may belong to a new invocation;
    /// the host must match its historical received.json anchor. Inspection is
    /// read-only and never constructs a dispatch request or clears a hold.
    fn inspect_application_api(&self) -> Result<Value> {
        let attempt = self
            .journal
            .application_api_attempt
            .as_ref()
            .ok_or("no unresolved application API attempt")?;
        if sha256_file(&attempt.request_path)? != attempt.request_sha256 {
            return Err("retained application API request bytes changed".into());
        }
        let Some(binding) = attempt.binding_sha256.as_deref() else {
            // No forward dispatch frame can begin before a checked binding
            // is durably saved. This is a local read-only custody report.
            return Ok(json!({"operationId":attempt.operation_id.to_string(),
                "phase":attempt.phase,"host":null,"recoveredHttp":null}));
        };
        if let Some(route) = self.config.tool_task.as_ref().and_then(|tool| {
            tool.allowed_application_lifetime_routes
                .iter()
                .find(|route| route.name == attempt.route_name)
        }) {
            let mut request = json!({"type":"inspect-v3","protocol":"mini-spk-agent-api-v3",
                "operationId":attempt.operation_id.to_string(),"bindingSha256":binding});
            if let Some(fingerprint) = attempt.operation_fingerprint.as_deref() {
                request["operationFingerprint"] = json!(fingerprint);
            }
            let deadline = Instant::now() + Duration::from_secs(30);
            let response = application_api_tools::exchange_once(
                &route.socket_path,
                route.host_uid,
                &request,
                deadline,
            )
            .map_err(|error| format!("lifetime application read-only inspect: {error:?}"))?;
            let recovered = recovered_lifetime_http(
                attempt,
                &response,
                self.journal.dispatch_attempt.is_some()
                    || self.journal.dispatch_hold.is_some()
                    || self.journal.dispatch_pending.is_some(),
            )?;
            return Ok(json!({"operationId":attempt.operation_id.to_string(),
                "phase":attempt.phase,"host":response,"recoveredHttp":recovered}));
        }
        let route = self
            .config
            .tool_task
            .as_ref()
            .and_then(|tool| {
                tool.allowed_application_api_routes
                    .iter()
                    .find(|route| route.name == attempt.route_name)
            })
            .ok_or("retained application API route is absent")?;
        let deadline = Instant::now() + Duration::from_secs(30);
        let response = application_api_tools::exchange_once(
            &route.socket_path,
            route.host_uid,
            &application_api_tools::inspect_historical_request(attempt.operation_id, binding)?,
            deadline,
        )
        .map_err(|error| format!("application API read-only inspect: {error:?}"))?;
        let reply = application_api_tools::parse_host_reply(response)?;
        application_api_tools::verify_operation_reply(&reply, attempt.operation_id, binding)?;
        if !matches!(reply, application_api_tools::HostReply::Inspection { .. }) {
            return Err("application API inspect returned a non-inspection reply".into());
        }
        let recovered =
            application_api_tools::recovered_definite_http(&reply, attempt.operation_id, binding)?;
        Ok(json!({"operationId":attempt.operation_id.to_string(),
            "phase":attempt.phase,"host":reply,"recoveredHttp":recovered}))
    }
    fn provider_lease_current(&self, lease: &provider::LeaseId) -> Result<()> {
        if self.provider_lease.as_ref() != Some(lease)
            || !self.prompt_active
            || self.cancelled.load(Ordering::SeqCst)
            || self.journal.connection == Connection::Fenced
            || self.journal.child.as_ref().map(|child| child.operation_id)
                != Some(lease.prompt_operation_id)
        {
            return Err("provider prompt lease is no longer active".into());
        }
        Ok(())
    }
    fn handle_provider(&mut self, command: provider::ProviderCommand) {
        match command {
            provider::ProviderCommand::Reserve { request, reply } => {
                let result = self.provider_reserve(request);
                let _ = reply.send(result);
            }
            provider::ProviderCommand::BeforeSend {
                attempt_id,
                lease,
                reply,
            } => {
                let result = self.provider_before_send(attempt_id, &lease);
                let _ = reply.send(result);
            }
            provider::ProviderCommand::Outcome {
                attempt_id,
                outcome,
                reply,
            } => {
                let recorded =
                    self.provider_record_outcome(attempt_id, outcome)
                        .and_then(|charge| {
                            if charge == Some("configured")
                                && self
                                    .config
                                    .provider_task
                                    .as_ref()
                                    .is_some_and(|task| task.metering)
                            {
                                self.provider_meter_quote(attempt_id)?;
                            }
                            Ok(charge)
                        });
                if recorded.is_err()
                    && self
                        .config
                        .provider_task
                        .as_ref()
                        .is_some_and(|task| task.metering)
                    && self
                        .journal
                        .provider_attempt
                        .as_ref()
                        .is_some_and(|attempt| {
                            attempt.id == attempt_id
                                && attempt.outcome.as_deref().is_some_and(|kind| {
                                    kind.starts_with("received:") || kind.starts_with("uncertain:")
                                })
                        })
                {
                    let note = format!("metered provider request {attempt_id} retained a response without a valid Lean quote; held allowance needs reconciliation");
                    if !self.journal.unresolved_external.contains(&note) {
                        self.journal.unresolved_external.push(note);
                        let _ = self.save();
                    }
                }
                let not_sent = recorded.as_ref().ok().copied().flatten() == Some("0");
                let acknowledged = reply.send(recorded.map(|_| ())).is_ok();
                // A Received response is not a delivered response. Keep its
                // exact hold until a separate local-write outcome arrives;
                // an SDK retry cannot be allowed to reserve again here.
                if not_sent && acknowledged {
                    if let Err(error) = self.provider_settle("0") {
                        eprintln!("provider settlement unresolved: {error}");
                    }
                }
            }
            provider::ProviderCommand::Delivery {
                attempt_id,
                local_write_success,
                reply,
            } => {
                let result = self.provider_delivery(attempt_id, local_write_success);
                let settle = result.as_ref().ok().and_then(|charge| charge.clone());
                let _ = reply.send(result.map(|_| ()));
                if let Some(charge) = settle {
                    if let Err(error) = self.provider_settle(&charge) {
                        eprintln!("provider settlement unresolved: {error}");
                    }
                }
            }
        }
    }
    fn drain_provider_after_prompt(&mut self, active: &ActiveProvider) -> Result<()> {
        active.endpoint.control().revoke();
        self.provider_lease = None;
        let started = Instant::now();
        loop {
            let mut handled = false;
            for _ in 0..4 {
                match active.requests.try_recv() {
                    Ok(command) => {
                        handled = true;
                        self.handle_provider(command);
                    }
                    Err(_) => break,
                }
            }
            if active.endpoint.control().is_idle() && !handled {
                return Ok(());
            }
            if started.elapsed() >= Duration::from_secs(45) {
                let note = "provider gateway did not drain after prompt; exact attempt may have external effects";
                if !self
                    .journal
                    .unresolved_external
                    .iter()
                    .any(|entry| entry == note)
                {
                    self.journal.unresolved_external.push(note.into());
                    self.save()?;
                }
                return Err(note.into());
            }
            thread::sleep(Duration::from_millis(20));
        }
    }
    fn provider_reserve(
        &mut self,
        request: provider::ProviderRequest,
    ) -> Result<provider::ForwardPermit> {
        self.provider_lease_current(&request.lease)?;
        let task = self
            .config
            .provider_task
            .clone()
            .ok_or("providerTask absent")?;
        if request.model != task.model
            || request.exact_body.is_empty()
            || request.exact_body.len() > task.max_request_bytes
        {
            return Err("provider request differs from pinned model or size".into());
        }
        let metering_pin = self.provider_metering_pin(&task)?;
        if let Some(pin) = &metering_pin {
            let maximum = provider_max_charge_bound(
                pin,
                task.max_input_tokens
                    .ok_or("metered input ceiling absent")?,
                task.max_output_tokens
                    .ok_or("metered output ceiling absent")?,
            )?;
            let reserve = task
                .reserve
                .parse::<u128>()
                .map_err(|_| "provider reserve exceeds u128")?;
            if maximum > reserve {
                return Err(
                    "operator-pinned provider maximum charge exceeds signed reserve".into(),
                );
            }
        }
        if self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
        {
            return Err("prior provider request needs exact reconciliation".into());
        }
        if let Some(replay) = Self::provider_replay(&self.journal.provider_replays, &request)? {
            return Ok(replay);
        }
        if self.journal.provider_replays.len() >= 16 {
            return Err("provider prompt response replay bound reached".into());
        }
        // Refresh only the root and unchanged state coordinates of this same
        // reserved generation. The native joint reserve remains the atomic
        // authority check; Rust cannot infer admission from this observation.
        let parent = self.query()?;
        self.provider_lease_current(&request.lease)?;
        let grain = parent.get("grain").ok_or("parent grain absent")?;
        if grain.get("generation").and_then(Value::as_str)
            != Some(request.lease.parent_generation.as_str())
            || !matches!(grain.get("status").and_then(Value::as_str), Some("3" | "4"))
        {
            return Err("parent prompt generation is no longer reserved".into());
        }
        let mut witness = self
            .journal
            .prompt_witness
            .clone()
            .ok_or("parent prompt witness absent")?;
        witness["expectedTargetRoot"] = parent
            .get("targetRoot")
            .ok_or("parent root absent")?
            .clone();
        witness["before"] = json!({
            "generation":grain.get("generation"), "status":grain.get("status"),
            "remaining":grain.get("remaining"), "reserved":grain.get("reserved")
        });
        self.journal.prompt_witness = Some(witness);
        self.save()?;
        let id = self.next_id()?;
        let request_path = self
            .config
            .state_dir
            .join(format!("provider-{id:016}.controller-request"));
        write_new(&request_path, &request.exact_body)?;
        let request_sha256 = sha256_file(&request_path)?;
        self.journal.provider_settlement = None;
        self.journal.provider_attempt = Some(ProviderAttempt {
            id,
            prompt_operation_id: request.lease.prompt_operation_id,
            parent_generation: request.lease.parent_generation.clone(),
            model: request.model,
            request_path,
            request_bytes: request.exact_body.len(),
            request_sha256,
            send_started: false,
            outcome_path: None,
            outcome_bytes: None,
            outcome_sha256: None,
            outcome: None,
            response_status: None,
            response_content_type: None,
            response_headers_path: None,
            response_headers_bytes: None,
            response_headers_sha256: None,
            metering_pin,
            meter_report_path: None,
            meter_report_sha256: None,
            metered_charge: None,
        });
        self.save()?;
        let authority = self.provider()?;
        let status = self
            .query_as(&authority)?
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("provider grain status absent")?
            .to_owned();
        if status == "0" {
            self.provider_lease_current(&request.lease)?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "provider attach",
                "gateway provider attach",
                vec![],
            )?;
        } else if status != "1" {
            return Err(format!(
                "provider task status {status} needs reconciliation"
            ));
        }
        self.provider_lease_current(&request.lease)?;
        self.mark_hold_as(
            AuthoritySlot::Provider,
            &authority,
            &task.reserve,
            &task.charge,
        )?;
        self.provider_lease_current(&request.lease)?;
        self.transition_as_with_witness(
            &authority,
            json!({"type":"reserve","amount":task.reserve}),
            "provider reserve",
            "gateway exact request reserve",
            vec![],
            Some((task.parent_capability, task.parent_observe_capability)),
        )?;
        self.provider_lease_current(&request.lease)?;
        Ok(provider::ForwardPermit::Fresh {
            attempt_id: id,
            lease: request.lease,
            exact_body: request.exact_body,
        })
    }
    fn provider_metering_pin(&self, task: &ProviderTask) -> Result<Option<ProviderMeteringPin>> {
        if !task.metering {
            return Ok(None);
        }
        let output = Command::new(&self.config.mini)
            .arg("profile")
            .arg("--host")
            .arg(&self.config.host)
            .arg("--config")
            .arg(&self.config.host_config)
            .output()
            .map_err(|e| format!("provider metering profile: {e}"))?;
        if !output.status.success() || output.stdout.len() > 16_384 {
            return Err("pinned Host provider metering profile unavailable".into());
        }
        let profile: Value = serde_json::from_slice(&output.stdout)
            .map_err(|e| format!("invalid provider metering profile: {e}"))?;
        let metering = select_provider_metering(&profile, &task.task)?;
        let field = |name: &str| -> Result<String> {
            let value = metering
                .get(name)
                .and_then(Value::as_str)
                .ok_or_else(|| format!("provider metering profile lacks {name}"))?;
            if value.len() > 80 {
                return Err(format!("provider metering {name} exceeds decimal bound"));
            }
            decimal(value, name)?;
            Ok(value.to_owned())
        };
        let pin = ProviderMeteringPin {
            provider_resource_id: field("providerResourceId")?,
            metadata_version: if profile.get("providerMeterings").is_some() {
                2
            } else {
                1
            },
            model: metering
                .get("model")
                .and_then(Value::as_str)
                .ok_or("provider metering model absent")?
                .to_owned(),
            tariff_version: field("tariffVersion")?,
            tariff_digest: field("tariffDigest")?,
            input_micro_per_million: field("inputMicroPerMillion")?,
            output_micro_per_million: field("outputMicroPerMillion")?,
            max_input_tokens: task.max_input_tokens,
            max_output_tokens: task.max_output_tokens,
        };
        if pin.provider_resource_id != task.task
            || pin.model != task.model
            || pin.tariff_version == "0"
        {
            return Err(
                "provider task differs from the operator-pinned Host metering tariff".into(),
            );
        }
        Ok(Some(pin))
    }
    fn provider_replay(
        replays: &[ProviderReplay],
        request: &provider::ProviderRequest,
    ) -> Result<Option<provider::ForwardPermit>> {
        for prior in replays {
            if prior.prompt_operation_id != request.lease.prompt_operation_id
                || prior.parent_generation != request.lease.parent_generation
                || prior.request_bytes != request.exact_body.len()
            {
                continue;
            }
            let exact_request = retained_exact(
                &prior.request_path,
                prior.request_bytes,
                &prior.request_sha256,
                1_048_576,
            )?;
            if exact_request != request.exact_body {
                continue;
            }
            let exact_response = retained_exact(
                &prior.response_path,
                prior.response_bytes,
                &prior.response_sha256,
                8_388_608,
            )?;
            if let (Some(path), Some(bytes), Some(digest)) = (
                &prior.response_headers_path,
                prior.response_headers_bytes,
                &prior.response_headers_sha256,
            ) {
                let headers = retained_exact(path, bytes, digest, 131_072)?;
                if provider::response_headers(&headers)
                    .map_err(|e| format!("retained provider replay headers invalid: {e}"))?
                    != (prior.status, prior.content_type.clone())
                {
                    return Err("provider replay headers differ from durable response".into());
                }
            } else if prior.response_headers_path.is_some()
                || prior.response_headers_bytes.is_some()
                || prior.response_headers_sha256.is_some()
            {
                return Err("provider replay headers have incomplete custody".into());
            }
            if let (Some(path), Some(digest), Some(charge)) = (
                &prior.meter_report_path,
                &prior.meter_report_sha256,
                &prior.metered_charge,
            ) {
                let length = fs::symlink_metadata(path)
                    .map_err(|e| format!("retained provider quote: {e}"))?
                    .len() as usize;
                let bytes = retained_exact(path, length, digest, 16_384)?;
                let report: Value = serde_json::from_slice(&bytes)
                    .map_err(|e| format!("retained provider quote: {e}"))?;
                if report.get("charge").and_then(Value::as_str) != Some(charge.as_str())
                    || report.pointer("/operation/type").and_then(Value::as_str) != Some("settle")
                    || report.pointer("/operation/charge").and_then(Value::as_str)
                        != Some(charge.as_str())
                {
                    return Err("provider replay quote differs from retained charge".into());
                }
            } else if prior.meter_report_path.is_some()
                || prior.meter_report_sha256.is_some()
                || prior.metered_charge.is_some()
            {
                return Err("provider replay quote has incomplete custody".into());
            }
            return Ok(Some(provider::ForwardPermit::Replay {
                lease: request.lease.clone(),
                exact_body: request.exact_body.clone(),
                status: prior.status,
                content_type: prior.content_type.clone(),
                exact_response,
            }));
        }
        Ok(None)
    }
    fn provider_before_send(&mut self, attempt_id: u64, lease: &provider::LeaseId) -> Result<()> {
        self.provider_lease_current(lease)?;
        if self.journal.provider_pending.is_some()
            || !self
                .journal
                .provider_hold
                .as_ref()
                .is_some_and(|hold| hold.reserve_confirmed)
        {
            return Err("provider reserve is not confirmed".into());
        }
        let parent = self.query()?;
        let provider_state = self.query_as(&self.provider()?)?;
        self.provider_lease_current(lease)?;
        let hold = self
            .journal
            .provider_hold
            .as_ref()
            .ok_or("provider held reserve disappeared")?;
        if parent.pointer("/grain/generation").and_then(Value::as_str)
            != Some(lease.parent_generation.as_str())
            || !matches!(
                parent.pointer("/grain/status").and_then(Value::as_str),
                Some("3" | "4")
            )
            || !provider_reserve_coordinates(&provider_state, hold)
        {
            return Err(
                "signed parent or provider reserved coordinates changed before upstream send"
                    .into(),
            );
        }
        self.verify_provider_reserve_continuity(hold.clone())?;
        self.provider_lease_current(lease)?;
        let parent_after = self.query()?;
        self.provider_lease_current(lease)?;
        if parent_after
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            != Some(lease.parent_generation.as_str())
            || !matches!(
                parent_after
                    .pointer("/grain/status")
                    .and_then(Value::as_str),
                Some("3" | "4")
            )
        {
            return Err("parent prompt generation changed during reserve continuity check".into());
        }
        let attempt = self
            .journal
            .provider_attempt
            .as_mut()
            .ok_or("provider attempt absent")?;
        if attempt.id != attempt_id
            || attempt.prompt_operation_id != lease.prompt_operation_id
            || attempt.parent_generation != lease.parent_generation
            || attempt.send_started
            || attempt.outcome.is_some()
        {
            return Err("provider send boundary differs from durable attempt".into());
        }
        attempt.send_started = true;
        self.save()
    }
    fn verify_provider_reserve_continuity(&mut self, hold: HeldCharge) -> Result<()> {
        let socket = self
            .config
            .host_socket
            .as_ref()
            .ok_or("provider continuity requires the pinned persistent Mini host socket")?
            .clone();
        let reserve_attempt = hold
            .reserve_attempt
            .as_ref()
            .ok_or("provider reserve attempt absent")?;
        let call = reserve_attempt.join("call.bin");
        let outcome = hold
            .reserve_outcome_path
            .as_ref()
            .ok_or("provider confirmed outcome path absent")?;
        if outcome.parent() != Some(reserve_attempt.as_path()) {
            return Err("provider confirmed outcome is outside reserve attempt".into());
        }
        let anchor = hold
            .reserve_anchor
            .ok_or("provider confirmed anchor absent")?;
        for file in [&call, outcome] {
            if !fs::symlink_metadata(file)
                .map_err(|e| format!("{}: {e}", file.display()))?
                .file_type()
                .is_file()
            {
                return Err("retained provider reserve evidence is not a regular file".into());
            }
        }
        if hold.reserve_boundary.as_deref() != Some(anchor.image_boundary.as_str())
            || Some(sha256_file(&call)?.as_str()) != hold.reserve_call_sha256.as_deref()
            || Some(sha256_file(outcome)?.as_str()) != hold.reserve_outcome_sha256.as_deref()
        {
            return Err("retained provider reserve evidence differs from durable anchor".into());
        }
        let id = self.next_id()?;
        let attempt = self
            .config
            .state_dir
            .join(format!("provider-continuity-{id:016}"));
        let cfg = &self.config;
        self.command_output(
            &cfg.mini,
            &[
                "continuity",
                "--host",
                cfg.host.to_str().ok_or("host path UTF-8")?,
                "--config",
                cfg.host_config.to_str().ok_or("config path UTF-8")?,
                "--socket",
                socket.to_str().ok_or("host socket path UTF-8")?,
                "--call",
                call.to_str().ok_or("reserve call path UTF-8")?,
                "--outcome",
                outcome.to_str().ok_or("reserve outcome path UTF-8")?,
                "--dir",
                attempt.to_str().ok_or("continuity attempt path UTF-8")?,
            ],
        )
        .map_err(|error| format!("provider continuity attempt {}: {error}", attempt.display()))?;
        let result: Value = serde_json::from_slice(
            &fs::read(attempt.join("continuity.json")).map_err(|e| e.to_string())?,
        )
        .map_err(|e| e.to_string())?;
        if result.get("type").and_then(Value::as_str) != Some("minidregg-provider-continuity-v1")
            || result.get("status").and_then(Value::as_str) != Some("confirmed")
            || result.get("continuous").and_then(Value::as_bool) != Some(true)
            || result.get("providerResourceId").and_then(Value::as_str)
                != self
                    .config
                    .provider_task
                    .as_ref()
                    .map(|task| task.task.as_str())
        {
            return Err(format!(
                "native provider reserve continuity refused or names another cell; retained {}",
                attempt.display()
            ));
        }
        let observed = result.get("anchor").ok_or("continuity anchor absent")?;
        if observed.get("type").and_then(Value::as_str) != Some("verified-mini-native-prefix-v1")
            || observed.get("transactionId").and_then(Value::as_str)
                != Some(anchor.transaction_id.as_str())
            || observed.get("eventId").and_then(Value::as_str) != Some(anchor.event_id.as_str())
            || observed.get("acceptedCount").and_then(Value::as_str)
                != Some(anchor.accepted_count.as_str())
            || observed.get("imageBoundary").and_then(Value::as_str)
                != Some(anchor.image_boundary.as_str())
        {
            return Err("native continuity anchor differs from retained reserve receipt".into());
        }
        decimal(
            result
                .get("checkedImageBoundary")
                .and_then(Value::as_str)
                .ok_or("continuity checked boundary absent")?,
            "continuity checked boundary",
        )?;
        decimal(
            result
                .get("checkedAcceptedCount")
                .and_then(Value::as_str)
                .ok_or("continuity checked count absent")?,
            "continuity checked count",
        )?;
        Ok(())
    }
    fn provider_record_outcome(
        &mut self,
        attempt_id: u64,
        outcome: provider::ProviderOutcome,
    ) -> Result<Option<&'static str>> {
        let attempt = self
            .journal
            .provider_attempt
            .as_ref()
            .ok_or("provider attempt absent")?;
        if attempt.id != attempt_id || attempt.outcome.is_some() {
            return Err("provider outcome differs from durable attempt".into());
        }
        let (kind, bytes, headers, charge, response_status, response_content_type, headers_valid) =
            match outcome {
                provider::ProviderOutcome::Received {
                    status,
                    content_type,
                    exact_headers,
                    exact_body,
                } => {
                    if !attempt.send_started {
                        return Err("provider response without durable send boundary".into());
                    }
                    let headers_valid = provider::response_headers(&exact_headers)
                        .is_ok_and(|parsed| parsed == (status, content_type.clone()));
                    (
                        format!("received:{status}:{content_type}"),
                        exact_body,
                        Some(exact_headers),
                        Some("configured"),
                        Some(status),
                        Some(content_type),
                        headers_valid,
                    )
                }
                provider::ProviderOutcome::NotSent { reason } => (
                    format!("not-sent:{reason}"),
                    Vec::new(),
                    None,
                    Some("0"),
                    None,
                    None,
                    true,
                ),
                provider::ProviderOutcome::Uncertain {
                    partial_body,
                    reason,
                } => (
                    format!("uncertain:{reason}"),
                    partial_body,
                    None,
                    None,
                    None,
                    None,
                    true,
                ),
            };
        let path = self
            .config
            .state_dir
            .join(format!("provider-{attempt_id:016}.controller-outcome"));
        write_new(&path, &bytes)?;
        let digest = sha256_file(&path)?;
        let retained_headers = if let Some(headers) = headers {
            let path = self.config.state_dir.join(format!(
                "provider-{attempt_id:016}.controller-response-headers"
            ));
            write_new(&path, &headers)?;
            let digest = sha256_file(&path)?;
            Some((path, headers.len(), digest))
        } else {
            None
        };
        let attempt = self
            .journal
            .provider_attempt
            .as_mut()
            .ok_or("provider attempt disappeared before outcome journal")?;
        attempt.outcome_path = Some(path);
        attempt.outcome_bytes = Some(bytes.len());
        attempt.outcome_sha256 = Some(digest);
        attempt.outcome = Some(kind.clone());
        attempt.response_status = response_status;
        attempt.response_content_type = response_content_type;
        if let Some((path, len, digest)) = retained_headers {
            attempt.response_headers_path = Some(path);
            attempt.response_headers_bytes = Some(len);
            attempt.response_headers_sha256 = Some(digest);
        }
        if charge.is_none() {
            self.journal.unresolved_external.push(format!(
                "provider request {attempt_id} may have reached upstream; exact response uncertain"
            ));
        }
        if !headers_valid {
            attempt.outcome = Some("uncertain:raw-header-metadata-mismatch".into());
            self.journal.unresolved_external.push(format!(
                "provider request {attempt_id} returned raw headers inconsistent with reported metadata"
            ));
            self.save()?;
            return Err("provider response metadata differs from retained raw headers".into());
        }
        self.save()?;
        Ok(charge)
    }
    fn provider_meter_quote(&mut self, attempt_id: u64) -> Result<()> {
        self.provider_meter_quote_inner(attempt_id, true)
    }
    fn provider_meter_quote_inner(
        &mut self,
        attempt_id: u64,
        require_live_lease: bool,
    ) -> Result<()> {
        let task = self
            .config
            .provider_task
            .clone()
            .ok_or("providerTask absent")?;
        if !task.metering {
            return Err("provider metering is not enabled".into());
        }
        let attempt = self
            .journal
            .provider_attempt
            .clone()
            .ok_or("provider attempt absent")?;
        let lease = provider::LeaseId {
            prompt_operation_id: attempt.prompt_operation_id,
            parent_generation: attempt.parent_generation.clone(),
        };
        if require_live_lease {
            self.provider_lease_current(&lease)?;
        }
        let pin = attempt
            .metering_pin
            .as_ref()
            .ok_or("provider tariff pin absent")?;
        let hold = self
            .journal
            .provider_hold
            .clone()
            .ok_or("provider signed hold absent")?;
        if attempt.id != attempt_id
            || !attempt.send_started
            || !attempt
                .outcome
                .as_deref()
                .is_some_and(|value| value.starts_with("received:"))
            || attempt.meter_report_path.is_some()
            || !hold.reserve_confirmed
            || hold.reserve != task.reserve
            || pin.provider_resource_id != task.task
            || pin.model != task.model
        {
            return Err("provider metering lacks the exact held request and response".into());
        }
        let provider_authority = self.provider()?;
        let signed_provider = self.query_as(&provider_authority)?;
        if !(if require_live_lease {
            provider_reserve_coordinates(&signed_provider, &hold)
        } else {
            provider_audit_coordinates(&signed_provider, &hold)
        }) {
            return Err("signed provider state differs from the held metering reserve".into());
        }
        let request = retained_exact(
            &attempt.request_path,
            attempt.request_bytes,
            &attempt.request_sha256,
            task.max_request_bytes,
        )?;
        let response_path = attempt
            .outcome_path
            .as_ref()
            .ok_or("provider response absent")?;
        let response = retained_exact(
            response_path,
            attempt
                .outcome_bytes
                .ok_or("provider response byte count absent")?,
            attempt
                .outcome_sha256
                .as_deref()
                .ok_or("provider response digest absent")?,
            task.max_response_bytes,
        )?;
        let headers = retained_exact(
            attempt
                .response_headers_path
                .as_deref()
                .ok_or("metered provider headers absent")?,
            attempt
                .response_headers_bytes
                .ok_or("metered provider header length absent")?,
            attempt
                .response_headers_sha256
                .as_deref()
                .ok_or("metered provider header digest absent")?,
            131_072,
        )?;
        let (status, content_type) = provider::response_headers(&headers)
            .map_err(|e| format!("metered response headers invalid: {e}"))?;
        if Some(status) != attempt.response_status
            || Some(content_type.as_str()) != attempt.response_content_type.as_deref()
        {
            return Err("metering metadata differs from the retained raw headers".into());
        }
        let socket = self
            .config
            .host_socket
            .clone()
            .ok_or("metering requires pinned Host socket")?;
        let id = self.next_id()?;
        let metadata_path = self
            .config
            .state_dir
            .join(format!("provider-meter-{id:016}.metadata.json"));
        let metadata = provider_metering_metadata(pin, status, &content_type, &hold.reserve)?;
        write_new(&metadata_path, metadata.to_string().as_bytes())?;
        let directory = self
            .config
            .state_dir
            .join(format!("provider-meter-{id:016}"));
        let cfg = &self.config;
        self.command_output(
            &cfg.mini,
            &[
                "meter",
                "--host",
                cfg.host.to_str().ok_or("host path UTF-8")?,
                "--config",
                cfg.host_config.to_str().ok_or("config path UTF-8")?,
                "--socket",
                socket.to_str().ok_or("Host socket path UTF-8")?,
                "--metadata",
                metadata_path.to_str().ok_or("meter metadata path UTF-8")?,
                "--request",
                attempt.request_path.to_str().ok_or("request path UTF-8")?,
                "--response",
                response_path.to_str().ok_or("response path UTF-8")?,
                "--dir",
                directory.to_str().ok_or("meter attempt path UTF-8")?,
            ],
        )
        .map_err(|e| {
            format!(
                "provider Lean quote retained at {}: {e}",
                directory.display()
            )
        })?;
        let report_path = directory.join("meter.json");
        let report_bytes = bounded_regular_file(&report_path, 16_384)?;
        let report: Value = serde_json::from_slice(&report_bytes)
            .map_err(|e| format!("provider Lean quote JSON: {e}"))?;
        let charge =
            provider_quote_charge(&report, pin, &hold.reserve, request.len(), response.len())?;
        if require_live_lease {
            self.provider_lease_current(&lease)?;
        }
        let digest = sha256_bytes(&report_bytes)?;
        let mut current = self
            .journal
            .provider_attempt
            .clone()
            .ok_or("provider attempt disappeared")?;
        if current.id != attempt_id || current.meter_report_path.is_some() {
            return Err("provider attempt changed during read-only quote".into());
        }
        current.meter_report_path = Some(report_path);
        current.meter_report_sha256 = Some(digest);
        current.metered_charge = Some(charge);
        self.validated_metered_charge(&current)?;
        self.journal.provider_attempt = Some(current);
        self.save()
    }
    fn validated_metered_charge(&self, attempt: &ProviderAttempt) -> Result<String> {
        let hold = self
            .journal
            .provider_hold
            .as_ref()
            .ok_or("metered provider hold absent")?;
        if !hold.reserve_confirmed {
            return Err("metered provider reserve lacks confirmed receipt".into());
        }
        self.validated_metered_charge_for_reserve(attempt, &hold.reserve)
    }
    fn validated_metered_charge_for_reserve(
        &self,
        attempt: &ProviderAttempt,
        reserve: &str,
    ) -> Result<String> {
        let task = self
            .config
            .provider_task
            .as_ref()
            .ok_or("providerTask absent")?;
        let pin = attempt
            .metering_pin
            .as_ref()
            .ok_or("metered tariff pin absent")?;
        if !task.metering
            || reserve != task.reserve
            || pin.provider_resource_id != task.task
            || pin.model != task.model
        {
            return Err("metered quote differs from configured task or signed hold".into());
        }
        let request = retained_exact(
            &attempt.request_path,
            attempt.request_bytes,
            &attempt.request_sha256,
            task.max_request_bytes,
        )?;
        let response = retained_exact(
            attempt
                .outcome_path
                .as_deref()
                .ok_or("metered response absent")?,
            attempt
                .outcome_bytes
                .ok_or("metered response length absent")?,
            attempt
                .outcome_sha256
                .as_deref()
                .ok_or("metered response digest absent")?,
            task.max_response_bytes,
        )?;
        let headers = retained_exact(
            attempt
                .response_headers_path
                .as_deref()
                .ok_or("metered raw headers absent")?,
            attempt
                .response_headers_bytes
                .ok_or("metered raw headers length absent")?,
            attempt
                .response_headers_sha256
                .as_deref()
                .ok_or("metered raw headers digest absent")?,
            131_072,
        )?;
        let (status, content_type) = provider::response_headers(&headers)
            .map_err(|e| format!("metered raw headers invalid: {e}"))?;
        if Some(status) != attempt.response_status
            || Some(content_type.as_str()) != attempt.response_content_type.as_deref()
        {
            return Err("metered status or Content-Type differs from raw headers".into());
        }
        let report_path = attempt
            .meter_report_path
            .as_ref()
            .ok_or("metered report absent")?;
        let report_digest = attempt
            .meter_report_sha256
            .as_deref()
            .ok_or("metered report digest absent")?;
        let directory = report_path
            .parent()
            .ok_or("metered report directory absent")?;
        let report_len = fs::symlink_metadata(report_path)
            .map_err(|e| format!("metered report: {e}"))?
            .len() as usize;
        let report_bytes = retained_exact(report_path, report_len, report_digest, 16_384)?;
        let frame = bounded_regular_file(&directory.join("reply.frame"), 16_385)?;
        if frame.len() != report_bytes.len() + 1
            || frame.first() != Some(&19)
            || frame.get(1..) != Some(report_bytes.as_slice())
            || retained_exact(
                &directory.join("request.bin"),
                request.len(),
                &attempt.request_sha256,
                task.max_request_bytes,
            )? != request
            || retained_exact(
                &directory.join("response.bin"),
                response.len(),
                attempt
                    .outcome_sha256
                    .as_deref()
                    .ok_or("metered response digest absent")?,
                task.max_response_bytes,
            )? != response
        {
            return Err(
                "metered Host frame or copied inputs differ from the retained attempt".into(),
            );
        }
        let metadata = provider_metering_metadata(pin, status, &content_type, reserve)?;
        if bounded_regular_file(&directory.join("metadata.json"), 4096)?
            != metadata.to_string().as_bytes()
            || bounded_regular_file(&directory.join("config.json"), 131_072)?
                != bounded_regular_file(&self.config.host_config, 131_072)?
        {
            return Err("metered metadata or config differs from pinned evidence".into());
        }
        let report: Value = serde_json::from_slice(&report_bytes)
            .map_err(|e| format!("metered report JSON: {e}"))?;
        let charge = provider_quote_charge(&report, pin, reserve, request.len(), response.len())?;
        if attempt.metered_charge.as_deref() != Some(charge.as_str()) {
            return Err("metered charge differs from source-authored retained report".into());
        }
        Ok(charge)
    }
    fn provider_delivery(
        &mut self,
        attempt_id: u64,
        local_write_success: bool,
    ) -> Result<Option<String>> {
        let attempt = self
            .journal
            .provider_attempt
            .clone()
            .ok_or("provider delivery has no durable request")?;
        if attempt.id != attempt_id
            || !attempt.send_started
            || !attempt
                .outcome
                .as_deref()
                .is_some_and(|kind| kind.starts_with("received:"))
        {
            return Err("provider delivery differs from received request".into());
        }
        if !local_write_success {
            let note = format!(
                "provider response {} was retained but local HTTP delivery failed; client may retry",
                attempt_id
            );
            if !self.journal.unresolved_external.contains(&note) {
                self.journal.unresolved_external.push(note);
                self.save()?;
            }
            return Ok(None);
        }
        let response_path = attempt
            .outcome_path
            .clone()
            .ok_or("provider response evidence path absent")?;
        let response_bytes = attempt
            .outcome_bytes
            .ok_or("provider response length absent")?;
        let response_sha256 = attempt
            .outcome_sha256
            .clone()
            .ok_or("provider response digest absent")?;
        let status = attempt
            .response_status
            .ok_or("provider response status absent")?;
        let content_type = attempt
            .response_content_type
            .clone()
            .ok_or("provider response content type absent")?;
        let charge = if self
            .config
            .provider_task
            .as_ref()
            .is_some_and(|task| task.metering)
        {
            self.validated_metered_charge(&attempt)?
        } else {
            "configured".to_owned()
        };
        let response_headers_path = attempt.response_headers_path.clone();
        let response_headers_bytes = attempt.response_headers_bytes;
        let response_headers_sha256 = attempt.response_headers_sha256.clone();
        if let (Some(path), Some(bytes), Some(digest)) = (
            &response_headers_path,
            response_headers_bytes,
            &response_headers_sha256,
        ) {
            let headers =
                fs::read(path).map_err(|e| format!("provider response headers absent: {e}"))?;
            if headers.len() != bytes
                || sha256_file(path)? != *digest
                || provider::response_headers(&headers)
                    .map_err(|e| format!("provider response headers invalid: {e}"))?
                    != (status, content_type.clone())
            {
                return Err("provider response headers differ from durable metadata".into());
            }
        } else if response_headers_path.is_some()
            || response_headers_bytes.is_some()
            || response_headers_sha256.is_some()
        {
            return Err("provider response headers have incomplete custody".into());
        }
        if fs::metadata(&response_path)
            .map_err(|e| format!("provider response evidence absent: {e}"))?
            .len()
            != response_bytes as u64
            || sha256_file(&response_path)? != response_sha256
            || fs::metadata(&attempt.request_path)
                .map_err(|e| format!("provider request evidence absent: {e}"))?
                .len()
                != attempt.request_bytes as u64
            || sha256_file(&attempt.request_path)? != attempt.request_sha256
        {
            return Err("provider delivery evidence differs from durable exact bytes".into());
        }
        if self.journal.provider_replays.len() >= 16 {
            return Err("provider prompt response replay bound reached".into());
        }
        self.journal.provider_replays.push(ProviderReplay {
            prompt_operation_id: attempt.prompt_operation_id,
            parent_generation: attempt.parent_generation,
            request_path: attempt.request_path,
            request_bytes: attempt.request_bytes,
            request_sha256: attempt.request_sha256,
            response_path,
            response_bytes,
            response_sha256,
            status,
            content_type,
            response_headers_path,
            response_headers_bytes,
            response_headers_sha256,
            meter_report_path: attempt.meter_report_path,
            meter_report_sha256: attempt.meter_report_sha256,
            metered_charge: attempt.metered_charge,
        });
        // Save the replay entry before settlement may clear the hold. If a
        // response reached the local socket but the SDK retries the same body,
        // it can never trigger another upstream send in this prompt.
        self.save()?;
        Ok(Some(charge))
    }
    fn provider_settle(&mut self, charge: &str) -> Result<()> {
        let authority = self.provider()?;
        let configured = self
            .config
            .provider_task
            .clone()
            .ok_or("providerTask absent")?;
        let charge = if charge == "configured" {
            if configured.metering {
                return Err("metered provider cannot use configured fixed charge".into());
            }
            configured.charge.clone()
        } else {
            charge.to_owned()
        };
        if configured.metering {
            if self.cancelled.load(Ordering::SeqCst) {
                return Err("metered provider interruption requires audited settlement".into());
            }
            let hold = self
                .journal
                .provider_hold
                .clone()
                .ok_or("metered provider hold absent")?;
            let attempt = self
                .journal
                .provider_attempt
                .as_ref()
                .ok_or("metered provider attempt absent")?;
            let quote_matches = if attempt
                .outcome
                .as_deref()
                .is_some_and(|kind| kind.starts_with("received:"))
            {
                self.validated_metered_charge(attempt)? == charge
            } else {
                attempt
                    .outcome
                    .as_deref()
                    .is_some_and(|kind| kind.starts_with("not-sent:"))
                    && charge == "0"
            };
            if !quote_matches || !hold.reserve_confirmed || hold.reserve != configured.reserve {
                return Err(
                    "metered provider settlement lacks retained quote and exact hold".into(),
                );
            }
            let signed = self.query_as(&authority)?;
            if !provider_reserve_coordinates(&signed, &hold) {
                return Err("metered provider signed hold changed before settlement".into());
            }
        }
        if self.journal.provider_pending.is_some() {
            return Err("provider transition needs exact retry".into());
        }
        self.transition_as(
            &authority,
            json!({"type":"settle","charge":charge}),
            "provider settle",
            if configured.metering {
                "gateway source-quoted provider settlement"
            } else {
                "gateway fixed-charge settlement"
            },
            vec![],
        )?;
        let after = self.query_as(&authority)?;
        match after.pointer("/grain/status").and_then(Value::as_str) {
            Some("1") => self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "provider disconnect",
                "gateway request completed",
                vec![],
            )?,
            Some("0" | "6") => {}
            other => return Err(format!("provider settle left unexpected status {other:?}")),
        }
        self.journal.provider_attempt = None;
        self.save()
    }
    fn finish_no_birth(&mut self) -> Result<()> {
        if self.journal.birth_operation.is_none() {
            return Ok(());
        }
        if self.journal.birth_pending.is_some() || self.journal.tool_pending.is_some() {
            return Err("resource birth still has an exact pending native attempt".into());
        }
        let authority = self.tool()?;
        let observed = self.query_as(&authority)?;
        let status = observed
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("no-birth tool status absent")?
            .to_owned();
        if let Some(hold) = self.journal.tool_hold.clone() {
            if hold.reserve_confirmed && !hold.reserve_refused {
                if observed.pointer("/grain/reserved").and_then(Value::as_str)
                    != Some(hold.reserve.as_str())
                    || !matches!(status.as_str(), "3" | "5")
                {
                    return Err("no-birth allowance differs from exact held reserve".into());
                }
                let before = hold
                    .before_generation
                    .parse::<u64>()
                    .map_err(|_| "no-birth held generation invalid")?;
                let expected = before
                    .checked_add(u64::from(status == "5"))
                    .ok_or("no-birth generation overflow")?;
                if observed
                    .pointer("/grain/generation")
                    .and_then(Value::as_str)
                    != Some(expected.to_string().as_str())
                {
                    return Err("no-birth reservation generation changed".into());
                }
                self.transition_as(
                    &authority,
                    json!({"type":"settle","charge":"0"}),
                    "tool release",
                    "no resource birth was dispatched or native birth was refused",
                    vec![],
                )?;
            } else {
                if !matches!(status.as_str(), "0" | "1")
                    || observed.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
                    || observed.get("targetRoot").and_then(Value::as_str)
                        != Some(hold.before_target_root.as_str())
                {
                    return Err("no-birth reserve refusal needs exact signed idle origin".into());
                }
                self.journal.tool_hold = None;
                self.save()?;
            }
        } else if !matches!(status.as_str(), "0" | "1")
            || observed.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
        {
            return Err("no-birth marker has an unexplained reserved tool".into());
        }
        let after = self.query_as(&authority)?;
        if after.pointer("/grain/status").and_then(Value::as_str) == Some("1") {
            self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "tool disconnect",
                "no-birth zero-charge cleanup",
                vec![],
            )?;
        }
        let terminal = self.query_as(&authority)?;
        if terminal.pointer("/grain/status").and_then(Value::as_str) != Some("0")
            || terminal.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            || self.journal.tool_hold.is_some()
        {
            return Err("no-birth zero-charge cleanup has no signed idle terminal".into());
        }
        // The signed zero release is terminal. Only a marker that still
        // proves no Mini birth submit could have started may return the
        // consumed tail ordinal. The ordinal and marker change in one journal
        // rename below; an interrupted save leaves the old marker intact.
        persist_retired_no_birth_operation(
            &self.config.state_dir.join("journal.json"),
            &mut self.journal,
        )
    }

    fn create_resource(
        &mut self,
        arguments: &Value,
        route: Option<ApplicationBirthRoute>,
    ) -> Result<Value> {
        let tool = self
            .config
            .tool_task
            .as_ref()
            .ok_or("toolTask is not configured")?
            .clone();
        let object = arguments
            .as_object()
            .ok_or("birth tool arguments must be an object")?;
        let expected_fields = if route == Some(ApplicationBirthRoute::Session) {
            2
        } else {
            1
        };
        if object.len() != expected_fields {
            return Err("birth tool has unexpected arguments".into());
        }
        let family_name = object
            .get("family")
            .and_then(Value::as_str)
            .ok_or("birth family must be a name")?;
        let selected_application = if route == Some(ApplicationBirthRoute::Session) {
            let name = object
                .get("application")
                .and_then(Value::as_str)
                .ok_or("session birth requires a named application")?;
            if name.is_empty() || name.len() > 64 {
                return Err("session application name exceeds bound".into());
            }
            Some(name.to_owned())
        } else {
            None
        };
        let (max_births, member_count, charge) = match route {
            None => {
                let family = resource_tools::select_birth(&tool.allowed_birth_families, arguments)?;
                (
                    family.max_births,
                    1,
                    resource_tools::planned_birth_charge(family)?,
                )
            }
            Some(ApplicationBirthRoute::Application) => {
                let family = tool
                    .allowed_application_families
                    .iter()
                    .find(|family| family.name == family_name)
                    .ok_or("application family is not allowlisted")?;
                (
                    family.max_births,
                    3,
                    application_tools::planned_charge(&family.profile, 3)?,
                )
            }
            Some(ApplicationBirthRoute::Session) => {
                let family = tool
                    .allowed_session_families
                    .iter()
                    .find(|family| family.name == family_name)
                    .ok_or("session family is not allowlisted")?;
                (
                    family.max_births,
                    2,
                    application_tools::planned_charge(&family.profile, 2)?,
                )
            }
        };
        if route.is_some() {
            let expected = tool
                .current_birth_host_sha256
                .as_deref()
                .ok_or("current application birth is not enabled by operator Host pin")?;
            if self.config.host_socket.is_none() || sha256_file(&self.config.host)? != expected {
                return Err(
                    "current application birth Host image or socket differs from operator pin"
                        .into(),
                );
            }
        }
        if self.journal.birth_operation.is_some()
            || self.journal.birth_pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.tool_hold.is_some()
        {
            return Err("resource birth has an unresolved delegated attempt".into());
        }
        // Resolve a named local birth or an operator-pinned foreign reference
        // before consuming an ordinal or holding allowance. A foreign name
        // supplies discovery provenance, never a locally born owner grant.
        let (selected_app_birth, selected_shared) = if route == Some(ApplicationBirthRoute::Session)
        {
            let family = tool
                .allowed_session_families
                .iter()
                .find(|family| family.name == family_name)
                .ok_or("session family is not allowlisted")?;
            let name = selected_application
                .as_deref()
                .ok_or("session application selector absent")?;
            let local = self.journal.born_resources.iter().find(|record| {
                record.pending.route == Some(ApplicationBirthRoute::Application)
                    && record.pending.family == family.application_family
                    && record.pending.born.name == name
            });
            let shared = tool
                .registered_shared_applications
                .iter()
                .find(|reference| {
                    reference.name == name
                        && reference.application_family == family.application_family
                });
            match (local, shared) {
                (Some(_), Some(_)) => return Err("session application name is ambiguous".into()),
                (Some(record), None) => {
                    self.verify_born_record(record)?;
                    (Some(record.pending.born.clone()), None)
                }
                (None, Some(reference)) => {
                    let reference = reference.clone();
                    (None, Some(self.resolve_shared_app(&tool, &reference)?))
                }
                (None, None) => return Err("session application has no confirmed local birth or registered shared reference".into()),
            }
        } else {
            (None, None)
        };
        let ordinal = *self
            .journal
            .birth_next_ordinal
            .get(family_name)
            .unwrap_or(&0);
        if ordinal >= max_births {
            return Err(format!(
                "{} resource birth family is exhausted",
                family_name
            ));
        }
        if self.journal.born_resource_count() + member_count > 8 * 1024 {
            return Err("resource birth registry is full".into());
        }
        let (prompt_operation_id, session_id, work_origin) = self.current_work_origin()?;
        let next_ordinal = ordinal.checked_add(1).ok_or("birth ordinal exhausted")?;
        self.journal
            .birth_next_ordinal
            .insert(family_name.to_owned(), next_ordinal);
        self.journal.birth_operation = Some(BirthOperation {
            family: family_name.to_owned(),
            ordinal,
            no_native_submit: true,
        });
        // Save the no-dispatch identity before even attaching or reserving.
        // A crash before the exact composite pending save can only release
        // this allowance at zero; it cannot prove a birth occurred.
        self.save()?;
        let authority = self.tool()?;
        let status = self
            .query_as(&authority)?
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("tool grain status absent")?
            .to_owned();
        if status == "0" {
            self.check_not_cancelled()?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "tool attach",
                "Hermes delegated resource birth attach",
                vec![],
            )?;
        } else if status != "1" {
            return Err(format!("tool task status {status} needs reconciliation"));
        }
        self.check_not_cancelled()?;
        self.mark_hold(true, &tool.reserve, &charge)?;
        self.transition_as(
            &authority,
            json!({"type":"reserve","amount":tool.reserve}),
            "tool reserve",
            "Hermes delegated resource birth reserve",
            vec![],
        )?;
        self.check_not_cancelled()?;
        let tool_view = self.query_as(&authority)?;
        let parent_view = self.query()?;
        let id = self.next_id()?;
        let (source, born) = match route {
            None => {
                let family = resource_tools::select_birth(&tool.allowed_birth_families, arguments)?;
                let (source, born) = resource_tools::plan_content_birth(
                    family,
                    &tool,
                    &self.config.task,
                    id,
                    ordinal,
                    &tool_view,
                    &parent_view,
                )?;
                (source, vec![born])
            }
            Some(ApplicationBirthRoute::Application) => {
                let family = tool
                    .allowed_application_families
                    .iter()
                    .find(|family| family.name == family_name)
                    .ok_or("application family changed during birth")?;
                application_tools::plan_application_birth(
                    family,
                    &tool,
                    &self.config.task,
                    id,
                    ordinal,
                    &tool_view,
                    &parent_view,
                )?
            }
            Some(ApplicationBirthRoute::Session) => {
                let family = tool
                    .allowed_session_families
                    .iter()
                    .find(|family| family.name == family_name)
                    .ok_or("session family changed during birth")?;
                let app_target = if let Some(app) = selected_app_birth.as_ref() {
                    let read = resource_tools::born_read(app);
                    let read_nonce = self.next_id()?;
                    let observation = self.supervised_resource_read(&tool, &read, read_nonce)?;
                    if observation.get("target").and_then(Value::as_str)
                        != Some(app.target.as_str())
                    {
                        return Err(
                            "fresh signed application read differs from retained birth".into()
                        );
                    }
                    app.target.as_str()
                } else {
                    selected_shared
                        .as_ref()
                        .ok_or("session shared application selection disappeared")?
                        .app_target
                        .as_str()
                };
                application_tools::plan_session_birth(
                    family,
                    &tool,
                    &self.config.task,
                    app_target,
                    application_tools::BirthIndex { nonce: id, ordinal },
                    &tool_view,
                    &parent_view,
                )?
            }
        };
        let attempt = self.config.state_dir.join(format!("attempt-{id:016}"));
        let source_path = self.config.state_dir.join(format!("source-{id:016}.json"));
        write_new(
            &source_path,
            &serde_json::to_vec_pretty(&source).map_err(|e| e.to_string())?,
        )?;
        let (intent_path, authored_intent_sha256) = if let Some(route) = route {
            let author = self
                .config
                .state_dir
                .join(format!("current-author-{id:016}"));
            let command = match route {
                ApplicationBirthRoute::Application => "current-application-intent",
                ApplicationBirthRoute::Session => "current-session-intent",
            };
            let cfg = &self.config;
            let socket = cfg
                .host_socket
                .as_ref()
                .ok_or("current birth socket absent")?;
            // Current-author is read-only, but a hard connector break must
            // still stop and reap its Mini child before settlement begins.
            // The durable birth_operation already precedes this step; no
            // birth_pending or signed call exists until authoring completes.
            self.check_not_cancelled()?;
            self.work_output(
                &cfg.mini,
                &[
                    command,
                    "--host",
                    cfg.host.to_str().ok_or("host path UTF-8")?,
                    "--config",
                    cfg.host_config.to_str().ok_or("config path UTF-8")?,
                    "--socket",
                    socket.to_str().ok_or("socket path UTF-8")?,
                    "--source",
                    source_path.to_str().ok_or("source path UTF-8")?,
                    "--dir",
                    author.to_str().ok_or("author path UTF-8")?,
                ],
            )
            .map_err(|error| format!("current birth authoring interrupted or refused: {error}"))?;
            self.check_not_cancelled()?;
            let intent = author.join("intent.bin");
            let digest = sha256_bytes(&bounded_regular_file(&intent, 4_194_304)?)?;
            (intent, Some(digest))
        } else {
            (source_path.clone(), None)
        };
        let origin = BirthPending {
            operation_id: id,
            family: family_name.to_owned(),
            ordinal,
            source_sha256: sha256_file(&source_path)?,
            born: born[0].clone(),
            route,
            born_bundle: if route.is_some() { born } else { Vec::new() },
            selected_application,
            selected_shared,
            authored_intent_sha256,
            tool_view,
            parent_view,
            prompt_operation_id,
            session_id,
            work_origin,
        };
        origin.validate_members()?;
        let birth_operation = self
            .journal
            .birth_operation
            .as_mut()
            .ok_or("resource birth lost its pre-submit marker")?;
        if birth_operation.family != family_name
            || birth_operation.ordinal != ordinal
            || !birth_operation.no_native_submit
        {
            return Err("resource birth pre-submit marker differs".into());
        }
        // This flag and both pending records become durable together before
        // the first possible `mini submit` invocation.
        birth_operation.no_native_submit = false;
        self.journal.birth_pending = Some(origin.clone());
        self.journal.tool_pending = Some(Pending {
            operation_id: id,
            operation: "tool birth".into(),
            attempt: attempt.clone(),
            uncertain: false,
            publication: None,
        });
        self.save()?;
        let cfg = &self.config;
        let mut args = vec![
            "submit",
            "--host",
            cfg.host.to_str().ok_or("host path UTF-8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config path UTF-8")?,
            "--intent",
            intent_path.to_str().ok_or("intent path UTF-8")?,
            "--intent-kind",
            if route.is_some() {
                "binary"
            } else {
                "grain-birth-intent"
            },
            "--key",
            authority.custody_key.to_str().ok_or("key path UTF-8")?,
            "--dir",
            attempt.to_str().ok_or("attempt path UTF-8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
        }
        match self.work_output(&cfg.mini, &args) {
            Ok(()) => {
                let pending = self
                    .journal
                    .tool_pending
                    .as_ref()
                    .ok_or("resource birth pending disappeared")?;
                let record = self
                    .confirmed_birth_record(pending, &origin, &attempt.join("outcome.json"))?
                    .ok_or("resource birth confirmation absent")?;
                self.journal.born_resources.push(record.clone());
                self.journal.birth_operation = None;
                self.journal.birth_pending = None;
                self.journal.tool_pending = None;
                self.journal.tool_hold = None;
                self.save()?;
                self.check_not_cancelled()?;
                self.transition_as(
                    &authority,
                    json!({"type":"disconnect"}),
                    "tool disconnect",
                    "confirmed delegated resource birth",
                    vec![],
                )?;
                Ok(birth_receipt_json(&record))
            }
            Err(custody_gate::CustodyError::BeforeSpawn) => {
                // The gate proves that this controller never started a Mini
                // custody child. Keep the durable operation marker so
                // recovery releases its held allowance at zero.
                self.journal.birth_pending = None;
                self.journal.tool_pending = None;
                self.save()?;
                Err("hard connector closed before resource birth submission; exact zero-charge recovery required".into())
            }
            Err(error) => {
                let explicit = fs::read(attempt.join("outcome.json"))
                    .ok()
                    .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).ok())
                    .is_some_and(|outcome| outcome["type"] == "refused");
                let prepared = inspected_pre_submit_refusal(&self.config, &attempt)
                    .ok()
                    .flatten();
                if explicit || prepared.is_some() {
                    // Keep birth_operation through the signed zero settlement.
                    self.journal.birth_pending = None;
                    self.journal.tool_pending = None;
                    self.save()?;
                    self.finish_no_birth()?;
                    return Err(format!("resource birth refused by Mini: {error}"));
                }
                self.journal
                    .tool_pending
                    .as_mut()
                    .ok_or("resource birth pending disappeared")?
                    .uncertain = true;
                self.save()?;
                Err(format!(
                    "resource birth outcome unknown: {error}; exact lookup is required before another birth"
                ))
            }
        }
    }

    fn workspace_root(&self) -> Result<PathBuf> {
        let tool = self.config.tool_task.as_ref().ok_or("toolTask absent")?;
        validate_resource_workspace(&self.config, tool)
    }

    fn workspace_proposal_paths(&self, id: u64) -> Result<(PathBuf, PathBuf)> {
        let dir = self
            .workspace_root()?
            .join("proposals")
            .join(id.to_string());
        Ok((dir.join("intent.json"), dir.join("proposal.json")))
    }

    fn workspace_readonly(&mut self, action: &str, arguments: &Value) -> Result<Value> {
        let root = self.workspace_root()?;
        let mut command = Command::new(&self.config.mini);
        command
            .arg("workspace")
            .arg("--action")
            .arg(action)
            .arg("--dir")
            .arg(root);
        if action == "list" {
            if arguments != &json!({}) && !arguments.is_null() {
                return Err("workspace list takes no arguments".into());
            }
        } else {
            let object = arguments
                .as_object()
                .ok_or("workspace read requires a name")?;
            if object.len() != 1 {
                return Err("workspace read requires exactly one name".into());
            }
            let name = object
                .get("name")
                .and_then(Value::as_str)
                .ok_or("workspace name absent")?;
            if name.is_empty()
                || name.len() > 64
                || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
            {
                return Err("workspace name is not bounded ASCII".into());
            }
            command.arg("--name").arg(name);
        }
        let mut value = self.supervised_json_command(command)?;
        if action == "list" {
            let refs = value
                .get("references")
                .and_then(Value::as_array)
                .ok_or("workspace list has no references")?;
            if refs.len() > 256 {
                return Err("workspace list exceeds 256 references".into());
            }
            let mut names = Vec::with_capacity(refs.len());
            for reference in refs {
                let name = reference
                    .get("name")
                    .and_then(Value::as_str)
                    .ok_or("workspace reference name absent")?;
                let kind = reference
                    .get("kind")
                    .and_then(Value::as_str)
                    .ok_or("workspace reference kind absent")?;
                names.push(json!({"name":name,"kind":kind}));
            }
            value = json!({"type":"mini-grain-workspace-catalog-v1","references":names,
                "authority":"discovery-only; current Mini admission required"});
        }
        if serde_json::to_vec(&value).map_err(|e| e.to_string())?.len() > 1_048_576 {
            return Err("workspace response exceeds 1 MiB".into());
        }
        Ok(value)
    }

    fn workspace_propose(&mut self, arguments: &Value) -> Result<Value> {
        if self.journal.workspace_attempt.is_some() || self.journal.workspace_proposals.len() >= 64
        {
            return Err("workspace has an unresolved effect or 64 retained proposals".into());
        }
        let object = arguments
            .as_object()
            .ok_or("workspace proposal arguments must be an object")?;
        if object.len() != 1 {
            return Err("workspace proposal requires only request".into());
        }
        let request = object
            .get("request")
            .ok_or("workspace proposal request absent")?;
        if request.get("type").and_then(Value::as_str) != Some("minidregg-workspace-proposal-v1")
            || !matches!(
                request.get("action").and_then(Value::as_str),
                Some("invoke" | "install-policy" | "delegate")
            )
        {
            return Err("workspace proposal has unsupported typed action".into());
        }
        let bytes = serde_json::to_vec(request).map_err(|e| e.to_string())?;
        if bytes.len() > 32_768 {
            return Err("workspace proposal exceeds 32 KiB".into());
        }
        let id = self.next_id()?;
        let request_path = self
            .config
            .state_dir
            .join(format!("workspace-proposal-{id:016}.json"));
        write_new(&request_path, &bytes)?;
        let root = self.workspace_root()?;
        let command = {
            let mut command = Command::new(&self.config.mini);
            command
                .arg("workspace")
                .arg("--action")
                .arg("propose")
                .arg("--dir")
                .arg(&root)
                .arg("--request")
                .arg(&request_path)
                .arg("--proposal-id")
                .arg(id.to_string());
            command
        };
        let result = self.supervised_json_command(command)?;
        if result["type"] != "minidregg-workspace-proposal-result-v1"
            || result["proposalId"].as_str() != Some(id.to_string().as_str())
            || result["intentSha256"].as_str().is_none()
        {
            return Err("workspace source proposal result has wrong identity".into());
        }
        let (intent_path, proposal_path) = self.workspace_proposal_paths(id)?;
        let intent_sha256 = sha256_bytes(&bounded_regular_file(&intent_path, 262_144)?)?;
        let summary: Value = serde_json::from_slice(&bounded_regular_file(&proposal_path, 65_536)?)
            .map_err(|e| format!("workspace proposal summary: {e}"))?;
        if summary["intentSha256"].as_str() != Some(intent_sha256.as_str()) {
            return Err("workspace proposal summary differs from source-owned intent".into());
        }
        self.journal.workspace_proposals.push(WorkspaceProposal {
            id,
            request_sha256: sha256_bytes(&bytes)?,
            intent_sha256: intent_sha256.clone(),
            submitted: false,
        });
        self.save()?;
        Ok(
            json!({"proposalId":id.to_string(),"intentSha256":intent_sha256,
            "type":"minidregg-workspace-proposal-result-v1",
            "authority":"proposal-only; Mini checks current law on submit"}),
        )
    }

    fn workspace_submit(&mut self, arguments: &Value) -> Result<Value> {
        let object = arguments
            .as_object()
            .ok_or("workspace submit arguments must be an object")?;
        if object.len() != 1 {
            return Err("workspace submit requires only proposalId".into());
        }
        let selected = object
            .get("proposalId")
            .and_then(Value::as_str)
            .ok_or("workspace proposalId absent")?;
        decimal(selected, "workspace proposalId")?;
        let proposal_id = selected
            .parse::<u64>()
            .map_err(|_| "workspace proposalId exceeds u64")?;
        let proposal = self
            .journal
            .workspace_proposals
            .iter()
            .find(|proposal| proposal.id == proposal_id && !proposal.submitted)
            .ok_or("workspace proposal is absent or already submitted")?
            .clone();
        if self.journal.workspace_attempt.is_some() {
            return Err("workspace effect requires exact recovery before another submit".into());
        }
        let root = self.workspace_root()?;
        let (intent_path, summary_path) = self.workspace_proposal_paths(proposal_id)?;
        let request_path = self
            .config
            .state_dir
            .join(format!("workspace-proposal-{proposal_id:016}.json"));
        if sha256_bytes(&bounded_regular_file(&request_path, 32_768)?)? != proposal.request_sha256
            || sha256_bytes(&bounded_regular_file(&intent_path, 262_144)?)?
                != proposal.intent_sha256
        {
            return Err("workspace retained proposal changed before submission".into());
        }
        let summary: Value = serde_json::from_slice(&bounded_regular_file(&summary_path, 65_536)?)
            .map_err(|e| format!("workspace proposal summary: {e}"))?;
        if summary["intentSha256"].as_str() != Some(proposal.intent_sha256.as_str()) {
            return Err("workspace source summary changed before submission".into());
        }
        let operation_id = self.next_id()?;
        let attempt = root.join("attempts").join(operation_id.to_string());
        if attempt.exists() {
            return Err("workspace operation attempt path is already claimed".into());
        }
        root.to_str().ok_or("workspace path UTF-8")?;
        intent_path.to_str().ok_or("workspace intent path UTF-8")?;
        attempt.to_str().ok_or("workspace attempt path UTF-8")?;
        let tool = self
            .config
            .tool_task
            .as_ref()
            .ok_or("toolTask absent")?
            .clone();
        let authority = self.tool()?;
        let status = self
            .query_as(&authority)?
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("delegated tool status absent")?
            .to_owned();
        if status == "0" {
            self.check_not_cancelled()?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "tool attach",
                "workspace delegated attach",
                vec![],
            )?;
        } else if status != "1" {
            return Err("workspace delegated tool needs signed idle/attached state".into());
        }
        self.check_not_cancelled()?;
        self.mark_hold(true, &tool.reserve, &tool.charge)?;
        self.transition_as(
            &authority,
            json!({"type":"reserve","amount":tool.reserve}),
            "tool reserve",
            "workspace typed submission reserve",
            vec![],
        )?;
        self.check_not_cancelled()?;
        self.journal
            .workspace_proposals
            .iter_mut()
            .find(|saved| saved.id == proposal_id)
            .ok_or("workspace proposal disappeared")?
            .submitted = true;
        self.journal.workspace_attempt = Some(WorkspaceAttempt {
            operation_id,
            proposal_id,
            intent_sha256: proposal.intent_sha256,
            attempt: attempt.clone(),
            definite: false,
            no_submit: false,
        });
        self.save()?;
        let args = [
            "workspace",
            "--action",
            "submit",
            "--dir",
            root.to_str().ok_or("workspace path UTF-8")?,
            "--intent",
            intent_path.to_str().ok_or("workspace intent path UTF-8")?,
            "--attempt",
            attempt.to_str().ok_or("workspace attempt path UTF-8")?,
        ];
        match self.work_output(&self.config.mini, &args) {
            Ok(()) => self.workspace_recover_operation(operation_id, false),
            Err(custody_gate::CustodyError::BeforeSpawn) => {
                self.journal
                    .workspace_attempt
                    .as_mut()
                    .ok_or("workspace attempt disappeared")?
                    .no_submit = true;
                self.save()?;
                self.workspace_recover_operation(operation_id, false)
            }
            Err(error) => {
                // A direct source-inspected refusal is definite even though
                // the CLI exits nonzero. Otherwise the child may have sent
                // the exact call before losing its reply.
                match self.workspace_recover_operation(operation_id, false) {
                    Ok(result) => Ok(result),
                    Err(_) => Err(format!("workspace native outcome unknown: {error}; recover operation {operation_id} by exact lookup")),
                }
            }
        }
    }

    fn workspace_recover_operation(&mut self, operation_id: u64, lookup: bool) -> Result<Value> {
        let root = self.workspace_root()?;
        let pending = self
            .journal
            .workspace_attempt
            .as_ref()
            .filter(|attempt| attempt.operation_id == operation_id)
            .ok_or("no retained workspace attempt for operation ID")?
            .clone();
        if pending.attempt != root.join("attempts").join(operation_id.to_string()) {
            return Err("workspace attempt path differs from its controller operation ID".into());
        }
        let (intent_path, _) = self.workspace_proposal_paths(pending.proposal_id)?;
        if sha256_bytes(&bounded_regular_file(&intent_path, 262_144)?)? != pending.intent_sha256 {
            return Err("workspace operation source changed after reservation".into());
        }
        let configured_charge = self
            .config
            .tool_task
            .as_ref()
            .ok_or("toolTask absent")?
            .charge
            .clone();
        // (resolution, basis, exact outcome, delegated tool charge)
        let decided: (&str, &str, Value, String) = if pending.no_submit {
            (
                "refused",
                "custody-not-spawned",
                json!({"type":"not-submitted"}),
                "0".to_owned(),
            )
        } else {
            let attempt_meta = fs::symlink_metadata(&pending.attempt)
                .map_err(|e| format!("workspace retained attempt: {e}"))?;
            if !attempt_meta.file_type().is_dir()
                || attempt_meta.uid() != unsafe { libc::geteuid() }
                || attempt_meta.mode() & 0o077 != 0
            {
                return Err(
                    "workspace retained attempt must be an owner-private real directory".into(),
                );
            }
            let copied = pending.attempt.join("intent.json");
            if sha256_bytes(&bounded_regular_file(&copied, 262_144)?)? != pending.intent_sha256 {
                return Err("workspace retained attempt intent differs from proposal".into());
            }
            let copied_config = bounded_regular_file(&pending.attempt.join("config.json"), 65_536)?;
            let pinned_config = bounded_regular_file(&self.config.host_config, 65_536)?;
            if copied_config != pinned_config {
                return Err("workspace retained attempt Host config differs from pin".into());
            }
            let mut decided = None;
            let native_outcome = pending.attempt.join("outcome.json");
            if native_outcome.is_file() {
                bounded_regular_file(&pending.attempt.join("call.bin"), 4_194_304)?;
                bounded_regular_file(&pending.attempt.join("outcome.bin"), 4_194_304)?;
                let direct: Value =
                    serde_json::from_slice(&bounded_regular_file(&native_outcome, 131_072)?)
                        .map_err(|e| format!("workspace native outcome JSON: {e}"))?;
                match direct["type"].as_str() {
                    Some("confirmed") => {
                        decided = Some(("performed", "native-outcome", direct, configured_charge.clone()))
                    }
                    Some("refused") => {
                        decided = Some(("refused", "native-refusal", direct, configured_charge.clone()))
                    }
                    _ => {}
                }
            }
            if decided.is_none() && !pending.attempt.join("call.bin").exists() {
                if let Some(refusal) = inspected_pre_submit_refusal(&self.config, &pending.attempt)?
                {
                    decided = Some(("refused", "pre-submit-refusal", refusal, "0".to_owned()));
                }
            }
            if decided.is_none() && lookup {
                let submitter_stopped = self.workspace_submitter_stopped(operation_id);
                if !pending.attempt.join("call.bin").is_file() {
                    if !submitter_stopped {
                        return Err("workspace submission has no retained call; physical child audit is required before release".into());
                    }
                    // The client writes call.bin before its first send. With
                    // every process that could have written it proven gone,
                    // no call for this attempt can ever reach Mini.
                    decided = Some((
                        "refused",
                        "no-call-after-submitter-stop",
                        json!({"type":"not-submitted"}),
                        "0".to_owned(),
                    ));
                } else {
                    let before = retained_retry_names(&pending.attempt)?;
                    let command = {
                        let mut command = Command::new(&self.config.mini);
                        command
                            .arg("workspace")
                            .arg("--action")
                            .arg("recover")
                            .arg("--dir")
                            .arg(&root)
                            .arg("--attempt")
                            .arg(&pending.attempt);
                        command
                    };
                    let transport = self.supervised_json_command(command);
                    let answer = newest_new_retry(&pending.attempt, &before)?;
                    match answer.as_ref().and_then(|value| value["type"].as_str()) {
                        Some("confirmed") => {
                            decided = Some((
                                "performed",
                                "exact-lookup",
                                answer.unwrap_or(Value::Null),
                                configured_charge.clone(),
                            ))
                        }
                        // The pinned `mini serve` handles one connection at
                        // a time in accept order, so an earlier fully sent
                        // frame was decided before this lookup was read.
                        // With the submitter gone, absence is final.
                        Some("absent") if submitter_stopped => {
                            decided = Some((
                                "refused",
                                "absent-after-submitter-stop",
                                answer.unwrap_or(Value::Null),
                                configured_charge.clone(),
                            ))
                        }
                        Some("absent") => {
                            decided = Some((
                                "uncertain",
                                "absent-but-submitter-not-proven-stopped",
                                answer.unwrap_or(Value::Null),
                                configured_charge.clone(),
                            ))
                        }
                        _ => {
                            return Err(format!(
                                "workspace exact lookup gave no definite answer; effect remains pending: {}",
                                transport.err().unwrap_or_else(|| "unrecognized lookup record".into())
                            ));
                        }
                    }
                }
            }
            decided.ok_or(
                "workspace submission has no definite native result; exact lookup is required",
            )?
        };
        let (resolution, basis, outcome, charge) = decided;
        self.journal
            .workspace_attempt
            .as_mut()
            .ok_or("workspace attempt disappeared")?
            .definite = true;
        self.save()?;
        let authority = self.tool()?;
        if self.journal.tool_hold.is_some() {
            self.transition_as(
                &authority,
                json!({"type":"settle","charge":charge}),
                "tool settle",
                "workspace typed operation settlement",
                vec![],
            )?;
        }
        let state = self.query_as(&authority)?;
        match state.pointer("/grain/status").and_then(Value::as_str) {
            Some("1") => self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "tool disconnect",
                "workspace operation complete",
                vec![],
            )?,
            Some("0" | "6") => {}
            // A fenced or held tool purse after controller loss: settle the
            // retained hold before the definite result can be released.
            _ => return Err("workspace settlement lacks signed terminal tool status".into()),
        }
        let terminal = self.query_as(&authority)?;
        if terminal.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            || !matches!(
                terminal.pointer("/grain/status").and_then(Value::as_str),
                Some("0" | "6")
            )
        {
            return Err("workspace tool remains reserved after settlement".into());
        }
        let resolved_by = if !lookup {
            "submit"
        } else if self.startup_recovery_active {
            "restart-recovery"
        } else {
            "lookup"
        };
        let record = WorkspaceResolution {
            operation_id,
            proposal_id: pending.proposal_id,
            intent_sha256: pending.intent_sha256.clone(),
            attempt: pending.attempt.clone(),
            resolution: resolution.to_owned(),
            basis: basis.to_owned(),
            outcome,
            tool_charge: charge,
            resolved_by: resolved_by.to_owned(),
        };
        self.push_workspace_resolution(record.clone());
        self.journal.workspace_attempt = None;
        self.save()?;
        Ok(workspace_resolution_json(&record))
    }

    fn push_workspace_resolution(&mut self, record: WorkspaceResolution) {
        if self.journal.workspace_resolutions.len() >= MAX_WORKSPACE_RESOLUTIONS {
            self.journal.workspace_resolutions.remove(0);
        }
        self.journal.workspace_resolutions.push(record);
    }

    /// True only when no process that could hold this attempt's custody
    /// child is alive: this process reaps its own children before returning
    /// from the custody gate, and a previous controller run is covered by
    /// the startup unit/cgroup proof.
    fn workspace_submitter_stopped(&self, operation_id: u64) -> bool {
        if operation_id >= self.process_first_operation_id {
            self.custody_gate.is_idle()
        } else {
            self.prior_run_stopped
        }
    }

    /// Read-only: one retained resolution, the pending attempt, or the
    /// bounded newest-first list. Nothing here touches Mini.
    fn workspace_attempts(&self, arguments: &Value) -> Result<Value> {
        let object = arguments
            .as_object()
            .ok_or("workspace attempts arguments must be an object")?;
        let selected = match (object.len(), object.get("operationId")) {
            (0, _) => None,
            (1, Some(id)) => {
                let id = id.as_str().ok_or("operationId must be a decimal string")?;
                decimal(id, "operationId")?;
                Some(id.parse::<u64>().map_err(|_| "operationId exceeds u64")?)
            }
            _ => return Err("workspace attempts takes only an optional operationId".into()),
        };
        let pending = self.journal.workspace_attempt.as_ref().map(|attempt| {
            json!({"operationId":attempt.operation_id.to_string(),
                "proposalId":attempt.proposal_id.to_string(),
                "resolution":"pending","definite":attempt.definite,
                "detail":"retained for exact recovery; no further effect is admitted until it resolves"})
        });
        if let Some(id) = selected {
            if let Some(attempt) = self.journal.workspace_attempt.as_ref() {
                if attempt.operation_id == id {
                    return Ok(pending.unwrap_or(Value::Null));
                }
            }
            let record = self
                .journal
                .workspace_resolutions
                .iter()
                .find(|record| record.operation_id == id)
                .ok_or("no retained workspace attempt has this operation ID")?;
            return Ok(workspace_resolution_json(record));
        }
        let records: Vec<Value> = self
            .journal
            .workspace_resolutions
            .iter()
            .rev()
            .take(32)
            .map(workspace_resolution_json)
            .collect();
        Ok(json!({"type":"mini-grain-workspace-attempts-v1","pending":pending,
            "resolutions":records,
            "authority":"historical record of this grain's own submissions; current state requires a signed read"}))
    }

    /// Re-look-up a retained `uncertain` resolution. A confirmation upgrades
    /// it to `performed`; nothing is ever resubmitted and no allowance moves.
    fn workspace_relookup_uncertain(&mut self, operation_id: u64) -> Result<Value> {
        let root = self.workspace_root()?;
        let index = self
            .journal
            .workspace_resolutions
            .iter()
            .position(|record| record.operation_id == operation_id)
            .ok_or("no retained workspace attempt for operation ID")?;
        let record = self.journal.workspace_resolutions[index].clone();
        if record.resolution != "uncertain" {
            return Ok(workspace_resolution_json(&record));
        }
        if record.attempt != root.join("attempts").join(operation_id.to_string()) {
            return Err("retained resolution path differs from its operation ID".into());
        }
        let before = retained_retry_names(&record.attempt)?;
        let mut command = Command::new(&self.config.mini);
        command
            .arg("workspace")
            .arg("--action")
            .arg("recover")
            .arg("--dir")
            .arg(&root)
            .arg("--attempt")
            .arg(&record.attempt);
        let _ = self.supervised_json_command(command);
        let answer = newest_new_retry(&record.attempt, &before)?;
        let updated = match answer.as_ref().and_then(|value| value["type"].as_str()) {
            Some("confirmed") => Some((
                "performed",
                "later-exact-lookup",
                answer.clone().unwrap_or(Value::Null),
            )),
            Some("absent") if self.workspace_submitter_stopped(operation_id) => Some((
                "refused",
                "absent-after-submitter-stop",
                answer.clone().unwrap_or(Value::Null),
            )),
            Some("absent") => None,
            _ => return Err("workspace exact lookup gave no definite answer".into()),
        };
        if let Some((resolution, basis, outcome)) = updated {
            let saved = &mut self.journal.workspace_resolutions[index];
            saved.resolution = resolution.into();
            saved.basis = basis.into();
            saved.outcome = outcome;
            saved.resolved_by = "lookup".into();
            self.save()?;
        }
        Ok(workspace_resolution_json(
            &self.journal.workspace_resolutions[index],
        ))
    }

    fn workspace_recover(&mut self, arguments: &Value) -> Result<Value> {
        let object = arguments
            .as_object()
            .ok_or("workspace recover arguments must be an object")?;
        if object.len() != 1 {
            return Err("workspace recover requires only operationId".into());
        }
        let id = object
            .get("operationId")
            .and_then(Value::as_str)
            .ok_or("workspace operationId absent")?;
        decimal(id, "workspace operationId")?;
        let id = id.parse::<u64>().map_err(|_| "operationId exceeds u64")?;
        if self
            .journal
            .workspace_birth
            .as_ref()
            .is_some_and(|birth| birth.operation_id == id)
        {
            self.workspace_recover_birth(id, true)
        } else if self
            .journal
            .workspace_attempt
            .as_ref()
            .is_some_and(|attempt| attempt.operation_id == id)
        {
            self.workspace_recover_operation(id, true)
        } else {
            self.workspace_relookup_uncertain(id)
        }
    }

    fn supervised_text_command(&self, mut command: Command) -> Result<String> {
        unsafe {
            command.pre_exec(|| {
                libc::umask(0o077);
                Ok(())
            });
        }
        let output = self
            .custody_gate
            .run_capture(&self.cancelled, &mut command)
            .map_err(|error| format!("supervised workspace client: {error}"))?;
        if !output.status.success() {
            return Err(format!(
                "workspace client exited {}: {}",
                output.status,
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        String::from_utf8(output.stdout).map_err(|_| "workspace client output is not UTF-8".into())
    }

    /// Accept a recipient reference another participant published for this
    /// grain's subject. The common client checks the recipient and receipt;
    /// the stored name remains a hint and every use faces Mini admission.
    fn workspace_import_reference(&mut self, arguments: &Value) -> Result<Value> {
        let object = arguments
            .as_object()
            .ok_or("reference import arguments must be an object")?;
        if object.len() != 2 {
            return Err("reference import requires exactly name and reference".into());
        }
        let name = object
            .get("name")
            .and_then(Value::as_str)
            .ok_or("reference import name absent")?;
        if !valid_workspace_name(name) {
            return Err("workspace name is not bounded ASCII".into());
        }
        let reference = object
            .get("reference")
            .filter(|value| value.is_object())
            .ok_or("reference import requires a reference object")?;
        if reference.get("type").and_then(Value::as_str)
            != Some("minidregg-delegated-reference-v1")
        {
            return Err("reference is not a Mini delegated recipient reference".into());
        }
        let bytes = serde_json::to_vec(reference).map_err(|e| e.to_string())?;
        if bytes.len() > 65_536 {
            return Err("recipient reference exceeds 64 KiB".into());
        }
        let root = self.workspace_root()?;
        let id = self.next_id()?;
        let source = self
            .config
            .state_dir
            .join(format!("workspace-import-{id:016}.json"));
        write_new(&source, &bytes)?;
        let mut command = Command::new(&self.config.mini);
        command
            .arg("workspace")
            .arg("--action")
            .arg("import")
            .arg("--dir")
            .arg(&root)
            .arg("--name")
            .arg(name)
            .arg("--from-ref")
            .arg(&source);
        self.supervised_text_command(command)?;
        let stored: Value = serde_json::from_slice(&bounded_regular_file(
            &root.join("refs").join(format!("{name}.json")),
            131_072,
        )?)
        .map_err(|e| format!("imported reference JSON: {e}"))?;
        Ok(json!({"type":"mini-grain-imported-reference-v1","name":name,
            "kind":stored["kind"],"target":stored["target"],
            "capability":stored["observeCapability"],
            "receipt":reference.get("receipt"),
            "authority":"hint-only; every read or write still faces current Mini admission"}))
    }

    /// Publish the recipient reference for a delegation this grain proposed
    /// and whose submission resolved `performed`. The common client does an
    /// exact historical lookup before writing the reference.
    fn workspace_export_reference(&mut self, arguments: &Value) -> Result<Value> {
        let object = arguments
            .as_object()
            .ok_or("reference export arguments must be an object")?;
        if object.len() != 1 {
            return Err("reference export requires only proposalId".into());
        }
        let selected = object
            .get("proposalId")
            .and_then(Value::as_str)
            .ok_or("reference export proposalId absent")?;
        decimal(selected, "proposalId")?;
        let proposal_id = selected
            .parse::<u64>()
            .map_err(|_| "proposalId exceeds u64")?;
        let record = self
            .journal
            .workspace_resolutions
            .iter()
            .rev()
            .find(|record| record.proposal_id == proposal_id)
            .ok_or("proposal has no resolved submission in this grain")?
            .clone();
        if record.resolution != "performed" {
            return Err(format!(
                "delegation submission resolved {}; only a performed delegation has a recipient reference",
                record.resolution
            ));
        }
        let root = self.workspace_root()?;
        let proposal = root.join("proposals").join(proposal_id.to_string());
        let summary: Value =
            serde_json::from_slice(&bounded_regular_file(&proposal.join("proposal.json"), 65_536)?)
                .map_err(|e| format!("workspace proposal summary: {e}"))?;
        if !summary["delegation"].is_object()
            || summary["intentSha256"].as_str() != Some(record.intent_sha256.as_str())
        {
            return Err("resolved proposal is not this grain's delegation".into());
        }
        let mut command = Command::new(&self.config.mini);
        command
            .arg("workspace")
            .arg("--action")
            .arg("publish-delegation")
            .arg("--dir")
            .arg(&root)
            .arg("--proposal-id")
            .arg(proposal_id.to_string())
            .arg("--attempt")
            .arg(&record.attempt);
        self.supervised_text_command(command)?;
        let reference: Value = serde_json::from_slice(&bounded_regular_file(
            &proposal.join("recipient-reference.json"),
            65_536,
        )?)
        .map_err(|e| format!("recipient reference JSON: {e}"))?;
        if reference["type"] != "minidregg-delegated-reference-v1" {
            return Err("client wrote an unknown recipient reference".into());
        }
        Ok(json!({"type":"mini-grain-exported-reference-v1",
            "proposalId":proposal_id.to_string(),"reference":reference,
            "authority":"hint-only; give it to the recipient, whose own signed reads decide use"}))
    }

    fn workspace_create(&mut self, arguments: &Value) -> Result<Value> {
        let object = arguments
            .as_object()
            .ok_or("workspace create arguments must be an object")?;
        if object.len() != 3 {
            return Err("workspace create requires name, storage and predicate".into());
        }
        let name = object
            .get("name")
            .and_then(Value::as_str)
            .ok_or("workspace birth name absent")?;
        if name.is_empty()
            || name.len() > 64
            || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
        {
            return Err("workspace birth name is invalid".into());
        }
        let storage = object
            .get("storage")
            .and_then(Value::as_str)
            .ok_or("workspace storage absent")?;
        if !matches!(storage, "content" | "declared") {
            return Err("workspace storage is unsupported".into());
        }
        let predicate = object
            .get("predicate")
            .ok_or("workspace predicate absent")?;
        if !predicate.is_object() {
            return Err("workspace predicate must be an object".into());
        }
        let predicate_bytes = serde_json::to_vec(predicate).map_err(|e| e.to_string())?;
        if predicate_bytes.len() > 32_768 {
            return Err("workspace predicate exceeds 32 KiB".into());
        }
        let root = self.workspace_root()?;
        let config: Value =
            serde_json::from_slice(&bounded_regular_file(&root.join("workspace.json"), 65_536)?)
                .map_err(|e| format!("workspace birth config: {e}"))?;
        if config["birthContext"].as_str().is_none() || config["namespaceRoot"].as_str().is_none() {
            return Err("workspace has no operator-pinned birth namespace and context".into());
        }
        if root.join("refs").join(format!("{name}.json")).exists()
            || root
                .join("attempts")
                .join(format!("create-{name}"))
                .exists()
            || self.journal.workspace_birth.is_some()
            || self.journal.workspace_attempt.is_some()
        {
            return Err("workspace birth name or native effect is already retained".into());
        }
        let operation_id = self.next_id()?;
        let predicate_path = self
            .config
            .state_dir
            .join(format!("workspace-birth-{operation_id:016}.predicate.json"));
        write_new(&predicate_path, &predicate_bytes)?;
        root.to_str().ok_or("workspace path UTF-8")?;
        predicate_path.to_str().ok_or("predicate path UTF-8")?;
        let tool = self
            .config
            .tool_task
            .as_ref()
            .ok_or("toolTask absent")?
            .clone();
        let authority = self.tool()?;
        let status = self
            .query_as(&authority)?
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("workspace birth tool status absent")?
            .to_owned();
        if status == "0" {
            self.check_not_cancelled()?;
            self.transition_as(
                &authority,
                json!({"type":"attach","soft":false}),
                "tool attach",
                "workspace birth attach",
                vec![],
            )?;
        } else if status != "1" {
            return Err("workspace birth tool is not idle".into());
        }
        self.check_not_cancelled()?;
        self.mark_hold(true, &tool.reserve, &tool.charge)?;
        self.transition_as(
            &authority,
            json!({"type":"reserve","amount":tool.reserve}),
            "tool reserve",
            "workspace birth reserve",
            vec![],
        )?;
        self.check_not_cancelled()?;
        self.journal.workspace_birth = Some(WorkspaceBirth {
            operation_id,
            name: name.to_owned(),
            storage: storage.to_owned(),
            predicate_path: predicate_path.clone(),
            predicate_sha256: sha256_bytes(&predicate_bytes)?,
            attempt: root.join("attempts").join(format!("create-{name}")),
            no_submit: false,
            definite: false,
        });
        self.save()?;
        let args = [
            "workspace",
            "--action",
            "create",
            "--dir",
            root.to_str().ok_or("workspace path UTF-8")?,
            "--name",
            name,
            "--storage",
            storage,
            "--predicate",
            predicate_path.to_str().ok_or("predicate path UTF-8")?,
        ];
        match self.work_output(&self.config.mini,&args) {
            Ok(()) => self.workspace_recover_birth(operation_id,false),
            Err(custody_gate::CustodyError::BeforeSpawn) => {
                self.journal.workspace_birth.as_mut().ok_or("workspace birth marker absent")?.no_submit=true;
                self.save()?;
                self.workspace_recover_birth(operation_id,false)
            }
            Err(error) => match self.workspace_recover_birth(operation_id,false) {
                Ok(value) => Ok(value),
                Err(_) => Err(format!("workspace birth outcome unknown: {error}; exact recovery of operation {operation_id} required")),
            },
        }
    }

    fn workspace_recover_birth(&mut self, operation_id: u64, lookup: bool) -> Result<Value> {
        let root = self.workspace_root()?;
        let birth = self
            .journal
            .workspace_birth
            .as_ref()
            .filter(|birth| birth.operation_id == operation_id)
            .ok_or("no retained workspace birth for operation ID")?
            .clone();
        if birth.attempt != root.join("attempts").join(format!("create-{}", birth.name))
            || sha256_bytes(&bounded_regular_file(&birth.predicate_path, 32_768)?)?
                != birth.predicate_sha256
        {
            return Err("workspace birth request changed after reservation".into());
        }
        let mut outcome: Option<Value> = None;
        let mut pre_submit_refused = false;
        if !birth.no_submit {
            let meta = fs::symlink_metadata(&birth.attempt)
                .map_err(|e| format!("workspace birth attempt: {e}"))?;
            if !meta.file_type().is_dir()
                || meta.uid() != unsafe { libc::geteuid() }
                || meta.mode() & 0o077 != 0
            {
                return Err(
                    "workspace birth attempt is not an owner-private real directory".into(),
                );
            }
            if bounded_regular_file(&birth.attempt.join("config.json"), 65_536)?
                != bounded_regular_file(&self.config.host_config, 65_536)?
            {
                return Err("workspace birth retained Host config differs from pin".into());
            }
            let source_path = root
                .join("sources")
                .join(format!("create-{}.json", birth.name));
            let author_dir = root
                .join("sources")
                .join(format!("create-{}.current", birth.name));
            let source: Value =
                serde_json::from_slice(&bounded_regular_file(&source_path, 262_144)?)
                    .map_err(|e| format!("workspace birth source: {e}"))?;
            let predicate: Value =
                serde_json::from_slice(&bounded_regular_file(&birth.predicate_path, 32_768)?)
                    .map_err(|e| format!("workspace retained predicate: {e}"))?;
            let tool = self.config.tool_task.as_ref().ok_or("toolTask absent")?;
            if source["subject"].as_str() != Some(tool.subject.as_str())
                || source.pointer("/birth/resources/0/predicate") != Some(&predicate)
                || source
                    .pointer("/birth/resources/0/storage")
                    .and_then(Value::as_str)
                    != Some(birth.storage.as_str())
            {
                return Err("workspace birth source differs from retained typed request".into());
            }
            if bounded_regular_file(&author_dir.join("source.json"), 262_144)?
                != bounded_regular_file(&source_path, 262_144)?
                || bounded_regular_file(&birth.attempt.join("intent-source.bin"), 4_194_304)?
                    != bounded_regular_file(&author_dir.join("intent.bin"), 4_194_304)?
            {
                return Err(
                    "workspace birth exact binary attempt differs from current source author"
                        .into(),
                );
            }
            if birth.attempt.join("call.bin").exists() {
                bounded_regular_file(&birth.attempt.join("call.bin"), 4_194_304)?;
            } else if let Some(refusal) =
                inspected_pre_submit_refusal(&self.config, &birth.attempt)?
            {
                pre_submit_refused = true;
                outcome = Some(refusal);
            } else {
                return Err(
                    "workspace birth has no retained call or verified prepare refusal".into(),
                );
            }
            if birth.attempt.join("outcome.json").is_file() {
                let direct: Value = serde_json::from_slice(&bounded_regular_file(
                    &birth.attempt.join("outcome.json"),
                    131_072,
                )?)
                .map_err(|e| format!("workspace birth outcome: {e}"))?;
                if matches!(direct["type"].as_str(), Some("confirmed" | "refused")) {
                    outcome = Some(direct);
                }
            }
            if outcome.is_none() && lookup {
                let mut command = Command::new(&self.config.mini);
                command
                    .arg("workspace")
                    .arg("--action")
                    .arg("recover")
                    .arg("--dir")
                    .arg(&root)
                    .arg("--attempt")
                    .arg(&birth.attempt);
                let historical = self.supervised_json_command(command)?;
                if historical["type"] != "confirmed" {
                    return Err("workspace birth exact lookup has no accepted receipt".into());
                }
                outcome = Some(historical);
            }
            if outcome.is_none() {
                return Err("workspace birth has no definite native outcome".into());
            }
        }
        let outcome_type = outcome.as_ref().and_then(|value| value["type"].as_str());
        let mut reference = None;
        if outcome_type == Some("confirmed") {
            // The CLI's reentry is lookup-only once this exact call exists.
            // This completes a reference when the native birth succeeded but
            // its first process died before writing the local reference.
            let ref_path = root.join("refs").join(format!("{}.json", birth.name));
            if !ref_path.is_file() {
                let mut command = Command::new(&self.config.mini);
                command
                    .arg("workspace")
                    .arg("--action")
                    .arg("create")
                    .arg("--dir")
                    .arg(&root)
                    .arg("--name")
                    .arg(&birth.name)
                    .arg("--storage")
                    .arg(&birth.storage)
                    .arg("--predicate")
                    .arg(&birth.predicate_path);
                self.supervised_json_command(command)?;
            }
            let result: Value = serde_json::from_slice(&bounded_regular_file(&ref_path, 65_536)?)
                .map_err(|e| format!("workspace birth reference: {e}"))?;
            if result["name"].as_str() != Some(birth.name.as_str())
                || result
                    .pointer("/provenance/birthReceipt/type")
                    .and_then(Value::as_str)
                    != Some("confirmed")
                || ["transactionId", "eventId", "acceptedCount", "imageBoundary"]
                    .iter()
                    .any(|field| {
                        result
                            .pointer(&format!("/provenance/birthReceipt/{field}"))
                            .and_then(Value::as_str)
                            != outcome
                                .as_ref()
                                .and_then(|value| value.get(*field))
                                .and_then(Value::as_str)
                    })
            {
                return Err("workspace birth reference lacks exact accepted provenance".into());
            }
            reference = Some(json!({"name":birth.name,"kind":result["kind"],
                "authority":"reference-only; current Mini admission required"}));
        }
        self.journal
            .workspace_birth
            .as_mut()
            .ok_or("workspace birth marker absent")?
            .definite = true;
        self.save()?;
        let authority = self.tool()?;
        let charge = if birth.no_submit || pre_submit_refused {
            "0".to_owned()
        } else {
            self.config
                .tool_task
                .as_ref()
                .ok_or("toolTask absent")?
                .charge
                .clone()
        };
        if self.journal.tool_hold.is_some() {
            self.transition_as(
                &authority,
                json!({"type":"settle","charge":charge}),
                "tool settle",
                "workspace birth settlement",
                vec![],
            )?;
        }
        let status = self.query_as(&authority)?;
        match status.pointer("/grain/status").and_then(Value::as_str) {
            Some("1") => self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "tool disconnect",
                "workspace birth complete",
                vec![],
            )?,
            Some("0" | "6") => {}
            _ => return Err("workspace birth has no signed settled tool status".into()),
        }
        let terminal = self.query_as(&authority)?;
        if terminal.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            || !matches!(
                terminal.pointer("/grain/status").and_then(Value::as_str),
                Some("0" | "6")
            )
        {
            return Err("workspace birth tool remains reserved".into());
        }
        self.journal.workspace_birth = None;
        self.save()?;
        Ok(
            json!({"operationId":operation_id.to_string(),"name":birth.name,
            "outcome":outcome.unwrap_or_else(||json!({"type":"not-submitted"})),
            "reference":reference,"toolCharge":charge,"historical":true}),
        )
    }

    fn tool_call(&mut self, name: &str, arguments: &Value) -> Result<Value> {
        if self.cancelled.load(Ordering::SeqCst)
            || self.journal.connection == Connection::Fenced
            || (self.journal.child.is_none() && self.foreground_operation.is_none())
            || self.journal.pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || (!self.prompt_active && self.foreground_operation.is_none())
        {
            return Err("Hermes task is not running under this controller".into());
        }
        if name == "mini_workspace_recover" {
            return self.workspace_recover(arguments);
        }
        if name == "mini_workspace_attempts" {
            return self.workspace_attempts(arguments);
        }
        if self.journal.workspace_attempt.is_some()
            || self.journal.workspace_birth.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.birth_operation.is_some()
            || self.journal.birth_pending.is_some()
        {
            return Err(
                "delegated tool has an unresolved native attempt or held allowance; exact lookup and owner reconciliation are required before another tool call".into(),
            );
        }
        let authority = self.tool()?;
        match name {
            "mini_workspace_list" => self.workspace_readonly("list", arguments),
            "mini_workspace_describe" => self.workspace_readonly("describe", arguments),
            "mini_workspace_read" => self.workspace_readonly("read", arguments),
            "mini_workspace_propose" => self.workspace_propose(arguments),
            "mini_workspace_submit" => self.workspace_submit(arguments),
            "mini_workspace_create" => self.workspace_create(arguments),
            "mini_workspace_import_reference" => self.workspace_import_reference(arguments),
            "mini_workspace_export_reference" => self.workspace_export_reference(arguments),
            "mini_grain_status" => {
                if arguments != &json!({}) && !arguments.is_null() {
                    return Err("mini_grain_status takes no arguments".into());
                }
                let parent = self.query()?;
                let tool = self.query_as(&authority)?;
                Ok(json!({"parent":parent,"tool":tool}))
            }
            "mini_read_resource" => {
                let configured = self
                    .config
                    .tool_task
                    .as_ref()
                    .ok_or("toolTask is not configured")?
                    .clone();
                let mut reads = configured.allowed_reads.clone();
                if let Some(name) = arguments.get("name").and_then(Value::as_str) {
                    if let Some(born) = self.verified_born_named(name)? {
                        reads.push(resource_tools::born_read(&born));
                    }
                }
                // A factory-minted owner capability carries both observe and
                // mutate verbs. Static validate_reads intentionally rejects
                // that combination; dynamic entries enter only after their
                // exact composite receipt is revalidated above.
                let read = resource_tools::select_read(&reads, arguments)?.clone();
                let nonce = self.next_id()?;
                self.supervised_resource_read(&configured, &read, nonce)
            }
            "mini_create_resource" => {
                if self.tool_catalog()?.resource_workspace_create {
                    return Err(
                        "fixed resource birth is superseded by this task's common workspace".into(),
                    );
                }
                self.create_resource(arguments, None)
            }
            "mini_create_application" => {
                self.create_resource(arguments, Some(ApplicationBirthRoute::Application))
            }
            "mini_create_application_session" => {
                self.create_resource(arguments, Some(ApplicationBirthRoute::Session))
            }
            "mini_publish" => {
                let supplied = arguments
                    .get("publications")
                    .and_then(Value::as_array)
                    .ok_or("publications must be an array")?;
                if supplied.is_empty() || supplied.len() > 8 {
                    return Err("publication count must be 1 through 8".into());
                }
                if serde_json::to_vec(arguments)
                    .map_err(|e| e.to_string())?
                    .len()
                    > 32_768
                {
                    return Err("publication request exceeds 32 KiB".into());
                }
                let tool = self
                    .config
                    .tool_task
                    .as_ref()
                    .ok_or("toolTask is not configured")?
                    .clone();
                let mut publications = Vec::new();
                for source in supplied {
                    let object = source.as_object().ok_or("publication must be an object")?;
                    if object.keys().any(|k| {
                        !matches!(
                            k.as_str(),
                            "kind" | "target" | "expectedTargetRoot" | "payload"
                        )
                    }) || object.len() != 4
                    {
                        return Err("publication fields are not canonical".into());
                    }
                    let kind = source
                        .get("kind")
                        .and_then(Value::as_str)
                        .ok_or("publication kind")?;
                    let target = source
                        .get("target")
                        .and_then(Value::as_str)
                        .ok_or("publication target")?;
                    let allowed = if let Some(configured) = tool
                        .allowed_publications
                        .iter()
                        .find(|g| g.kind == kind && g.target == target)
                    {
                        configured.clone()
                    } else {
                        let born = self
                            .verified_born_target(kind, target)?
                            .ok_or("publication target is not delegated")?;
                        resource_tools::born_publication(&born)
                    };
                    let root = source
                        .get("expectedTargetRoot")
                        .and_then(Value::as_str)
                        .ok_or("expectedTargetRoot must be decimal string")?;
                    decimal(root, "expectedTargetRoot")?;
                    let payload = source
                        .get("payload")
                        .ok_or("publication payload absent")?
                        .clone();
                    publications.push(
                        json!({"kind":kind,"target":target,"capability":allowed.capability,
                        "observeCapability":allowed.observe_capability,"schemaVersion":"1",
                        "expectedTargetRoot":root,"payload":payload}),
                    );
                }
                // The settle transition journals one verified receipt before
                // returning. Bind the tool response to that new record and the
                // active prompt, never to a previous publication on this task.
                let (prompt_operation_id, session_id, work_origin) = self.current_work_origin()?;
                let target_ids: Vec<String> = publications
                    .iter()
                    .map(|publication| {
                        publication["target"]
                            .as_str()
                            .ok_or_else(|| "validated publication target absent".to_owned())
                            .map(str::to_owned)
                    })
                    .collect::<Result<_>>()?;
                let prior_receipt_ids: Vec<u64> = self
                    .journal
                    .publication_receipts
                    .iter()
                    .map(|record| record.operation_id)
                    .collect();
                let status = self
                    .query_as(&authority)?
                    .pointer("/grain/status")
                    .and_then(Value::as_str)
                    .ok_or("tool grain status absent")?
                    .to_owned();
                if status == "0" {
                    self.check_not_cancelled()?;
                    self.transition_as(
                        &authority,
                        json!({"type":"attach","soft":false}),
                        "tool attach",
                        "Hermes delegated tool attach",
                        vec![],
                    )?;
                } else if status != "1" {
                    return Err(format!("tool task status {status} needs reconciliation"));
                }
                self.check_not_cancelled()?;
                self.mark_hold(true, &tool.reserve, &tool.charge)?;
                self.transition_as(
                    &authority,
                    json!({"type":"reserve","amount":tool.reserve}),
                    "tool reserve",
                    "Hermes delegated publication reserve",
                    vec![],
                )?;
                self.check_not_cancelled()?;
                let publication = self.transition_as(
                    &authority,
                    json!({"type":"settle","charge":tool.charge}),
                    "tool settle",
                    "Hermes delegated publication settle",
                    publications,
                );
                if let Err(error) = publication {
                    // A definitive native refusal did not publish any target.
                    // Release the held allowance through another signed Mini
                    // transition. An uncertain call keeps its exact attempt
                    // and reservation for lookup instead.
                    if error.starts_with("tool settle refused by Mini:")
                        && self.journal.tool_pending.is_none()
                        && !self.cancelled.load(Ordering::SeqCst)
                    {
                        let release = self.transition_as(
                            &authority,
                            json!({"type":"settle","charge":"0"}),
                            "tool release",
                            "definitively refused publication",
                            vec![],
                        );
                        match release {
                            Ok(()) => {
                                match self.transition_as(
                                    &authority,
                                    json!({"type":"disconnect"}),
                                    "tool disconnect",
                                    "refused publication cleanup",
                                    vec![],
                                ) {
                                    Ok(()) => {
                                        return Err(format!(
                                            "{error}; signed zero-charge tool release and disconnect confirmed; if this prompt remains active, a fresh signed read may precede a new publication"
                                        ));
                                    }
                                    Err(cleanup) => {
                                        let disposition = if self.journal.tool_pending.is_some() {
                                            "exact lookup or owner reconciliation is required before retry"
                                        } else {
                                            "inspect the current signed tool state before retry"
                                        };
                                        return Err(format!(
                                            "{error}; zero-charge tool release confirmed, but disconnect cleanup did not confirm: {cleanup}; {disposition}"
                                        ));
                                    }
                                }
                            }
                            Err(cleanup) => {
                                return Err(format!(
                                    "{error}; zero-charge tool release unresolved or refused: {cleanup}; retained tool allowance requires exact lookup or owner reconciliation before retry"
                                ));
                            }
                        }
                    }
                    return Err(format!(
                        "{error}; delegated tool allowance remains unresolved; exact lookup or owner reconciliation is required before retry"
                    ));
                }
                self.check_not_cancelled()?;
                self.transition_as(
                    &authority,
                    json!({"type":"disconnect"}),
                    "tool disconnect",
                    "Hermes delegated tool detach",
                    vec![],
                )?;
                let mut tool_view = self.query_as(&authority)?;
                let receipt = current_publication_receipt(
                    &self.journal.publication_receipts,
                    &prior_receipt_ids,
                    prompt_operation_id,
                    &session_id,
                    work_origin.as_ref(),
                    &target_ids,
                )?;
                tool_view["publicationReceipt"] = publication_receipt_json(receipt);
                Ok(tool_view)
            }
            _ => Err("tool is not delegated".into()),
        }
    }

    /// Reject definite input errors before taking a signed parent allowance.
    /// This is only a syntax/operator-profile preflight; the normal tool path
    /// still verifies every native grant and current source state.
    fn preflight_foreground_arguments(&self, request: &ForegroundRequest) -> Result<()> {
        let arguments = &request.arguments;
        let tool = self
            .config
            .tool_task
            .as_ref()
            .ok_or("toolTask is not configured")?;
        match request.name.as_str() {
            "mini_workspace_list" => {
                if arguments != &json!({}) && !arguments.is_null() {
                    return Err("workspace list takes no arguments".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_describe" | "mini_workspace_read" => {
                let object = arguments
                    .as_object()
                    .ok_or("workspace read requires a name")?;
                let name = object
                    .get("name")
                    .and_then(Value::as_str)
                    .ok_or("workspace name absent")?;
                if object.len() != 1
                    || name.is_empty()
                    || name.len() > 64
                    || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
                {
                    return Err("workspace name is invalid".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_propose" => {
                let object = arguments
                    .as_object()
                    .ok_or("workspace proposal requires request")?;
                let request = object.get("request").ok_or("workspace request absent")?;
                if object.len() != 1
                    || request.get("type").and_then(Value::as_str)
                        != Some("minidregg-workspace-proposal-v1")
                    || !matches!(
                        request.get("action").and_then(Value::as_str),
                        Some("invoke" | "install-policy" | "delegate")
                    )
                    || serde_json::to_vec(arguments)
                        .map_err(|e| e.to_string())?
                        .len()
                        > 32_768
                {
                    return Err("workspace proposal has invalid typed action or byte bound".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_submit" => {
                let object = arguments
                    .as_object()
                    .ok_or("workspace submit requires proposalId")?;
                let id = object
                    .get("proposalId")
                    .and_then(Value::as_str)
                    .ok_or("proposalId absent")?;
                decimal(id, "proposalId")?;
                let parsed = id.parse::<u64>().map_err(|_| "proposalId exceeds u64")?;
                if object.len() != 1
                    || !self
                        .journal
                        .workspace_proposals
                        .iter()
                        .any(|proposal| proposal.id == parsed && !proposal.submitted)
                {
                    return Err("workspace proposal unavailable for submit".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_create" => {
                let object = arguments
                    .as_object()
                    .ok_or("workspace create requires object")?;
                let name = object
                    .get("name")
                    .and_then(Value::as_str)
                    .ok_or("birth name absent")?;
                let storage = object
                    .get("storage")
                    .and_then(Value::as_str)
                    .ok_or("storage absent")?;
                let predicate = object.get("predicate").ok_or("predicate absent")?;
                if object.len() != 3
                    || name.is_empty()
                    || name.len() > 64
                    || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
                    || !matches!(storage, "content" | "declared")
                    || !predicate.is_object()
                    || serde_json::to_vec(predicate)
                        .map_err(|e| e.to_string())?
                        .len()
                        > 32_768
                {
                    return Err("workspace create has invalid typed input".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_recover" => {
                let object = arguments
                    .as_object()
                    .ok_or("workspace recover requires operationId")?;
                let id = object
                    .get("operationId")
                    .and_then(Value::as_str)
                    .ok_or("operationId absent")?;
                decimal(id, "operationId")?;
                if object.len() != 1
                    || (!self
                        .journal
                        .workspace_attempt
                        .as_ref()
                        .is_some_and(|pending| pending.operation_id.to_string() == id)
                        && !self
                            .journal
                            .workspace_birth
                            .as_ref()
                            .is_some_and(|birth| birth.operation_id.to_string() == id)
                        && !self
                            .journal
                            .workspace_resolutions
                            .iter()
                            .any(|record| record.operation_id.to_string() == id))
                {
                    return Err("workspace attempt unavailable for recovery".into());
                }
            }
            "mini_workspace_attempts" => {
                let object = arguments
                    .as_object()
                    .ok_or("workspace attempts takes an object")?;
                let valid = match (object.len(), object.get("operationId")) {
                    (0, _) => true,
                    (1, Some(id)) => id.as_str().is_some_and(|id| decimal(id, "operationId").is_ok()),
                    _ => false,
                };
                if !valid {
                    return Err("workspace attempts takes only an optional operationId".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_import_reference" => {
                let object = arguments
                    .as_object()
                    .ok_or("reference import requires an object")?;
                let name = object
                    .get("name")
                    .and_then(Value::as_str)
                    .ok_or("reference import name absent")?;
                if object.len() != 2
                    || !valid_workspace_name(name)
                    || !object.get("reference").is_some_and(Value::is_object)
                    || serde_json::to_vec(arguments)
                        .map_err(|e| e.to_string())?
                        .len()
                        > 65_536
                {
                    return Err("reference import has invalid typed input".into());
                }
                self.workspace_root()?;
            }
            "mini_workspace_export_reference" => {
                let object = arguments
                    .as_object()
                    .ok_or("reference export requires proposalId")?;
                let id = object
                    .get("proposalId")
                    .and_then(Value::as_str)
                    .ok_or("proposalId absent")?;
                decimal(id, "proposalId")?;
                if object.len() != 1 {
                    return Err("reference export requires only proposalId".into());
                }
                self.workspace_root()?;
            }
            "mini_grain_status" => {
                if arguments != &json!({}) && !arguments.is_null() {
                    return Err("mini_grain_status takes no arguments".into());
                }
            }
            "mini_read_resource" => {
                let object = arguments
                    .as_object()
                    .ok_or("read arguments must be an object")?;
                if object.len() != 1 {
                    return Err("read requires exactly one name".into());
                }
                let name = object
                    .get("name")
                    .and_then(Value::as_str)
                    .ok_or("read name must be a string")?;
                if !tool.allowed_reads.iter().any(|read| read.name == name)
                    && !self
                        .journal
                        .born_resources
                        .iter()
                        .any(|born| born.pending.born.name == name)
                {
                    return Err("resource read name is not configured or recorded".into());
                }
            }
            "mini_create_resource" => {
                if self.tool_catalog()?.resource_workspace_create {
                    return Err(
                        "fixed resource birth is superseded by this task's common workspace".into(),
                    );
                }
                resource_tools::select_birth(&tool.allowed_birth_families, arguments)?;
            }
            "mini_create_application" | "mini_create_application_session" => {
                let object = arguments
                    .as_object()
                    .ok_or("birth arguments must be an object")?;
                let session = request.name == "mini_create_application_session";
                if object.len() != if session { 2 } else { 1 } {
                    return Err("birth tool has unexpected arguments".into());
                }
                let family = object
                    .get("family")
                    .and_then(Value::as_str)
                    .ok_or("birth family must be a name")?;
                if session {
                    let app = object
                        .get("application")
                        .and_then(Value::as_str)
                        .ok_or("session birth requires application")?;
                    if app.is_empty()
                        || app.len() > 64
                        || !tool
                            .allowed_session_families
                            .iter()
                            .any(|entry| entry.name == family)
                    {
                        return Err("session family or application is unavailable".into());
                    }
                    if !self
                        .journal
                        .born_resources
                        .iter()
                        .any(|born| born.pending.born.name == app)
                        && !tool
                            .registered_shared_applications
                            .iter()
                            .any(|entry| entry.name == app)
                    {
                        return Err("session application is not recorded or registered".into());
                    }
                } else if !tool
                    .allowed_application_families
                    .iter()
                    .any(|entry| entry.name == family)
                {
                    return Err("application family is not allowlisted".into());
                }
                let pin = tool
                    .current_birth_host_sha256
                    .as_deref()
                    .ok_or("current application birth is not enabled by operator Host pin")?;
                if self.config.host_socket.is_none() || sha256_file(&self.config.host)? != pin {
                    return Err(
                        "current application birth Host image or socket differs from operator pin"
                            .into(),
                    );
                }
            }
            "mini_publish" => {
                let supplied = arguments
                    .get("publications")
                    .and_then(Value::as_array)
                    .ok_or("publications must be an array")?;
                if supplied.is_empty()
                    || supplied.len() > 8
                    || serde_json::to_vec(arguments)
                        .map_err(|e| e.to_string())?
                        .len()
                        > 32_768
                {
                    return Err("publication request exceeds count or byte bound".into());
                }
                for source in supplied {
                    let object = source.as_object().ok_or("publication must be an object")?;
                    if object.len() != 4
                        || object.keys().any(|key| {
                            !matches!(
                                key.as_str(),
                                "kind" | "target" | "expectedTargetRoot" | "payload"
                            )
                        })
                    {
                        return Err("publication fields are not canonical".into());
                    }
                    let kind = source
                        .get("kind")
                        .and_then(Value::as_str)
                        .ok_or("publication kind")?;
                    let target = source
                        .get("target")
                        .and_then(Value::as_str)
                        .ok_or("publication target")?;
                    decimal(
                        source
                            .get("expectedTargetRoot")
                            .and_then(Value::as_str)
                            .ok_or("expectedTargetRoot must be decimal string")?,
                        "expectedTargetRoot",
                    )?;
                    if !tool
                        .allowed_publications
                        .iter()
                        .any(|entry| entry.kind == kind && entry.target == target)
                        && !self.journal.born_resources.iter().any(|born| {
                            born.pending.born.kind == kind && born.pending.born.target == target
                        })
                    {
                        return Err("publication target is not configured or recorded".into());
                    }
                }
            }
            "mini_application_api" => {
                let mut allowed = tool
                    .allowed_application_api_routes
                    .iter()
                    .map(|route| route.name.clone())
                    .collect::<Vec<_>>();
                allowed.extend(
                    tool.allowed_application_lifetime_routes
                        .iter()
                        .map(|route| route.name.clone()),
                );
                let input = application_api_tools::parse_input(arguments, &allowed)?;
                let lifetime = tool
                    .allowed_application_lifetime_routes
                    .iter()
                    .find(|route| route.name == input.application);
                let pin = if lifetime.is_some() {
                    tool.lifetime_api_host_sha256.as_deref().ok_or(
                        "lifetime application Host pin absent; agent delivery is unavailable",
                    )?
                } else {
                    tool.agent_api_host_sha256.as_deref().ok_or(
                        "application API event21 Host pin is absent; agent delivery is unavailable",
                    )?
                };
                if self.config.host_socket.is_none() || sha256_file(&self.config.host)? != pin {
                    return Err(
                        "application API event21 Host image or socket differs from pin".into(),
                    );
                }
                let (name, app_target) = if let Some(route) = lifetime {
                    (&route.name, &route.app_resource)
                } else {
                    let route = tool
                        .allowed_application_api_routes
                        .iter()
                        .find(|route| route.name == input.application)
                        .ok_or("application API route is absent")?;
                    (&route.name, &route.app_resource)
                };
                if !tool
                    .registered_shared_applications
                    .iter()
                    .any(|entry| entry.name == *name && entry.app_target == *app_target)
                    && !self.journal.born_resources.iter().any(|born| {
                        born.pending.born.name == *name && born.pending.born.target == *app_target
                    })
                {
                    return Err(
                        "application API route has no recorded app birth or shared registration"
                            .into(),
                    );
                }
            }
            _ => return Err("foreground tool is not delegated".into()),
        }
        Ok(())
    }

    /// Run one model-free tool call under the same signed parent/tool custody.
    /// The foreground operation ID is durable before reserve or any native
    /// submit; a lost result can only be inspected, never replayed as work.
    fn foreground_tool(
        &mut self,
        attachment_id: u64,
        frame: &[u8],
        input: &Receiver<Input>,
    ) -> Result<()> {
        if frame.is_empty() || frame.len() > 262_144 {
            return Err("foreground request exceeds 256 KiB".into());
        }
        let request: ForegroundRequest =
            serde_json::from_slice(frame).map_err(|e| format!("foreground request: {e}"))?;
        if !valid_foreground_request_id(&request.request_id) {
            return Err("foreground requestId must be 32 lowercase hex characters".into());
        }
        let request_sha256 = sha256_bytes(frame)?;
        if let Some(prior) = read_foreground_tombstone(&self.config.state_dir, &request.request_id)?
        {
            if prior.request_sha256 != request_sha256 {
                return Err("foreground requestId was already used for different bytes".into());
            }
            return Err(format!("foreground requestId {} is durably claimed by operation {}; inspect it without resubmitting", request.request_id, prior.operation_id));
        }
        if let Some(prior) = self
            .journal
            .foreground_history
            .iter()
            .chain(self.journal.foreground_attempt.iter())
            .find(|prior| prior.request_id == request.request_id)
        {
            if prior.request_sha256 != request_sha256 {
                return Err("foreground requestId was already used for different bytes".into());
            }
            return Err(format!("foreground requestId {} is retained as operation {}; inspect it without resubmitting", request.request_id, prior.operation_id));
        }
        if request.name.is_empty()
            || request.name.len() > 64
            || !request
                .name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-' || byte == b'_')
        {
            return Err("foreground tool name is invalid".into());
        }
        if !matches!(
            request.name.as_str(),
            "mini_grain_status"
                | "mini_workspace_list"
                | "mini_workspace_describe"
                | "mini_workspace_read"
                | "mini_workspace_propose"
                | "mini_workspace_submit"
                | "mini_workspace_create"
                | "mini_workspace_recover"
                | "mini_workspace_attempts"
                | "mini_workspace_import_reference"
                | "mini_workspace_export_reference"
                | "mini_read_resource"
                | "mini_create_resource"
                | "mini_create_application"
                | "mini_create_application_session"
                | "mini_publish"
                | "mini_application_api"
        ) {
            return Err("foreground tool is not delegated".into());
        }
        let profile = self
            .config
            .foreground_tool
            .clone()
            .ok_or("foregroundTool is not configured")?;
        self.preflight_foreground_arguments(&request)?;
        if !self
            .output
            .as_ref()
            .is_some_and(|output| output.is_active_framed_attachment(attachment_id))
            || !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || self.cancelled.load(Ordering::SeqCst)
            || self.journal.child.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.pending.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.workspace_attempt.is_some()
            || self.journal.workspace_birth.is_some()
            || self.journal.birth_operation.is_some()
            || self.journal.birth_pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || self.journal.application_api_attempt.is_some()
            || self.journal.settlement_due.is_some()
            || !self.journal.unresolved_external.is_empty()
        {
            return Err("foreground tool requires an attached, reconciled idle task".into());
        }
        if self.journal.foreground_history.len() >= 256 {
            let Some(index) = self
                .journal
                .foreground_history
                .iter()
                .position(|attempt| attempt.reported)
            else {
                return Err("foreground history has 256 unacknowledged results".into());
            };
            self.journal.foreground_history.remove(index);
            self.save()?;
        }
        let operation_id = self.next_id()?;
        let request_path = self
            .config
            .state_dir
            .join(format!("foreground-{operation_id:016}.request.json"));
        let tombstone = ForegroundTombstone {
            request_id: request.request_id.clone(),
            operation_id,
            request_sha256: request_sha256.clone(),
        };
        write_new(
            &foreground_tombstone_path(&self.config.state_dir, &request.request_id),
            &serde_json::to_vec(&tombstone).map_err(|e| e.to_string())?,
        )?;
        write_new(&request_path, frame)?;
        self.journal.foreground_attempt = Some(ForegroundAttempt {
            request_id: request.request_id.clone(),
            operation_id,
            name: request.name.clone(),
            request_sha256,
            request_path,
            phase: ForegroundPhase::Prepared,
            result_path: None,
            result_sha256: None,
            reported: false,
        });
        self.save()?;
        let outcome = (|| -> Result<Value> {
            self.reserve_parent_work_lease(&profile.reserve, &profile.charge, "foreground tool")?;
            self.journal.foreground_attempt.as_mut().unwrap().phase = ForegroundPhase::Reserved;
            self.save()?;
            self.foreground_operation = Some(operation_id);
            self.completion_phase.store(PHASE_RUNNING, Ordering::SeqCst);
            self.journal.foreground_attempt.as_mut().unwrap().phase = ForegroundPhase::Executing;
            self.save()?;
            let result = if request.name == "mini_application_api" {
                self.foreground_application_api(&request.arguments, input)?
            } else {
                self.tool_call(&request.name, &request.arguments)
                    .map(|value| json!({"isError":false,"text":value.to_string()}))?
            };
            self.check_not_cancelled()?;
            Ok(result)
        })();
        self.foreground_operation = None;
        let result = match outcome {
            Ok(value) => value,
            Err(error) => {
                if self.journal.parent_hold.is_none()
                    && self.journal.pending.is_none()
                    && self.journal.tool_hold.is_none()
                    && self.journal.tool_pending.is_none()
                    && self.journal.dispatch_hold.is_none()
                    && self.journal.dispatch_attempt.is_none()
                    && self.journal.application_api_attempt.is_none()
                    && !self.cancelled.load(Ordering::SeqCst)
                {
                    let (result, bytes) =
                        bounded_foreground_result(json!({"isError":true,"text":error}))?;
                    let path = self
                        .config
                        .state_dir
                        .join(format!("foreground-{operation_id:016}.result.json"));
                    write_new(&path, &bytes)?;
                    let attempt = self.journal.foreground_attempt.as_mut().unwrap();
                    attempt.result_sha256 = Some(sha256_bytes(&bytes)?);
                    attempt.result_path = Some(path);
                    attempt.phase = ForegroundPhase::Definite;
                    self.save()?;
                    let _queued = self.output.as_ref().is_some_and(|output| {
                        output.try_tool_event_for(
                            attachment_id,
                            json!({"v":1,
                            "type":"tool-complete","operationId":operation_id.to_string(),
                            "requestId":request.request_id,
                            "isError":true,"result":result}),
                        )
                    });
                    let finished = self.journal.foreground_attempt.take().unwrap();
                    self.journal.foreground_history.push(finished);
                    self.save()?;
                    return Ok(());
                }
                if let Some(attempt) = self.journal.foreground_attempt.as_mut() {
                    attempt.phase = ForegroundPhase::Uncertain;
                }
                self.save()?;
                let fence = self.disconnect();
                return Err(format!(
                    "foreground operation {operation_id} requires exact recovery: {error}; fence={fence:?}"
                ));
            }
        };
        let result_path = self
            .config
            .state_dir
            .join(format!("foreground-{operation_id:016}.result.json"));
        let (result, result_bytes) = bounded_foreground_result(result)?;
        write_new(&result_path, &result_bytes)?;
        let attempt = self.journal.foreground_attempt.as_mut().unwrap();
        attempt.result_sha256 = Some(sha256_bytes(&result_bytes)?);
        attempt.result_path = Some(result_path);
        self.save()?;
        if !self.claim_completion(&profile.charge)? {
            self.disconnect()?;
            return Err("hard disconnect before foreground settlement".into());
        }
        self.transition(
            json!({"type":"settle","charge":profile.charge}),
            "settle",
            "foreground tool complete",
        )?;
        self.journal.prompt_witness = None;
        self.journal.foreground_attempt.as_mut().unwrap().phase = ForegroundPhase::Definite;
        self.save()?;
        self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
        self.finish_reconnected_mode()?;
        let _queued = self.output.as_ref().is_some_and(|output| {
            output.try_tool_event_for(
                attachment_id,
                json!({"v":1,"type":"tool-complete","operationId":operation_id.to_string(),
                    "requestId":request.request_id,
                    "isError":result.get("isError").and_then(Value::as_bool).unwrap_or(true),
                    "result":result}),
            )
        });
        let finished = self.journal.foreground_attempt.take().unwrap();
        if self.journal.foreground_history.len() >= 256 {
            let Some(index) = self
                .journal
                .foreground_history
                .iter()
                .position(|attempt| attempt.reported)
            else {
                self.journal.foreground_attempt = Some(finished);
                self.save()?;
                return Err("foreground result archive has 256 unacknowledged results".into());
            };
            self.journal.foreground_history.remove(index);
        }
        self.journal.foreground_history.push(finished);
        self.save()?;
        Ok(())
    }

    fn foreground_result(&self, request_id: &str) -> Result<(u64, Value)> {
        if !valid_foreground_request_id(request_id) {
            return Err("foreground requestId is invalid".into());
        }
        let record = self
            .journal
            .foreground_history
            .iter()
            .find(|record| record.request_id == request_id)
            .or_else(|| {
                self.journal
                    .foreground_attempt
                    .as_ref()
                    .filter(|record| record.request_id == request_id)
            });
        let Some(record) = record else {
            return if let Some(tombstone) =
                read_foreground_tombstone(&self.config.state_dir, request_id)?
            {
                Err(format!("foreground operation {} is durably claimed without a retained result; inspect or audit, never resubmit", tombstone.operation_id))
            } else {
                Err("foreground requestId is not retained".into())
            };
        };
        if record.phase != ForegroundPhase::Definite {
            return Err(format!(
                "foreground operation {} is {:?}; exact recovery is required",
                record.operation_id, record.phase
            ));
        }
        let path = record
            .result_path
            .as_ref()
            .ok_or("foreground result path absent")?;
        let digest = record
            .result_sha256
            .as_deref()
            .ok_or("foreground result digest absent")?;
        let bytes = bounded_regular_file(path, 1_048_576)?;
        if sha256_bytes(&bytes)? != digest {
            return Err("foreground result bytes changed".into());
        }
        let result =
            serde_json::from_slice(&bytes).map_err(|e| format!("foreground result JSON: {e}"))?;
        Ok((record.operation_id, result))
    }

    fn acknowledge_foreground(&mut self, request_id: &str) -> Result<u64> {
        let (operation_id, _) = self.foreground_result(request_id)?;
        if self
            .journal
            .foreground_attempt
            .as_ref()
            .is_some_and(|attempt| {
                attempt.request_id == request_id && attempt.phase == ForegroundPhase::Definite
            })
        {
            if self.journal.pending.is_some()
                || self.journal.parent_hold.is_some()
                || self.journal.tool_pending.is_some()
                || self.journal.tool_hold.is_some()
                || self.journal.dispatch_pending.is_some()
                || self.journal.dispatch_hold.is_some()
                || self.journal.provider_pending.is_some()
                || self.journal.provider_hold.is_some()
                || self.journal.birth_pending.is_some()
                || self.journal.birth_operation.is_some()
                || self.journal.application_api_attempt.is_some()
                || self.journal.settlement_due.is_some()
            {
                return Err("definite foreground result still has unsettled authority".into());
            }
            if self.journal.foreground_history.len() >= 256 {
                let index = self
                    .journal
                    .foreground_history
                    .iter()
                    .position(|attempt| attempt.reported)
                    .ok_or("foreground history has 256 unacknowledged results")?;
                self.journal.foreground_history.remove(index);
            }
            let mut finished = self.journal.foreground_attempt.take().unwrap();
            finished.reported = true;
            self.journal.foreground_history.push(finished);
            return self.save().map(|()| operation_id);
        }
        let record = self
            .journal
            .foreground_history
            .iter_mut()
            .find(|record| record.request_id == request_id)
            .ok_or("foreground result has not been archived")?;
        if !record.reported {
            record.reported = true;
            self.save()?;
        }
        Ok(operation_id)
    }

    fn answer_foreground_result(&self, attachment_id: u64, request_id: &str) -> Result<()> {
        let response = self.foreground_result(request_id);
        if let Some(output) = &self.output {
            let event = match &response {
                Ok((id, result)) => json!({"v":1,"type":"tool-complete",
                    "operationId":id.to_string(),"requestId":request_id,
                    "isError":result.get("isError").and_then(Value::as_bool).unwrap_or(true),
                    "result":result}),
                Err(error) => json!({"v":1,"type":"tool-complete",
                    "requestId":request_id,"isError":true,"result":error}),
            };
            let _ = output.try_tool_event_for(attachment_id, event);
        }
        response.map(|_| ())
    }

    fn answer_foreground_ack(&mut self, attachment_id: u64, request_id: &str) -> Result<()> {
        let response = self.acknowledge_foreground(request_id);
        if let Some(output) = &self.output {
            let event = match &response {
                Ok(id) => json!({"v":1,"type":"tool-acknowledged",
                    "requestId":request_id,"operationId":id.to_string()}),
                Err(error) => json!({"v":1,"type":"tool-acknowledged",
                    "requestId":request_id,"isError":true,"result":error}),
            };
            let _ = output.try_tool_event_for(attachment_id, event);
        }
        response.map(|_| ())
    }

    fn reconcile_foreground_audited(&mut self) -> Result<()> {
        let attempt = self
            .journal
            .foreground_attempt
            .as_ref()
            .ok_or("no unresolved foreground operation")?
            .clone();
        if attempt.phase == ForegroundPhase::Definite {
            return Err("definite foreground result requires exact result inspection".into());
        }
        if self.journal.pending.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.birth_pending.is_some()
            || self.journal.birth_operation.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || self.journal.application_api_attempt.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.settlement_due.is_some()
            || !self.journal.unresolved_external.is_empty()
        {
            return Err(
                "foreground audit requires all native and external effects reconciled".into(),
            );
        }
        let parent = self.query()?;
        if !matches!(
            parent.pointer("/grain/status").and_then(Value::as_str),
            Some("0" | "1" | "2" | "6")
        ) || parent.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
        {
            return Err("foreground audit lacks signed idle parent".into());
        }
        let tool = self.query_as(&self.tool()?)?;
        if !matches!(
            tool.pointer("/grain/status").and_then(Value::as_str),
            Some("0" | "1" | "2" | "6")
        ) || tool.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
        {
            return Err("foreground audit lacks signed idle tool".into());
        }
        let attempt_id = attempt.operation_id;
        let request_sha256 = attempt.request_sha256.clone();
        let decision_id = self.next_id()?;
        self.journal.reconciliation_log.push(json!({
            "decisionId":decision_id.to_string(),
            "action":"foreground-audited-terminal",
            "operationId":attempt_id.to_string(),
            "requestSha256":request_sha256,
            "result":"no definitive foreground response claimed"
        }));
        let mut finished = self.journal.foreground_attempt.take().unwrap();
        finished.phase = ForegroundPhase::Audited;
        finished.reported = true;
        if self.journal.foreground_history.len() >= 256 {
            let Some(index) = self
                .journal
                .foreground_history
                .iter()
                .position(|prior| prior.reported)
            else {
                self.journal.foreground_attempt = Some(finished);
                return Err("foreground audit history has 256 unacknowledged results".into());
            };
            self.journal.foreground_history.remove(index);
        }
        self.journal.foreground_history.push(finished);
        self.save()
    }

    fn foreground_application_api(
        &mut self,
        arguments: &Value,
        input: &Receiver<Input>,
    ) -> Result<Value> {
        let (reply, received) = mpsc::channel();
        let mut active = Some(self.begin_application_api(arguments, reply, None, false)?);
        let deadline = Instant::now() + Duration::from_secs(1800);
        loop {
            self.poll_application_api(&mut active)?;
            if let Ok(value) = received.try_recv() {
                if value.get("isError").and_then(Value::as_bool) == Some(true)
                    && self.journal.application_api_attempt.is_some()
                {
                    return Err(
                        "application API outcome remains retained for read-only inspection".into(),
                    );
                }
                return Ok(value);
            }
            if self.cancelled.load(Ordering::SeqCst) || Instant::now() >= deadline {
                return Err(
                    "foreground API call cancelled or timed out; inspect exact attempt".into(),
                );
            }
            match input.try_recv() {
                Ok(Input::Dispatch(request)) => self.answer_dispatch(request),
                Ok(Input::Admin(request)) => {
                    let _ = request.reply.send("foreground API call is running".into());
                }
                Ok(Input::Disconnect) => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        return Err("hard disconnect during foreground API call".into());
                    }
                }
                Ok(Input::Line(line)) if line == "disconnect" => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        return Err("hard disconnect during foreground API call".into());
                    }
                }
                Ok(Input::SoftDetach) => self.stdin_gone = true,
                Ok(Input::Line(line))
                    if line == "attach soft" && self.journal.connection == Connection::Soft =>
                {
                    self.emit("reconnected to soft foreground tool\n");
                }
                Ok(Input::Line(line))
                    if line == "attach hard" && self.journal.connection == Connection::Soft =>
                {
                    self.note_hard_reconnect()?;
                }
                Ok(Input::ForegroundTool {
                    attachment_id,
                    frame,
                }) => {
                    if let Some(output) = &self.output {
                        let _ = output.try_tool_event_for(
                            attachment_id,
                            json!({"v":1,
                            "type":"tool-complete","isError":true,
                            "requestId":foreground_request_id(&frame),
                            "result":"foreground tool already in progress"}),
                        );
                    }
                }
                Ok(Input::ForegroundResult {
                    attachment_id,
                    request_id,
                }) => {
                    let _ = self.answer_foreground_result(attachment_id, &request_id);
                }
                Ok(Input::ForegroundAck {
                    attachment_id,
                    request_id,
                }) => {
                    let _ = self.answer_foreground_ack(attachment_id, &request_id);
                }
                Ok(_) | Err(mpsc::TryRecvError::Empty) => {}
                Err(mpsc::TryRecvError::Disconnected) => {
                    return Err("foreground connector channel closed".into());
                }
            }
            thread::sleep(Duration::from_millis(20));
        }
    }
    fn check_not_cancelled(&self) -> Result<()> {
        if self.cancelled.load(Ordering::SeqCst) {
            Err("hard connection closed; tool task requires reconciliation".into())
        } else {
            Ok(())
        }
    }
    fn finish_reconnected_mode(&mut self) -> Result<()> {
        if self.journal.connection == Connection::Soft
            && self.journal.hard_reconnect_pending
            && self.hard_connection.load(Ordering::SeqCst)
        {
            if self.cancelled.load(Ordering::SeqCst) {
                return self.disconnect();
            }
            self.transition(
                json!({"type":"mode","soft":false}),
                "mode",
                "hard connector reattached after soft reservation",
            )?;
            self.journal.connection = Connection::Hard;
            self.journal.hard_reconnect_pending = false;
            self.save()?;
            if self.cancelled.load(Ordering::SeqCst) {
                return self.disconnect();
            }
        }
        Ok(())
    }
    fn conversation_new(&mut self) -> Result<()> {
        if !matches!(self.journal.connection, Connection::Hard | Connection::Soft)
            || self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || self.journal.settlement_due.is_some()
            || !self.journal.unresolved_external.is_empty()
        {
            return Err(
                "conversation reset requires an attached, fully reconciled idle task".into(),
            );
        }
        if let Some(prior) = self.journal.hermes_session.take() {
            if self.journal.prior_hermes_sessions.len() >= 32 {
                self.journal.hermes_session = Some(prior);
                return Err("conversation history archive reached its 32-session bound".into());
            }
            self.journal.prior_hermes_sessions.push(prior);
            self.save()?;
            self.emit(
                "new conversation selected; prior Hermes session ID remains in the journal\n",
            );
        } else {
            self.emit("conversation is already new\n");
        }
        Ok(())
    }
    fn note_hard_reconnect(&mut self) -> Result<()> {
        self.journal.hard_reconnect_pending = true;
        self.save()?;
        self.hard_connection.store(true, Ordering::SeqCst);
        self.emit("hard transport attached to soft reservation; loss will interrupt the task\n");
        Ok(())
    }
    fn attach(&mut self, soft: bool) -> Result<()> {
        if self.journal.connection == Connection::Fenced
            || self.journal.child.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || !self.journal.unresolved_external.is_empty()
        {
            return Err("task is fenced or unresolved; cannot attach".into());
        }
        let prior = self.journal.connection.clone();
        let op = if prior == Connection::Soft {
            json!({"type":"mode","soft":soft})
        } else {
            json!({"type":"attach","soft":soft})
        };
        self.journal.connection = Connection::Fenced;
        self.save()?;
        self.renew_worker_policy(prior != Connection::Soft)?;
        self.transition(op, "attach", "controller attach")?;
        self.journal.connection = if soft {
            Connection::Soft
        } else {
            Connection::Hard
        };
        self.hard_connection.store(!soft, Ordering::SeqCst);
        self.cancelled.store(false, Ordering::SeqCst);
        self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
        self.save()?;
        self.emit(format!(
            "attached {} to Mini grain {}\n",
            if soft { "soft" } else { "hard" },
            self.config.task
        ));
        Ok(())
    }
    fn stop_and_reap_owned(&mut self) -> Result<std::process::ExitStatus> {
        let unit = self.journal.child.as_ref().and_then(|c| c.unit.clone());
        let child = self.child.as_ref().ok_or("no live owned child")?;
        let pgid = child.id() as i32;
        // The leader remains unreaped until group cleanup, so its PID cannot
        // be recycled while signals address the process group.
        if group_has_live_member(pgid)? {
            signal_group(pgid, libc::SIGTERM)?;
        }
        if let Some(unit) = &unit {
            let record = self
                .journal
                .child
                .as_ref()
                .ok_or("owned child record absent")?;
            if record.launch_gate_protocol.as_deref() != Some("mini-grain-launch-gate-v1") {
                return Err("scoped worker has no durable launch gate".into());
            }
            self.launch_gate(&record.program, unit, "fence")?;
            kill_unit(unit)?;
        }
        for _ in 0..10 {
            if !group_has_live_member(pgid)? {
                break;
            }
            thread::sleep(Duration::from_millis(50));
        }
        if group_has_live_member(pgid)? {
            signal_group(pgid, libc::SIGKILL)?;
        }
        if let Some(unit) = &unit {
            kill_unit(unit)?;
        }
        for _ in 0..20 {
            if !group_has_live_member(pgid)? {
                break;
            }
            thread::sleep(Duration::from_millis(50));
        }
        if group_has_live_member(pgid)? {
            return Err(format!(
                "process group {pgid} still has live members after SIGKILL"
            ));
        }
        if let Some(unit) = &unit {
            // A systemd-run client may have raced the first kill while it was
            // creating the transient unit. After the wrapper group stops,
            // repeat the kill and verify the service has no live workers.
            kill_unit(unit)?;
            for _ in 0..20 {
                if unit_inactive(unit)? {
                    break;
                }
                thread::sleep(Duration::from_millis(50));
                kill_unit(unit)?;
            }
            if !unit_inactive(unit)? {
                return Err(format!("worker unit {unit} remains active"));
            }
            let record = self
                .journal
                .child
                .as_ref()
                .ok_or("owned child record absent")?;
            prove_worker_unit_stopped(&self.config.task, record, unit)?;
        }
        let _signal_guard = self
            .signal_lock
            .lock()
            .map_err(|_| "signal lock poisoned")?;
        let status = self
            .child
            .as_mut()
            .ok_or("owned child disappeared")?
            .wait()
            .map_err(|e| format!("child wait: {e}"))?;
        self.child = None;
        self.current_pgid.store(0, Ordering::SeqCst);
        *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
        self.journal.child = None;
        self.save()?;
        Ok(status)
    }
    fn kill_child(&mut self) -> Result<()> {
        if self.child.is_none() {
            return Ok(());
        }
        self.stop_and_reap_owned().map(|_| ())
    }
    fn disconnect(&mut self) -> Result<()> {
        if self.journal.connection == Connection::Soft
            && !self.hard_connection.load(Ordering::SeqCst)
        {
            return Ok(());
        }
        self.cancelled.store(true, Ordering::SeqCst);
        self.revoke_provider_gateway();
        let _ = self.completion_phase.compare_exchange(
            PHASE_RUNNING,
            PHASE_CANCELLED,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        self.journal.connection = Connection::Fenced;
        self.hard_connection.store(false, Ordering::SeqCst);
        // Signal first on detection; neither filesystem sync nor Mini's
        // potentially slow replay may precede local physical interruption.
        let stopped = self.kill_child();
        self.application_api_send_gate.cancel();
        let custody_stopped = self
            .custody_gate
            .cancel()
            .map(|_| ())
            .map_err(|error| format!("Mini custody child stop: {error}"));
        self.save()?;
        // Exact retained lookups settle any lost reply before we decide if a
        // second transport event needs a new transition. A missing or refused
        // lookup remains unresolved; it is never a license to resubmit.
        let parent_retry = self.retry_pending(false);
        let tool_retry = self.retry_pending(true);
        let dispatch_retry = self.retry_pending_slot(AuthoritySlot::Dispatch);
        let provider_retry = self.retry_pending_slot(AuthoritySlot::Provider);
        let tool_fenced = tool_retry.and_then(|_| self.fence_tool());
        let dispatch_fenced = dispatch_retry.and_then(|_| match self.fence_dispatch()? {
            DispatchFenceOutcome::Released => Ok(()),
            DispatchFenceOutcome::HeldForAudit => {
                Err("dispatch reservation remains held for private audit".into())
            }
        });
        let provider_fenced = provider_retry.and_then(|_| self.fence_provider());
        let fenced = parent_retry.and_then(|_| {
            let parent_state = self.query()?;
            let parent_status = parent_state
                .pointer("/grain/status")
                .and_then(Value::as_str)
                .ok_or("hard disconnect signed grain status absent")?;
            if matches!(parent_status, "5" | "7") {
                let hold = self
                    .journal
                    .parent_hold
                    .as_ref()
                    .ok_or("signed fenced reservation has no durable parent hold")?;
                let before_generation = hold
                    .before_generation
                    .parse::<u64>()
                    .map_err(|_| "durable parent hold generation invalid")?;
                let expected_generation = before_generation
                    .checked_add(1)
                    .ok_or("durable parent hold generation overflow")?
                    .to_string();
                if parent_state
                    .pointer("/grain/reserved")
                    .and_then(Value::as_str)
                    != Some(hold.reserve.as_str())
                    || parent_state
                        .pointer("/grain/generation")
                        .and_then(Value::as_str)
                        != Some(expected_generation.as_str())
                {
                    Err("signed fenced reservation differs from durable parent hold origin".into())
                } else {
                    Ok(())
                }
            } else if matches!(parent_status, "0" | "6")
                && self.journal.parent_hold.is_none()
                && self.journal.settlement_due.is_none()
            {
                // Completion can win the atomic phase race immediately before
                // EOF. With no live allowance, the signed terminal state is
                // already the fence; a second disconnect edge is invalid.
                Ok(())
            } else {
                self.transition(
                    json!({"type":"interrupt"}),
                    "interrupt",
                    "hard connection lost",
                )
            }
        });
        match (stopped.and(custody_stopped), fenced, tool_fenced, dispatch_fenced, provider_fenced) {
            (Ok(()), Ok(()), Ok(()), Ok(()), Ok(())) => {
                self.journal.connection = Connection::Detached;
                self.journal.hard_reconnect_pending = false;
                self.journal.prompt_witness = None;
                self.save()
            }
            (a, b, c, d, e) => Err(format!(
                "hard disconnect unresolved: local stop={a:?}; Mini fence={b:?}; tool fence={c:?}; dispatch fence={d:?}; provider fence={e:?}"
            )),
        }
    }
    fn fence_dispatch(&mut self) -> Result<DispatchFenceOutcome> {
        if self.config.dispatch_task.is_none() {
            return Ok(DispatchFenceOutcome::Released);
        }
        let authority = self.dispatch()?;
        let state = self.query_as(&authority)?;
        let status = state
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("dispatch grain status absent")?;
        if matches!(status, "1" | "3") {
            self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "dispatch disconnect",
                "parent hard connection lost",
                vec![],
            )?;
        } else if !matches!(status, "0" | "5" | "6" | "7") {
            return Err(format!("unexpected dispatch status {status}"));
        }
        let after = self.query_as(&authority)?;
        match after.pointer("/grain/status").and_then(Value::as_str) {
            Some("0" | "6") => Ok(DispatchFenceOutcome::Released),
            Some("5" | "7") => {
                let hold = self
                    .journal
                    .dispatch_hold
                    .as_ref()
                    .filter(|hold| hold.reserve_confirmed && hold.reserve_anchor.is_some())
                    .ok_or("fenced dispatch reservation lacks confirmed native hold")?;
                let before = hold
                    .before_generation
                    .parse::<u64>()
                    .map_err(|_| "dispatch hold generation invalid")?;
                let expected = before
                    .checked_add(1)
                    .ok_or("dispatch fence generation overflow")?
                    .to_string();
                if after.pointer("/grain/generation").and_then(Value::as_str)
                    != Some(expected.as_str())
                    || after.pointer("/grain/reserved").and_then(Value::as_str)
                        != Some(hold.reserve.as_str())
                {
                    return Err("fenced dispatch state differs from confirmed hold".into());
                }
                let note = "dispatch reservation fenced; app send/response needs exact audit";
                if !self
                    .journal
                    .unresolved_external
                    .iter()
                    .any(|entry| entry == note)
                {
                    self.journal.unresolved_external.push(note.into());
                    self.save()?;
                }
                Ok(DispatchFenceOutcome::HeldForAudit)
            }
            other => Err(format!("unexpected dispatch status after fence {other:?}")),
        }
    }
    fn fence_provider(&mut self) -> Result<()> {
        if self.config.provider_task.is_none() {
            return Ok(());
        }
        let authority = self.provider()?;
        let state = self.query_as(&authority)?;
        let status = state
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("provider grain status absent")?;
        if matches!(status, "1" | "3") {
            self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "provider disconnect",
                "parent hard connection lost",
                vec![],
            )?;
        } else if !matches!(status, "0" | "5" | "6" | "7") {
            return Err(format!("unexpected provider status {status}"));
        }
        let after = self.query_as(&authority)?;
        match after.pointer("/grain/status").and_then(Value::as_str) {
            Some("0" | "6") => Ok(()),
            Some("5" | "7") => {
                let note =
                    "provider reservation fenced; external send/response requires exact audit";
                if !self
                    .journal
                    .unresolved_external
                    .iter()
                    .any(|entry| entry == note)
                {
                    self.journal.unresolved_external.push(note.into());
                    self.save()?;
                }
                Err("provider reservation remains held after fence".into())
            }
            other => Err(format!("unexpected provider status after fence {other:?}")),
        }
    }
    fn fence_tool(&mut self) -> Result<()> {
        if self.config.tool_task.is_none() {
            return Ok(());
        }
        let authority = self.tool()?;
        let state = self.query_as(&authority)?;
        let status = state
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("tool grain status absent")?;
        if matches!(status, "1" | "3") {
            self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "tool disconnect",
                "parent hard connection lost",
                vec![],
            )?;
        } else if !matches!(status, "0" | "5" | "6" | "7") {
            return Err(format!("unexpected tool status {status}"));
        }
        let after = self.query_as(&authority)?;
        if self.journal.workspace_attempt.is_some() || self.journal.workspace_birth.is_some() {
            return Err("workspace submission remains retained for exact recovery".into());
        }
        match after.pointer("/grain/status").and_then(Value::as_str) {
            Some("5" | "7") => {
                self.journal.unresolved_external.push(
                    "delegated tool reservation fenced with uncertain external effects".into(),
                );
                self.save()?;
                Err("tool reservation remains unresolved after fence".into())
            }
            Some("0" | "6") => Ok(()),
            Some("2" | "4") => {
                Err("tool task unexpectedly soft; operator reconciliation required".into())
            }
            other => Err(format!("unexpected tool status after fence {other:?}")),
        }
    }
    fn run(&mut self, name: &str, input: &Receiver<Input>) -> Result<()> {
        if !matches!(self.journal.connection, Connection::Hard | Connection::Soft) {
            return Err("attach before running a command".into());
        }
        if self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.workspace_attempt.is_some()
            || self.journal.workspace_birth.is_some()
            || self.journal.child.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err("task has unresolved work".into());
        }
        let spec = self
            .config
            .commands
            .iter()
            .find(|c| c.name == name)
            .ok_or_else(|| format!("command {name} is not configured"))?
            .clone();
        if spec.systemd_scope {
            prove_controller_unit(&self.config.task)?;
            Self::prove_launcher_gate(&spec.program)?;
        }
        self.mark_hold(false, &spec.reserve, &spec.charge)?;
        self.transition(
            json!({"type":"reserve","amount":spec.reserve}),
            "reserve",
            &format!("command:{name}"),
        )?;
        if self.journal.connection == Connection::Hard {
            match input.try_recv() {
                Ok(Input::Disconnect) => {
                    self.stdin_gone = true;
                    return self.disconnect();
                }
                Ok(Input::Line(line)) if line == "disconnect" => {
                    self.stdin_gone = true;
                    return self.disconnect();
                }
                Err(mpsc::TryRecvError::Disconnected) => {
                    self.stdin_gone = true;
                    return self.disconnect();
                }
                Ok(Input::Admin(request)) => {
                    let _ = request.reply.send("worker reservation in progress".into());
                }
                Ok(Input::Dispatch(request)) => {
                    let _ = request.reply.send(json!({"type":"refused",
                        "detail":"worker reservation in progress"}));
                }
                _ => {}
            }
        }
        let id = self.next_id()?;
        let unit = self.worker_unit(id, &spec);
        if let Some(unit) = &unit {
            Self::prove_launcher_gate(&spec.program)?;
            self.launch_gate(&spec.program, unit, "init")?;
        }
        let mut command = Command::new(&spec.program);
        command
            .args(&spec.args)
            .current_dir(&self.config.cwd)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        self.worker_env(&mut command, &spec, &unit, None);
        unsafe {
            command.pre_exec(|| {
                if libc::setsid() < 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(())
                }
            });
        }
        // The marker is durable before spawn. A crash between spawn and PID
        // publication leaves a blocked task, never an apparently idle one.
        self.journal.child = Some(ChildRecord {
            operation_id: id,
            pid: 0,
            program: spec.program.clone(),
            pgid: 0,
            unit: unit.clone(),
            launch_gate_protocol: unit.as_ref().map(|_| "mini-grain-launch-gate-v1".into()),
        });
        self.save()?;
        self.completion_phase.store(PHASE_RUNNING, Ordering::SeqCst);
        *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = unit
            .as_ref()
            .map(|unit| (unit.clone(), spec.program.clone()));
        let signal_lock = self.signal_lock.clone();
        let spawn_guard = signal_lock.lock().map_err(|_| "signal lock poisoned")?;
        if self.cancelled.load(Ordering::SeqCst) {
            drop(spawn_guard);
            *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
            if let Some(unit) = &unit {
                self.launch_gate(&spec.program, unit, "fence")?;
            }
            self.journal.child = None;
            self.save()?;
            self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
            return self.disconnect();
        }
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(e) => {
                drop(spawn_guard);
                *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
                if let Some(unit) = &unit {
                    self.launch_gate(&spec.program, unit, "fence")?;
                }
                self.journal.child = None;
                self.save()?;
                self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
                self.transition(
                    json!({"type":"settle","charge":"0"}),
                    "settle",
                    &format!("command:{name}:spawn-failed"),
                )?;
                return Err(format!("spawn {}: {e}", spec.program.display()));
            }
        };
        let pid = child.id();
        self.current_pgid.store(pid as i32, Ordering::SeqCst);
        drop(spawn_guard);
        if let Some(output) = self.output.clone() {
            if let Some(stdout) = child.stdout.take() {
                forward_display(stdout, output.clone());
            }
            if let Some(stderr) = child.stderr.take() {
                forward_display(stderr, output);
            }
        }
        self.child = Some(child);
        self.journal.child = Some(ChildRecord {
            operation_id: id,
            pid,
            program: spec.program,
            pgid: pid as i32,
            launch_gate_protocol: unit.as_ref().map(|_| "mini-grain-launch-gate-v1".into()),
            unit,
        });
        if let Err(e) = self.save() {
            let _ = self.kill_child();
            return Err(e);
        }
        loop {
            if self.cancelled.load(Ordering::SeqCst) && self.hard_connection.load(Ordering::SeqCst)
            {
                return self.disconnect();
            }
            if child_exited_unreaped(self.child.as_ref().unwrap())? {
                let status = self.stop_and_reap_owned()?;
                if !self.claim_completion(&spec.charge)? {
                    return self.disconnect();
                }
                self.transition(
                    json!({"type":"settle","charge":spec.charge}),
                    "settle",
                    &format!("command:{name}:exit:{status}"),
                )?;
                self.journal.settlement_due = None;
                self.save()?;
                self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
                self.finish_reconnected_mode()?;
                self.emit(format!("command {name} exited {status}\n"));
                return Ok(());
            }
            match input.try_recv() {
                Ok(Input::Disconnect) => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        return self.disconnect();
                    }
                }
                Ok(Input::Line(line)) if line == "disconnect" => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        return self.disconnect();
                    }
                }
                Ok(Input::Line(line))
                    if line == "attach soft" && self.journal.connection == Connection::Soft =>
                {
                    self.emit("reconnected to soft task\n");
                }
                Ok(Input::Line(line))
                    if line == "attach hard" && self.journal.connection == Connection::Soft =>
                {
                    self.note_hard_reconnect()?;
                }
                Ok(Input::Line(_) | Input::TerminalLine { .. }) => {
                    eprintln!("command running; only disconnect is accepted")
                }
                Ok(Input::ForegroundTool {
                    attachment_id,
                    frame,
                }) => {
                    if let Some(output) = &self.output {
                        let _ = output.try_tool_event_for(
                            attachment_id,
                            json!({"v":1,
                            "type":"tool-complete","isError":true,
                            "requestId":foreground_request_id(&frame),
                            "result":"worker is running"}),
                        );
                    }
                }
                Ok(Input::ForegroundResult {
                    attachment_id,
                    request_id,
                }) => {
                    let _ = self.answer_foreground_result(attachment_id, &request_id);
                }
                Ok(Input::ForegroundAck {
                    attachment_id,
                    request_id,
                }) => {
                    let _ = self.answer_foreground_ack(attachment_id, &request_id);
                }
                Ok(Input::Admin(request)) => {
                    let _ = request
                        .reply
                        .send("worker is running; stop and fence it first".into());
                }
                Ok(Input::Dispatch(request)) => {
                    let _ = request.reply.send(json!({"type":"refused",
                        "detail":"agent dispatch requires an active Hermes prompt"}));
                }
                Ok(Input::SoftDetach) => {
                    self.stdin_gone = true;
                }
                Err(mpsc::TryRecvError::Disconnected) => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        return self.disconnect();
                    }
                }
                Err(mpsc::TryRecvError::Empty) => {}
            }
            thread::sleep(Duration::from_millis(20));
        }
    }
    /// Prepare bounded tool-discovery names from exact retained Mini births.
    /// The catalog never substitutes for admission on a later tool call.
    fn tool_catalog(&self) -> Result<mcp::ToolCatalog> {
        let Some(tool) = self.config.tool_task.as_ref() else {
            return Ok(mcp::ToolCatalog::default());
        };
        if !tool.allowed_application_families.is_empty()
            || !tool.allowed_session_families.is_empty()
        {
            let expected = tool
                .current_birth_host_sha256
                .as_deref()
                .ok_or("current application birth Host pin absent")?;
            if self.config.host_socket.is_none() || sha256_file(&self.config.host)? != expected {
                return Err(
                    "current application birth Host image or socket differs from operator pin"
                        .into(),
                );
            }
        }
        let mut applications = Vec::new();
        if !tool.allowed_session_families.is_empty() {
            let mut seen = std::collections::HashSet::new();
            // A bounded discovery hint, never a use grant. Later tool calls
            // still require the exact birth receipt and fresh signed read.
            for record in self.journal.born_resources.iter().rev() {
                if record.pending.route == Some(ApplicationBirthRoute::Application)
                    && tool
                        .allowed_session_families
                        .iter()
                        .any(|family| family.application_family == record.pending.family)
                {
                    self.verify_born_record(record)?;
                    if !seen.insert(record.pending.born.name.clone()) {
                        return Err("duplicate confirmed application name".into());
                    }
                    if applications.len() >= 64 {
                        return Err("application catalog exceeds 64 names".into());
                    }
                    applications.push(record.pending.born.name.clone());
                }
            }
            applications.reverse();
            for name in shared_app_refs::discovery_names(&tool.registered_shared_applications) {
                if !seen.insert(name.clone()) {
                    return Err("registered shared application duplicates a local name".into());
                }
                if applications.len() >= 64 {
                    return Err("application catalog exceeds 64 names".into());
                }
                applications.push(name);
            }
        }
        Ok(mcp::ToolCatalog {
            birth_families: tool
                .allowed_birth_families
                .iter()
                .map(|family| family.name.clone())
                .collect(),
            application_families: tool
                .allowed_application_families
                .iter()
                .map(|family| family.name.clone())
                .collect(),
            session_families: tool
                .allowed_session_families
                .iter()
                .map(|family| family.name.clone())
                .collect(),
            applications,
            api_applications: if tool.agent_api_host_sha256.is_some() {
                tool.allowed_application_api_routes
                    .iter()
                    .map(|route| route.name.clone())
                    .chain(
                        tool.allowed_application_lifetime_routes
                            .iter()
                            .filter(|_| tool.lifetime_api_host_sha256.is_some())
                            .map(|route| route.name.clone()),
                    )
                    .collect()
            } else if tool.lifetime_api_host_sha256.is_some() {
                tool.allowed_application_lifetime_routes
                    .iter()
                    .map(|route| route.name.clone())
                    .collect()
            } else {
                Vec::new()
            },
            resource_workspace: tool.resource_workspace.is_some(),
            resource_workspace_create: if let Some(root) = &tool.resource_workspace {
                let workspace: Value = serde_json::from_slice(&bounded_regular_file(
                    &root.join("workspace.json"),
                    65_536,
                )?)
                .map_err(|e| format!("workspace catalog config: {e}"))?;
                workspace["birthContext"].as_str().is_some()
                    && workspace["namespaceRoot"].as_str().is_some()
            } else {
                false
            },
        })
    }

    /// Drive the real upstream `hermes-acp` through an operator-selected OS
    /// confinement wrapper. ACP permission requests are refused; built-in
    /// tools are still present upstream, so OS confinement is mandatory.
    /// The wrapper's fixed args must launch hermes-acp inside its sandbox.
    fn hermes(&mut self, prompt: &str, input: &Receiver<Input>) -> Result<()> {
        if prompt.is_empty() || prompt.len() > 16_384 {
            return Err("prompt length is outside profile".into());
        }
        if !matches!(self.journal.connection, Connection::Hard | Connection::Soft) {
            return Err("attach before running Hermes".into());
        }
        if self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.workspace_attempt.is_some()
            || self.journal.workspace_birth.is_some()
            || self.journal.child.is_some()
            || self.journal.foreground_attempt.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err("task has unresolved work".into());
        }
        let spec = self
            .config
            .commands
            .iter()
            .find(|c| c.name == "hermes-acp")
            .ok_or("no hermes-acp command configured")?
            .clone();
        let wrapper = spec
            .program
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("");
        if wrapper != "sandbox-exec" && wrapper != "bwrap" {
            return Err("Hermes requires an OS confinement wrapper (sandbox-exec or bwrap)".into());
        }
        if !spec.args.iter().any(|s| s.ends_with("hermes-acp")) {
            return Err("Hermes wrapper must launch the upstream hermes-acp executable".into());
        }
        let worker_workspace = if spec.systemd_scope {
            let index = spec
                .args
                .iter()
                .position(|argument| argument == "--workspace")
                .ok_or("scoped Hermes command has no fixed --workspace")?;
            let path = spec
                .args
                .get(index + 1)
                .ok_or("scoped Hermes command has no workspace path")?;
            let path = PathBuf::from(path);
            if !path.is_absolute() {
                return Err("scoped Hermes workspace must be absolute".into());
            }
            path
        } else {
            self.config.cwd.clone()
        };
        let (workspace, hermes_home) = hermes_workspace_home(&worker_workspace)?;
        if let Some(mut session) = self.journal.hermes_session.clone() {
            if session.workspace != workspace {
                // Older scoped controllers fingerprinted config.cwd even
                // though bwrap mounted its fixed --workspace elsewhere. This
                // exact old failure may be repaired only by finding a private
                // DB in the now-correct mount; session/load must still prove
                // the retained ID before a prompt is sent.
                let old_controller_workspace = fs::canonicalize(&self.config.cwd)
                    .map_err(|e| format!("old controller workspace: {e}"))?;
                if !spec.systemd_scope
                    || session.workspace != old_controller_workspace
                    || session.retention_issue.as_deref()
                        != Some("upstream did not create state.db after the prompt")
                    || session.state_fingerprint.is_some()
                {
                    return Err("saved Hermes session belongs to another workspace".into());
                }
                let fingerprint = hermes_state_fingerprint(&hermes_home)?
                    .ok_or("fixed scoped workspace has no retained Hermes state.db")?;
                session.workspace = workspace.clone();
                session.state_fingerprint = Some(fingerprint);
                session.retention_issue = None;
                self.journal.hermes_session = Some(session.clone());
                self.save()?;
                self.emit("corrected prior scoped-workspace journal path; exact Hermes session/load is required before prompting\n");
            }
            let current = hermes_state_fingerprint(&hermes_home)?;
            if session.pending_prompt {
                if current == session.state_fingerprint {
                    self.emit("Hermes interrupted turn made no observed transcript-store change; its last prompt may be absent\n");
                } else {
                    self.emit("Hermes interrupted turn changed the transcript store; reloading its exact session ID after Mini reconciliation\n");
                }
                if let Some(fingerprint) = current {
                    if let Some(saved) = self.journal.hermes_session.as_mut() {
                        saved.state_fingerprint = Some(fingerprint);
                        saved.retention_issue = None;
                    }
                    self.save()?;
                } else {
                    if let Some(saved) = self.journal.hermes_session.as_mut() {
                        saved.retention_issue =
                            Some("interrupted prompt left no Hermes state.db".into());
                    }
                    self.save()?;
                    return Err("interrupted Hermes prompt has no retained state; use `conversation new` explicitly".into());
                }
            } else {
                if let Some(issue) = &session.retention_issue {
                    return Err(format!("Hermes conversation not retained: {issue}; use `conversation new` to start explicitly"));
                }
                if current != session.state_fingerprint {
                    return Err("Hermes transcript store changed between prompts; use `conversation new` after review".into());
                }
            }
        }
        // Provider credentials stay in controller memory and its private
        // stateDir. Hermes receives only a fresh one-prompt gateway token.
        // This setup runs before any Mini reservation, so a profile failure
        // cannot strand a paid allowance.
        let provider_runtime = if let Some(task) = self.config.provider_task.clone() {
            let key =
                provider_profile::private_key(&task.provider_key_file, &self.config.state_dir)?;
            let bind = task
                .gateway_bind
                .parse()
                .map_err(|_| "invalid gateway bind")?;
            let (tx, rx) = mpsc::sync_channel(8);
            let endpoint = provider::GatewayEndpoint::start(
                provider::GatewayConfig {
                    bind,
                    unix_socket: (!task.local_fixture_host_network)
                        .then(|| self.config.state_dir.join("provider-gateway.sock")),
                    upstream_url: task.upstream_url.clone(),
                    pinned_model: task.model.clone(),
                    provider_key: key,
                    private_dir: self.config.state_dir.clone(),
                    max_request_bytes: task.max_request_bytes,
                    max_response_bytes: task.max_response_bytes,
                    max_input_tokens: task.max_input_tokens,
                    max_output_tokens: task.max_output_tokens,
                    timeout: Duration::from_secs(task.timeout_seconds),
                },
                tx,
            )?;
            let token = provider_profile::random_token()?;
            provider_profile::install_worker_profile(
                &hermes_home,
                &task.model,
                endpoint.local_addr(),
                &token,
                spec.wall_time_seconds.unwrap_or(600) - 60,
                provider_max_iterations(task.max_iterations)?,
                task.max_input_tokens,
            )?;
            *self
                .provider_control
                .lock()
                .map_err(|_| "provider control lock poisoned")? = Some(endpoint.control());
            Some(ActiveProvider {
                endpoint,
                requests: rx,
                token,
                control_slot: self.provider_control.clone(),
            })
        } else {
            None
        };
        if spec.systemd_scope {
            // This is the host path bwrap mounts as /workspace/.hermes. The
            // upstream ACP adapter drops MCP timeout fields supplied in
            // session/new, so validate the actual worker config before Mini
            // reserves any prompt allowance.
            provider_profile::require_worker_mcp_timeout(
                &hermes_home,
                spec.wall_time_seconds.unwrap_or(600),
            )?;
        }
        let acp_cwd = if spec.systemd_scope {
            PathBuf::from("/workspace")
        } else {
            workspace.clone()
        };
        if spec.systemd_scope {
            prove_controller_unit(&self.config.task)?;
            Self::prove_launcher_gate(&spec.program)?;
        }
        self.reserve_parent_work_lease(&spec.reserve, &spec.charge, "hermes-acp prompt")?;
        if self.journal.connection == Connection::Hard {
            match input.try_recv() {
                Ok(Input::Disconnect) => {
                    self.stdin_gone = true;
                    return self.disconnect();
                }
                Ok(Input::Line(line)) if line == "disconnect" => {
                    self.stdin_gone = true;
                    return self.disconnect();
                }
                Err(mpsc::TryRecvError::Disconnected) => {
                    self.stdin_gone = true;
                    return self.disconnect();
                }
                Ok(Input::Admin(request)) => {
                    let _ = request.reply.send("Hermes reservation in progress".into());
                }
                Ok(Input::Dispatch(request)) => {
                    let _ = request.reply.send(json!({"type":"refused",
                        "detail":"Hermes reservation in progress"}));
                }
                _ => {}
            }
        }
        let id = self.next_id()?;
        if !self.journal.provider_replays.is_empty() {
            // A new explicit prompt rotates the gateway token and its replay
            // scope. Prior exact artifacts remain on disk for audit.
            self.journal.provider_replays.clear();
            self.save()?;
        }
        let unit = self.worker_unit(id, &spec);
        if let Some(unit) = &unit {
            Self::prove_launcher_gate(&spec.program)?;
            self.launch_gate(&spec.program, unit, "init")?;
        }
        let broker_path = self.config.state_dir.join(format!("mcp-{id:016}.sock"));
        let catalog = self.tool_catalog()?;
        let broker = mcp::start_broker(
            &broker_path,
            Duration::from_secs(spec.wall_time_seconds.unwrap_or(600)),
            catalog,
        )?;
        let broker_program = if spec.systemd_scope {
            PathBuf::from("/agent/grain-runtime")
        } else {
            std::env::current_exe().map_err(|e| e.to_string())?
        };
        let broker_socket = if spec.systemd_scope {
            PathBuf::from("/run/mini-grain.sock")
        } else {
            broker_path.clone()
        };
        let mut command = Command::new(&spec.program);
        command
            .args(&spec.args)
            .current_dir(&self.config.cwd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        if !spec.systemd_scope {
            command.env("HERMES_HOME", &hermes_home);
        }
        self.worker_env(&mut command, &spec, &unit, Some(&broker_path));
        unsafe {
            command.pre_exec(|| {
                libc::umask(0o077);
                if libc::setsid() < 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(())
                }
            });
        }
        self.journal.child = Some(ChildRecord {
            operation_id: id,
            pid: 0,
            program: spec.program.clone(),
            pgid: 0,
            unit: unit.clone(),
            launch_gate_protocol: unit.as_ref().map(|_| "mini-grain-launch-gate-v1".into()),
        });
        self.save()?;
        self.completion_phase.store(PHASE_RUNNING, Ordering::SeqCst);
        *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = unit
            .as_ref()
            .map(|unit| (unit.clone(), spec.program.clone()));
        let signal_lock = self.signal_lock.clone();
        let spawn_guard = signal_lock.lock().map_err(|_| "signal lock poisoned")?;
        if self.cancelled.load(Ordering::SeqCst) {
            drop(spawn_guard);
            *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
            if let Some(unit) = &unit {
                self.launch_gate(&spec.program, unit, "fence")?;
            }
            self.journal.child = None;
            self.save()?;
            self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
            return self.disconnect();
        }
        let worker_deadline =
            Instant::now() + Duration::from_secs(spec.wall_time_seconds.unwrap_or(600));
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(e) => {
                drop(spawn_guard);
                *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
                if let Some(unit) = &unit {
                    self.launch_gate(&spec.program, unit, "fence")?;
                }
                self.journal.child = None;
                self.save()?;
                self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
                self.transition(
                    json!({"type":"settle","charge":"0"}),
                    "settle",
                    "hermes spawn failed",
                )?;
                return Err(format!("Hermes spawn: {e}"));
            }
        };
        let pid = child.id();
        self.current_pgid.store(pid as i32, Ordering::SeqCst);
        drop(spawn_guard);
        let mut child_stdin = child.stdin.take().ok_or("Hermes stdin absent")?;
        let child_stdout = child.stdout.take().ok_or("Hermes stdout absent")?;
        self.child = Some(child);
        self.journal.child = Some(ChildRecord {
            operation_id: id,
            pid,
            program: spec.program,
            pgid: pid as i32,
            launch_gate_protocol: unit.as_ref().map(|_| "mini-grain-launch-gate-v1".into()),
            unit,
        });
        if let Err(e) = self.save() {
            let _ = self.kill_child();
            return Err(e);
        }
        let (tx, rx) = mpsc::sync_channel::<Result<Value>>(8);
        thread::spawn(move || {
            let mut reader = io::BufReader::new(child_stdout);
            loop {
                match read_acp_frame(&mut reader) {
                    Ok(Some(frame)) => {
                        let msg =
                            serde_json::from_slice::<Value>(&frame).map_err(|e| e.to_string());
                        if tx.send(msg).is_err() {
                            return;
                        }
                    }
                    Ok(None) => return,
                    Err(error) => {
                        let _ = tx.send(Err(format!("ACP frame refused: {error}")));
                        return;
                    }
                }
            }
        });
        // A slow SSH reader must not block the controller while Hermes is
        // running. The bounded channel drops display deltas under backpressure;
        // it never drops native decisions or the retained ACP session.
        let (display_tx, display_rx) = mpsc::sync_channel::<String>(128);
        let display_output = self.output.clone();
        thread::spawn(move || {
            for chunk in display_rx {
                if let Some(output) = &display_output {
                    let _ = output.try_output(chunk);
                }
            }
        });
        let existing_session = self.journal.hermes_session.clone();
        let session = (|| -> Result<String> {
            acp_send(
                &mut child_stdin,
                1,
                "initialize",
                json!({
                    "protocolVersion":1,
                    "clientCapabilities":{"fs":{"readTextFile":false,"writeTextFile":false}},
                    "clientInfo":{"name":"minidregg-grain-runtime","version":"0.1.0"}
                }),
            )?;
            self.acp_response(1, &rx, input, &mut child_stdin, &display_tx, &broker, None)?;
            let method = if existing_session.is_some() {
                "session/load"
            } else {
                "session/new"
            };
            let mut params = json!({
                "cwd":acp_cwd,"mcpServers":[{"name":"mini-grain",
                    "command":broker_program,"args":["mcp-stdio",broker_socket],"env":[]}]
            });
            if let Some(previous) = &existing_session {
                params["sessionId"] = Value::String(previous.id.clone());
            }
            acp_send(&mut child_stdin, 2, method, params)?;
            let response =
                self.acp_response(2, &rx, input, &mut child_stdin, &display_tx, &broker, None)?;
            if let Some(previous) = &existing_session {
                if !response.is_object() {
                    return Err("Hermes did not reload the retained session".into());
                }
                if let Some(current) = self.journal.hermes_session.as_mut() {
                    current.load_verified = true;
                    current.retention_issue = None;
                }
                self.save()?;
                if previous.pending_prompt {
                    self.emit("Hermes session reloaded; the interrupted last turn may be partial, so inspect its history before repeating effects\n");
                }
                Ok(previous.id.clone())
            } else {
                let session_id = response
                    .get("sessionId")
                    .or_else(|| response.get("session_id"))
                    .and_then(Value::as_str)
                    .ok_or("Hermes omitted session ID")?;
                if session_id.is_empty()
                    || session_id.len() > 256
                    || session_id.chars().any(char::is_control)
                {
                    return Err("Hermes returned an invalid session ID".into());
                }
                self.journal.hermes_session = Some(HermesSession {
                    id: session_id.to_owned(),
                    workspace: workspace.clone(),
                    load_verified: false,
                    state_fingerprint: None,
                    retention_issue: Some("first prompt has not yet been retained".into()),
                    pending_prompt: false,
                });
                self.save()?;
                Ok(session_id.to_owned())
            }
        })();
        let mut reported_publications = Vec::new();
        let outcome = match &session {
            Ok(session_id) => {
                self.prompt_active = true;
                let prompt_sent = (|| -> Result<()> {
                    let (receipt_report, receipt_ids) =
                        self.verified_publication_report(session_id)?;
                    reported_publications = receipt_ids;
                    let prompt_text = if receipt_report.is_empty() {
                        prompt.to_owned()
                    } else {
                        format!("{prompt}\n\n{receipt_report}")
                    };
                    if let Some(current) = self.journal.hermes_session.as_mut() {
                        current.pending_prompt = true;
                    }
                    self.save()?;
                    if let Some(active) = provider_runtime.as_ref() {
                        let parent_generation = self
                            .journal
                            .prompt_witness
                            .as_ref()
                            .and_then(|witness| witness.pointer("/before/generation"))
                            .and_then(Value::as_str)
                            .ok_or("provider parent witness generation absent")?;
                        let lease_id = provider::LeaseId {
                            prompt_operation_id: id,
                            parent_generation: parent_generation.to_owned(),
                        };
                        active.endpoint.control().activate(
                            provider::Lease {
                                id: lease_id.clone(),
                                worker_token: active.token.clone(),
                            },
                            worker_deadline,
                        )?;
                        self.provider_lease = Some(lease_id);
                    }
                    broker.activate_prompt();
                    acp_send(
                        &mut child_stdin,
                        3,
                        "session/prompt",
                        json!({
                            "sessionId":session_id,"prompt":[{"type":"text","text":prompt_text}]
                        }),
                    )
                })();
                prompt_sent.and_then(|_| {
                    self.acp_response(
                        3,
                        &rx,
                        input,
                        &mut child_stdin,
                        &display_tx,
                        &broker,
                        provider_runtime.as_ref(),
                    )
                })
            }
            Err(e) => Err(e.clone()),
        };
        self.prompt_active = false;
        broker.deactivate_prompt();
        let provider_drained = if let Some(active) = provider_runtime.as_ref() {
            self.drain_provider_after_prompt(active)
        } else {
            Ok(())
        };
        self.revoke_provider_gateway();
        let outcome = match (outcome, provider_drained) {
            (Ok(value), Ok(())) => Ok(value),
            (Err(error), Ok(())) | (Ok(_), Err(error)) => Err(error),
            (Err(acp), Err(provider)) => {
                Err(format!("ACP outcome: {acp}; provider drain: {provider}"))
            }
        };
        if self.cancelled.load(Ordering::SeqCst) && self.hard_connection.load(Ordering::SeqCst) {
            self.disconnect()?;
            return Err("hard disconnect while Hermes was running".into());
        }
        if self.journal.connection == Connection::Fenced {
            return outcome.map(|_| ());
        }
        if let Err(error) = &session {
            drop(child_stdin);
            let exit = self.stop_and_reap_owned()?;
            if !self.claim_completion("0")? {
                self.disconnect()?;
                return Err("hard disconnect before Hermes setup settlement".into());
            }
            if existing_session.is_some() {
                if let Some(current) = self.journal.hermes_session.as_mut() {
                    current.retention_issue = Some(format!("session/load failed: {error}"));
                }
                self.save()?;
            }
            self.transition(
                json!({"type":"settle","charge":"0"}),
                "settle",
                &format!("hermes-acp setup failed exit:{exit}"),
            )?;
            self.journal.settlement_due = None;
            self.journal.prompt_witness = None;
            self.save()?;
            self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
            self.finish_reconnected_mode()?;
            return Err(format!("Hermes setup failed before prompt: {error}"));
        }
        if let Err(error) = &outcome {
            let stopped = self.stop_and_reap_owned();
            self.journal
                .unresolved_external
                .push(format!("Hermes prompt {id}: {error}"));
            self.save()?;
            // An ACP fault ends even a soft prompt; this is a controller
            // failure, not a voluntary soft transport detach.
            self.hard_connection.store(true, Ordering::SeqCst);
            let fence = self.disconnect();
            return Err(format!("Hermes ACP outcome uncertain: {error}; local stop={stopped:?}; Mini/tool/provider fence={fence:?}"));
        }
        // The ACP server has finished the prompt. Close stdin and reap its
        // process. Provider usage may still be uncertain; charge is explicitly
        // the configured budget unit, not an attested invoice.
        drop(child_stdin);
        let exit = self.stop_and_reap_owned()?;
        if !self.claim_completion(&spec.charge)? {
            self.disconnect()?;
            return Err("hard disconnect before Hermes settlement".into());
        }
        self.transition(
            json!({"type":"settle","charge":spec.charge}),
            "settle",
            &format!("hermes-acp exit:{exit}"),
        )?;
        self.journal.settlement_due = None;
        self.journal.prompt_witness = None;
        self.save()?;
        self.completion_phase.store(PHASE_IDLE, Ordering::SeqCst);
        self.finish_reconnected_mode()?;
        let retention = hermes_state_fingerprint(&hermes_home);
        if let Some(current) = self.journal.hermes_session.as_mut() {
            current.pending_prompt = false;
            match &retention {
                Ok(Some(fingerprint)) => {
                    current.state_fingerprint = Some(fingerprint.clone());
                    current.retention_issue = None;
                }
                Ok(None) => {
                    current.state_fingerprint = None;
                    current.retention_issue =
                        Some("upstream did not create state.db after the prompt".into());
                }
                Err(error) => current.retention_issue = Some(error.clone()),
            }
            if matches!(retention, Ok(Some(_))) {
                for record in &mut self.journal.publication_receipts {
                    if reported_publications.contains(&record.operation_id) {
                        record.reported = true;
                    }
                }
                for record in &mut self.journal.born_resources {
                    if reported_publications.contains(&record.pending.operation_id) {
                        record.reported = true;
                    }
                }
            }
            self.save()?;
        }
        retention?;
        outcome.map(|_| ())
    }
    #[allow(clippy::too_many_arguments)] // ACP dispatch needs independent bounded input, output, broker, and provider channels.
    fn acp_response(
        &mut self,
        id: i64,
        rx: &Receiver<Result<Value>>,
        input: &Receiver<Input>,
        writer: &mut impl Write,
        display: &mpsc::SyncSender<String>,
        broker: &mcp::BrokerEndpoint,
        provider_runtime: Option<&ActiveProvider>,
    ) -> Result<Value> {
        let mut application_api_call: Option<ActiveApplicationApi> = None;
        let mut completed_acp: Option<Value> = None;
        let mut completed_acp_error: Option<String> = None;
        let mut acp_failure_deadline: Option<Instant> = None;
        loop {
            if let Err(error) = self.poll_application_api(&mut application_api_call) {
                if let Some(attempt) = self.journal.application_api_attempt.as_mut() {
                    attempt.phase = ApplicationApiPhase::Uncertain;
                }
                self.save()?;
                if let Some(call) = application_api_call.take() {
                    let _ = call.reply.send(json!({"isError":true,
                        "text":format!("application API attempt retained for read-only inspection: {error}")}));
                }
            }
            if application_api_call.is_none() {
                if let Some(error) = completed_acp_error.take() {
                    return Err(error);
                }
                if let Some(result) = completed_acp.take() {
                    return Ok(result);
                }
            }
            if let Some(active) = provider_runtime {
                for _ in 0..2 {
                    match active.requests.try_recv() {
                        Ok(request) => self.handle_provider(request),
                        Err(_) => break,
                    }
                }
            }
            for _ in 0..4 {
                match broker.requests.try_recv() {
                    Ok(request)
                        if matches!(
                            request.name.as_str(),
                            "mini_application_api" | "__mini_gitweb_http_raw"
                        ) =>
                    {
                        if application_api_call.is_some() {
                            let _ = request.reply.send(json!({"isError":true,
                                "text":"application API call already in progress"}));
                        } else {
                            match self.begin_application_api(
                                &request.arguments,
                                request.reply.clone(),
                                Some(request.prompt_epoch),
                                request.name == "__mini_gitweb_http_raw",
                            ) {
                                Ok(active) => application_api_call = Some(active),
                                Err(error) => {
                                    let _ =
                                        request.reply.send(json!({"isError":true,"text":error}));
                                }
                            }
                        }
                    }
                    Ok(request) => self.handle_tool(request, broker),
                    Err(_) => break,
                }
            }
            match input.try_recv() {
                Ok(Input::Disconnect) => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        self.disconnect()?;
                        return Err("hard disconnect".into());
                    }
                }
                Ok(Input::Line(line)) if line == "disconnect" => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        self.disconnect()?;
                        return Err("hard disconnect".into());
                    }
                }
                Ok(Input::Line(line))
                    if line == "attach soft" && self.journal.connection == Connection::Soft =>
                {
                    self.emit("reconnected to soft task\n");
                }
                Ok(Input::Line(line))
                    if line == "attach hard" && self.journal.connection == Connection::Soft =>
                {
                    self.note_hard_reconnect()?;
                }
                Ok(Input::Line(_) | Input::TerminalLine { .. }) => {
                    eprintln!("Hermes prompt running; only disconnect is accepted")
                }
                Ok(Input::ForegroundTool {
                    attachment_id,
                    frame,
                }) => {
                    if let Some(output) = &self.output {
                        let _ = output.try_tool_event_for(
                            attachment_id,
                            json!({"v":1,
                            "type":"tool-complete","isError":true,
                            "requestId":foreground_request_id(&frame),
                            "result":"Hermes prompt is running"}),
                        );
                    }
                }
                Ok(Input::ForegroundResult {
                    attachment_id,
                    request_id,
                }) => {
                    let _ = self.answer_foreground_result(attachment_id, &request_id);
                }
                Ok(Input::ForegroundAck {
                    attachment_id,
                    request_id,
                }) => {
                    let _ = self.answer_foreground_ack(attachment_id, &request_id);
                }
                Ok(Input::Admin(request)) => {
                    let _ = request
                        .reply
                        .send("Hermes is running; stop and fence it first".into());
                }
                Ok(Input::Dispatch(request)) => self.answer_dispatch(request),
                Ok(Input::SoftDetach) => {
                    self.stdin_gone = true;
                }
                Err(mpsc::TryRecvError::Disconnected) => {
                    self.stdin_gone = true;
                    if self.hard_connection.load(Ordering::SeqCst) {
                        self.disconnect()?;
                        return Err("hard disconnect".into());
                    }
                }
                Err(mpsc::TryRecvError::Empty) => {}
            }
            if completed_acp_error.is_some() {
                if acp_failure_deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                    if let Some(call) = application_api_call.take() {
                        if matches!(call.step, ApplicationApiStep::Hello(_)) {
                            self.finish_application_api_no_dispatch(call.operation_id)?;
                        } else if let Some(attempt) = self.journal.application_api_attempt.as_mut()
                        {
                            attempt.phase = ApplicationApiPhase::Uncertain;
                            self.save()?;
                        }
                        let _ = call.reply.send(json!({"isError":true,
                            "text":"application API caller stopped; exact operation retained for inspection"}));
                    }
                    return Err(completed_acp_error.take().unwrap());
                }
                std::thread::sleep(Duration::from_millis(20));
                continue;
            }
            let msg = match rx.recv_timeout(Duration::from_millis(20)) {
                Ok(Ok(v)) => v,
                Ok(Err(e)) if application_api_call.is_some() => {
                    completed_acp_error = Some(format!("ACP wire: {e}"));
                    acp_failure_deadline = Some(cancel_application_api_on_acp_failure(
                        &self.cancelled,
                        &self.application_api_send_gate,
                    ));
                    continue;
                }
                Ok(Err(e)) => return Err(format!("ACP wire: {e}")),
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    if application_api_call.is_some() {
                        completed_acp_error = Some("Hermes ACP stream closed".into());
                        acp_failure_deadline = Some(cancel_application_api_on_acp_failure(
                            &self.cancelled,
                            &self.application_api_send_gate,
                        ));
                        continue;
                    }
                    return Err("Hermes ACP stream closed".into());
                }
                Err(mpsc::RecvTimeoutError::Timeout) => continue,
            };
            if msg.get("id") == Some(&json!(id)) {
                if let Some(error) = msg.get("error") {
                    if application_api_call.is_some() {
                        completed_acp_error = Some(format!("Hermes ACP: {error}"));
                        acp_failure_deadline = Some(cancel_application_api_on_acp_failure(
                            &self.cancelled,
                            &self.application_api_send_gate,
                        ));
                        continue;
                    }
                    return Err(format!("Hermes ACP: {error}"));
                }
                if let Some(result) = msg.get("result") {
                    if application_api_call.is_some() {
                        completed_acp = Some(result.clone());
                        continue;
                    }
                    return Ok(result.clone());
                }
            }
            if msg.get("method").and_then(Value::as_str) == Some("session/request_permission") {
                let reply = json!({"jsonrpc":"2.0","id":msg.get("id"),
                    "result":{"outcome":{"outcome":"cancelled"}}});
                writeln!(writer, "{reply}")
                    .and_then(|_| writer.flush())
                    .map_err(|e| e.to_string())?;
            } else if msg.get("method").and_then(Value::as_str) == Some("session/update") {
                if let Some(text) = msg
                    .pointer("/params/update/content/text")
                    .and_then(Value::as_str)
                {
                    let _ = display.try_send(text.to_owned());
                }
            } else if let Some(peer_id) = msg.get("id") {
                let reply = json!({"jsonrpc":"2.0","id":peer_id,"result":{"error":"unsupported client method"}});
                writeln!(writer, "{reply}")
                    .and_then(|_| writer.flush())
                    .map_err(|e| e.to_string())?;
            }
        }
    }
    fn recover_v2_dispatch_reserve(&mut self) -> Result<()> {
        let Some(attempt) = self.journal.dispatch_attempt.clone() else {
            return Ok(());
        };
        let Some(directory) = attempt.reserve_v2_dir.as_ref() else {
            return Ok(());
        };
        // The first post-op2 save records the confirmed hold and anchor.
        // A later save records signed purse generation/root after exact op3.
        // Crashing between those saves must resume lookup, not mistake the
        // first phase for a fully reconstructed reserve.
        if self
            .journal
            .dispatch_hold
            .as_ref()
            .is_some_and(|hold| hold.reserve_confirmed)
            && attempt.dispatch_generation.is_some()
            && attempt.dispatch_post_root.is_some()
        {
            return Ok(());
        }
        let id = attempt.reserve_operation_id.ok_or("v2 reserve ID absent")?;
        if *directory
            != self
                .config
                .state_dir
                .join(format!("agent-reserve-{:016}", attempt.id))
            || sha256_file(&directory.join("request.bin"))?
                != attempt
                    .reserve_v2_request_sha256
                    .as_deref()
                    .ok_or("v2 reserve request hash absent")?
            || sha256_file(&directory.join("plan.bin"))?
                != attempt
                    .reserve_v2_plan_sha256
                    .as_deref()
                    .ok_or("v2 reserve plan hash absent")?
            || sha256_file(
                &self
                    .config
                    .state_dir
                    .join(format!("dispatch-reserve-source-{id:016}.json")),
            )? != attempt
                .reserve_v2_source_sha256
                .as_deref()
                .ok_or("v2 reserve source hash absent")?
        {
            return Err("v2 reserve source custody changed during recovery".into());
        }
        let authority = self.dispatch()?;
        if !directory.join("submit-marker.json").exists() {
            // Seal and plan are read-only. The client writes this marker
            // durably before it can issue public op2, so its absence proves
            // no native reserve was dispatched from this attempt.
            let hold = self.journal.dispatch_hold.clone();
            let state = self.query_as(&authority)?;
            if state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
                || hold.as_ref().is_some_and(|hold| {
                    state.pointer("/grain/generation").and_then(Value::as_str)
                        != Some(hold.before_generation.as_str())
                        || state.get("targetRoot").and_then(Value::as_str)
                            != Some(hold.before_target_root.as_str())
                })
            {
                return Err("v2 no-submit recovery differs from signed purse origin".into());
            }
            self.journal.dispatch_hold = None;
            self.journal.dispatch_attempt = None;
            self.save()?;
            return Ok(());
        }
        // A submit marker means op2 may have crossed. Public op3 is the
        // only recovery action, including when the original reply was lost.
        self.command_output(
            &self.config.mini,
            &[
                "agent-reserve-lookup",
                "--attempt",
                directory.to_str().ok_or("v2 reserve path UTF-8")?,
            ],
        )?;
        let original: Value = serde_json::from_slice(&bounded_regular_file(
            &directory.join("receipt.json"),
            4096,
        )?)
        .map_err(|error| format!("v2 recovered receipt JSON: {error}"))?;
        let anchor = ReserveAnchor {
            transaction_id: original
                .get("transactionId")
                .and_then(Value::as_str)
                .ok_or("v2 receipt transaction absent")?
                .into(),
            event_id: original
                .get("eventId")
                .and_then(Value::as_str)
                .ok_or("v2 receipt event absent")?
                .into(),
            accepted_count: original
                .get("acceptedCount")
                .and_then(Value::as_str)
                .ok_or("v2 receipt accepted count absent")?
                .into(),
            image_boundary: original
                .get("imageBoundary")
                .and_then(Value::as_str)
                .ok_or("v2 receipt boundary absent")?
                .into(),
        };
        for field in [
            &anchor.transaction_id,
            &anchor.event_id,
            &anchor.accepted_count,
            &anchor.image_boundary,
        ] {
            decimal(field, "recovered v2 reserve receipt")?;
        }
        if original.get("reserveIndex").and_then(Value::as_str)
            != Some(previous_accepted_index(&anchor.accepted_count)?.as_str())
        {
            return Err("v2 recovered receipt index differs from accepted count".into());
        }
        let call_hash = sha256_file(&directory.join("call.bin"))?;
        if let Some(held) = self.journal.dispatch_hold.as_ref() {
            if held.reserve_confirmed
                && (held.reserve_anchor.as_ref() != Some(&anchor)
                    || held.reserve_attempt.as_ref() != Some(directory)
                    || held.reserve_call_sha256.as_deref() != Some(call_hash.as_str()))
            {
                return Err("v2 confirmed hold differs from exact recovered receipt".into());
            }
        }
        let plan: Value = serde_json::from_slice(&bounded_regular_file(
            &directory.join("plan-inspected.json"),
            2_097_152,
        )?)
        .map_err(|error| format!("v2 reserve source plan inspection: {error}"))?;
        let task = self
            .config
            .dispatch_task
            .as_ref()
            .ok_or("dispatchTask absent")?
            .clone();
        if plan
            .pointer("/context/reserveOperationId")
            .and_then(Value::as_str)
            != Some(id.to_string().as_str())
            || plan.pointer("/context/purseTask").and_then(Value::as_str)
                != Some(task.task.as_str())
            || plan
                .pointer("/context/reserveAmount")
                .and_then(Value::as_str)
                != Some(task.reserve.as_str())
            || plan
                .pointer("/context/requestDigest")
                .and_then(Value::as_str)
                != Some(attempt.source_request_digest.as_str())
            || plan
                .pointer("/context/parentGeneration")
                .and_then(Value::as_str)
                != Some(attempt.parent_generation.as_str())
            || self.journal.dispatch_hold.as_ref().is_some_and(|held| {
                plan.pointer("/context/purseGeneration")
                    .and_then(Value::as_str)
                    != Some(held.before_generation.as_str())
                    || held.reserve != task.reserve
            })
        {
            return Err("v2 recovered source plan differs from held purse origin".into());
        }
        let state = self.query_as(&authority)?;
        let before_generation = self
            .journal
            .dispatch_hold
            .as_ref()
            .ok_or("v2 reserve hold absent")?
            .before_generation
            .parse::<u64>()
            .map_err(|_| "v2 held purse generation invalid")?;
        let expected_generation = before_generation
            .checked_add(1)
            .ok_or("v2 held purse generation overflow")?
            .to_string();
        if state.pointer("/grain/status").and_then(Value::as_str) != Some("3")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(task.reserve.as_str())
            || state.pointer("/grain/generation").and_then(Value::as_str)
                != Some(expected_generation.as_str())
            || attempt
                .dispatch_generation
                .as_ref()
                .is_some_and(|generation| {
                    state.pointer("/grain/generation").and_then(Value::as_str)
                        != Some(generation.as_str())
                })
            || attempt.dispatch_post_root.as_ref().is_some_and(|root| {
                state.get("targetRoot").and_then(Value::as_str) != Some(root.as_str())
            })
        {
            return Err("v2 recovered reserve lacks signed held purse".into());
        }
        let hold = self
            .journal
            .dispatch_hold
            .as_mut()
            .ok_or("v2 recovered hold disappeared")?;
        hold.reserve_attempt = Some(directory.clone());
        hold.reserve_confirmed = true;
        hold.reserve_boundary = Some(anchor.image_boundary.clone());
        hold.reserve_call_sha256 = Some(sha256_file(&directory.join("call.bin"))?);
        hold.reserve_source_sha256 = attempt.reserve_v2_source_sha256.clone();
        let outcome = directory.join("submit.outcome.bin");
        if outcome.exists() && outcome.with_extension("json").exists() {
            let observed: Value = serde_json::from_slice(&bounded_regular_file(
                &outcome.with_extension("json"),
                131_072,
            )?)
            .map_err(|error| format!("v2 original outcome JSON: {error}"))?;
            if ReserveAnchor::from_confirmed(&observed)? != anchor {
                return Err("v2 original outcome differs from recovered receipt".into());
            }
            hold.reserve_outcome_path = Some(outcome.clone());
            hold.reserve_outcome_sha256 = Some(sha256_file(&outcome)?);
        } else {
            // A lost original op2 reply can still be proven by op3; retain
            // its exact bytes as the durable original for later audits.
            let mut index = 0u16;
            while directory
                .join(format!("lookup-{index:04}.outcome.bin"))
                .exists()
            {
                index += 1;
            }
            if index == 0 {
                return Err("v2 reserve lookup yielded no retained outcome".into());
            }
            let recovered = directory.join(format!("lookup-{:04}.outcome.bin", index - 1));
            hold.reserve_outcome_sha256 = Some(sha256_file(&recovered)?);
            hold.reserve_outcome_path = Some(recovered);
        }
        hold.reserve_anchor = Some(anchor);
        let saved = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("v2 recovered attempt disappeared")?;
        saved.dispatch_generation = Some(
            state
                .pointer("/grain/generation")
                .and_then(Value::as_str)
                .ok_or("v2 recovered generation absent")?
                .into(),
        );
        saved.dispatch_post_root = Some(
            state
                .get("targetRoot")
                .and_then(Value::as_str)
                .ok_or("v2 recovered root absent")?
                .into(),
        );
        self.save()
    }

    fn recover_v3_dispatch_reserve(&mut self) -> Result<()> {
        let Some(attempt) = self.journal.dispatch_attempt.clone() else {
            return Ok(());
        };
        let Some(lifetime) = attempt.lifetime.as_ref() else {
            return Ok(());
        };
        let directory = &lifetime.reserve_dir;
        let id = attempt.reserve_operation_id.ok_or("v3 reserve ID absent")?;
        if *directory
            != self
                .config
                .state_dir
                .join(format!("agent-lifetime-reserve-{:016}", attempt.id))
            || lifetime.source_path
                != self
                    .config
                    .state_dir
                    .join(format!("dispatch-lifetime-source-{id:016}.json"))
            || sha256_file(&lifetime.source_path)? != lifetime.source_sha256
            || sha256_file(&directory.join("request.bin"))? != lifetime.reserve_request_sha256
            || sha256_file(&directory.join("plan.bin"))? != lifetime.reserve_plan_sha256
        {
            return Err("v3 reserve source custody changed on restart".into());
        }
        let authority = self.dispatch()?;
        let marker = directory.join("submit-marker.json");
        if !marker.exists() {
            // The client writes this marker durably before public op2. Its
            // absence proves this attempt did not cross native dispatch.
            let hold = self
                .journal
                .dispatch_hold
                .clone()
                .ok_or("v3 pre-submit hold absent")?;
            let state = self.query_as(&authority)?;
            if hold.reserve_confirmed
                || hold.reserve_attempt.is_some()
                || state.pointer("/grain/status").and_then(Value::as_str) != Some("1")
                || state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
                || state.pointer("/grain/generation").and_then(Value::as_str)
                    != Some(hold.before_generation.as_str())
                || state.get("targetRoot").and_then(Value::as_str)
                    != Some(hold.before_target_root.as_str())
            {
                return Err("v3 no-submit recovery differs from signed purse origin".into());
            }
            self.journal.dispatch_hold = None;
            self.journal.dispatch_attempt = None;
            // Keep the forward request terminal/uncertain. Even proven no
            // native reserve cannot authorize retransmitting HTTP after an
            // independent resident socket failure.
            self.save()?;
            return Ok(());
        }
        if self
            .journal
            .dispatch_hold
            .as_ref()
            .is_some_and(|hold| hold.reserve_confirmed)
            && attempt.dispatch_generation.is_some()
            && attempt.dispatch_post_root.is_some()
        {
            return Ok(());
        }
        self.command_output(
            &self.config.mini,
            &[
                "agent-lifetime-reserve-lookup",
                "--attempt",
                directory.to_str().ok_or("v3 reserve path UTF-8")?,
            ],
        )?;
        let receipt: Value = serde_json::from_slice(&bounded_regular_file(
            &directory.join("receipt.json"),
            4096,
        )?)
        .map_err(|error| format!("v3 recovered receipt JSON: {error}"))?;
        let anchor = ReserveAnchor {
            transaction_id: receipt
                .get("transactionId")
                .and_then(Value::as_str)
                .ok_or("v3 receipt transaction absent")?
                .into(),
            event_id: receipt
                .get("eventId")
                .and_then(Value::as_str)
                .ok_or("v3 receipt event absent")?
                .into(),
            accepted_count: receipt
                .get("acceptedCount")
                .and_then(Value::as_str)
                .ok_or("v3 receipt count absent")?
                .into(),
            image_boundary: receipt
                .get("imageBoundary")
                .and_then(Value::as_str)
                .ok_or("v3 receipt boundary absent")?
                .into(),
        };
        for field in [
            &anchor.transaction_id,
            &anchor.event_id,
            &anchor.accepted_count,
            &anchor.image_boundary,
        ] {
            decimal(field, "v3 reserve receipt")?;
        }
        if receipt.get("reserveIndex").and_then(Value::as_str)
            != Some(previous_accepted_index(&anchor.accepted_count)?.as_str())
            || lifetime
                .reserve_receipt
                .as_ref()
                .is_some_and(|saved| saved != &anchor)
            || lifetime.reserve_index.as_deref().is_some_and(|saved| {
                receipt.get("reserveIndex").and_then(Value::as_str) != Some(saved)
            })
        {
            return Err("v3 recovered receipt differs from retained historical anchor".into());
        }
        let state = self.query_as(&authority)?;
        let held = self
            .journal
            .dispatch_hold
            .as_ref()
            .ok_or("v3 reserve hold absent")?;
        let before = held
            .before_generation
            .parse::<u64>()
            .map_err(|_| "v3 purse generation malformed")?;
        let next = before
            .checked_add(1)
            .ok_or("v3 purse generation overflow")?
            .to_string();
        if state.pointer("/grain/status").and_then(Value::as_str) != Some("3")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(held.reserve.as_str())
            || state.pointer("/grain/generation").and_then(Value::as_str) != Some(next.as_str())
            || attempt.dispatch_generation.as_ref().is_some_and(|saved| {
                state.pointer("/grain/generation").and_then(Value::as_str) != Some(saved.as_str())
            })
            || attempt.dispatch_post_root.as_ref().is_some_and(|saved| {
                state.get("targetRoot").and_then(Value::as_str) != Some(saved.as_str())
            })
        {
            return Err("v3 recovered reserve lacks signed held purse".into());
        }
        let mut outcome = directory.join("submit.outcome.bin");
        if !outcome.exists() || !outcome.with_extension("json").exists() {
            let mut index = 0u16;
            while directory
                .join(format!("lookup-{index:04}.outcome.bin"))
                .exists()
            {
                index = index.checked_add(1).ok_or("v3 lookup index overflow")?;
            }
            if index == 0 {
                return Err("v3 lookup retained no exact outcome".into());
            }
            outcome = directory.join(format!("lookup-{:04}.outcome.bin", index - 1));
        }
        let observed: Value = serde_json::from_slice(&bounded_regular_file(
            &outcome.with_extension("json"),
            131_072,
        )?)
        .map_err(|error| format!("v3 original/replayed outcome JSON: {error}"))?;
        if ReserveAnchor::from_confirmed(&observed)? != anchor {
            return Err("v3 recovered outcome differs from exact receipt".into());
        }
        let hold = self
            .journal
            .dispatch_hold
            .as_mut()
            .ok_or("v3 hold disappeared")?;
        if hold.reserve_confirmed
            && (hold.reserve_anchor.as_ref() != Some(&anchor)
                || hold.reserve_call_sha256.as_deref()
                    != Some(sha256_file(&directory.join("call.bin"))?.as_str()))
        {
            return Err("v3 confirmed hold differs from recovered call".into());
        }
        hold.reserve_attempt = Some(directory.clone());
        hold.reserve_confirmed = true;
        hold.reserve_boundary = Some(anchor.image_boundary.clone());
        hold.reserve_call_sha256 = Some(sha256_file(&directory.join("call.bin"))?);
        hold.reserve_source_sha256 = Some(lifetime.source_sha256.clone());
        hold.reserve_outcome_path = Some(outcome.clone());
        hold.reserve_outcome_sha256 = Some(sha256_file(&outcome)?);
        hold.reserve_anchor = Some(anchor.clone());
        let saved = self
            .journal
            .dispatch_attempt
            .as_mut()
            .ok_or("v3 recovered attempt disappeared")?;
        saved.dispatch_generation = Some(next);
        saved.dispatch_post_root = Some(
            state
                .get("targetRoot")
                .and_then(Value::as_str)
                .ok_or("v3 recovered held root absent")?
                .into(),
        );
        let lifetime = saved.lifetime.as_mut().ok_or("v3 custody disappeared")?;
        lifetime.reserve_receipt = Some(anchor);
        lifetime.reserve_index = receipt
            .get("reserveIndex")
            .and_then(Value::as_str)
            .map(str::to_owned);
        lifetime.post_reserve_purse_physical_root = saved.dispatch_post_root.clone();
        self.save()
    }

    fn recover(&mut self) -> Result<()> {
        if let Some(record) = self.journal.child.clone() {
            let unit = record.unit.as_deref().ok_or(
                "prior controller died with unscoped child; operator process audit required",
            )?;
            if record.launch_gate_protocol.as_deref() != Some("mini-grain-launch-gate-v1") {
                return Err(
                    "prior child has no durable launch gate; operator process audit required"
                        .into(),
                );
            }
            if unit != format!("mini-grain-t{}-o{}", self.config.task, record.operation_id) {
                return Err("saved worker unit does not match its operation ID".into());
            }
            Self::prove_launcher_gate(&record.program)?;
            // The durable gate bars a delayed systemd StartTransientUnit from
            // executing after this observation. Never signal the saved PID:
            // it may belong to a different process after controller death.
            self.launch_gate(&record.program, unit, "fence")?;
            kill_unit(unit)?;
            prove_worker_unit_stopped(&self.config.task, &record, unit)?;
            let id = self.next_id()?;
            self.journal.reconciliation_log.push(json!({
                "decisionId":id.to_string(),"action":"recover-gated-worker",
                "operationId":record.operation_id.to_string(),"unit":unit,
                "machineProven":true,"stage":"physical-stop-verified"
            }));
            self.journal.child = None;
            self.journal.connection = Connection::Fenced;
            self.journal.unresolved_external.push(format!(
                "worker operation {} stopped after controller restart; external effects need acknowledgement",
                record.operation_id
            ));
            self.save()?;
        }
        self.recover_v2_dispatch_reserve()?;
        self.recover_v3_dispatch_reserve()?;
        self.retry_pending_slot(AuthoritySlot::Dispatch)?;
        if self.journal.dispatch_pending.is_none()
            && self.journal.dispatch_hold.as_ref().is_some_and(|hold| {
                !hold.reserve_confirmed && (hold.reserve_attempt.is_none() || hold.reserve_refused)
            })
            && self
                .journal
                .dispatch_attempt
                .as_ref()
                .is_some_and(|attempt| {
                    !attempt.send_started && attempt.reserve_operation_id.is_none()
                })
        {
            // No Mini reserve was submitted, or its exact retained outcome
            // was definitively refused. A signed idle task corroborates that
            // no purse amount is held. This clears no app-send marker.
            let state = self.query_as(&self.dispatch()?)?;
            if !matches!(
                state.pointer("/grain/status").and_then(Value::as_str),
                Some("0" | "1" | "2" | "6")
            ) || state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            {
                return Err(
                    "unsubmitted/refused dispatch reserve has changed signed task state".into(),
                );
            }
            self.journal.dispatch_hold = None;
            self.journal.dispatch_attempt = None;
            self.save()?;
        }
        if self.journal.dispatch_pending.is_none()
            && self.journal.dispatch_hold.is_none()
            && self
                .journal
                .dispatch_attempt
                .as_ref()
                .is_some_and(|attempt| {
                    !attempt.send_started
                        && !attempt.no_send_release_started
                        && attempt.reserve_operation_id.is_none()
                })
        {
            let state = self.query_as(&self.dispatch()?)?;
            if !matches!(
                state.pointer("/grain/status").and_then(Value::as_str),
                Some("0" | "1")
            ) || state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            {
                return Err("pre-reserve dispatch attempt has changed signed task state".into());
            }
            self.journal.dispatch_attempt = None;
            self.save()?;
        }
        if self.journal.dispatch_pending.is_none()
            && self.journal.dispatch_hold.is_none()
            && self
                .journal
                .dispatch_attempt
                .as_ref()
                .is_some_and(|attempt| attempt.no_send_release_started && !attempt.send_started)
        {
            // The hold is removed only in the same durable journal write as
            // a confirmed ordinary zero-charge settlement. The separately
            // saved release intent rules out interpreting an absent hold as
            // permission to discard an uncertain reserve.
            self.verified_dispatch_settlement(
                self.journal
                    .dispatch_attempt
                    .as_ref()
                    .ok_or("dispatch release attempt disappeared")?,
            )?;
            let state = self.query_as(&self.dispatch()?)?;
            if state.pointer("/grain/status").and_then(Value::as_str) != Some("1")
                || state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            {
                return Err("dispatch zero-release recovery lacks settled task state".into());
            }
            self.journal.dispatch_attempt = None;
            self.save()?;
        }
        if self.journal.dispatch_pending.is_none()
            && self.journal.dispatch_hold.is_none()
            && self
                .journal
                .dispatch_attempt
                .as_ref()
                .is_some_and(|attempt| attempt.audited_charge.is_some())
        {
            // An audited charge is saved before the ordinary settlement. The
            // confirmed settlement removes the hold in the same journal
            // write; an absent hold without this marker proves nothing.
            self.verified_dispatch_settlement(
                self.journal
                    .dispatch_attempt
                    .as_ref()
                    .ok_or("audited dispatch attempt disappeared")?,
            )?;
            let state = self.query_as(&self.dispatch()?)?;
            if !matches!(
                state.pointer("/grain/status").and_then(Value::as_str),
                Some("0" | "1" | "6")
            ) || state.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            {
                return Err("audited dispatch recovery lacks signed settled state".into());
            }
            self.journal.dispatch_attempt = None;
            self.save()?;
        }
        if self.journal.dispatch_pending.is_none()
            && self.journal.dispatch_hold.is_none()
            && self
                .journal
                .dispatch_attempt
                .as_ref()
                .is_some_and(|attempt| attempt.send_started && attempt.response_sha256.is_some())
        {
            let attempt = self
                .journal
                .dispatch_attempt
                .as_ref()
                .ok_or("definite dispatch attempt disappeared")?
                .clone();
            self.verified_dispatch_settlement(&attempt)?;
            if let Some(lifetime) = attempt.lifetime.as_ref() {
                let forward = self
                    .journal
                    .application_api_attempt
                    .as_mut()
                    .ok_or("recovered lifetime forward attempt absent")?;
                if forward.operation_id.to_string() != attempt.http_operation_id
                    || forward.lifetime_committed_receipt.as_ref()
                        != lifetime.committed_receipt.as_ref()
                {
                    return Err("recovered lifetime settlement lacks committed lineage".into());
                }
                let response_sha256 = attempt
                    .response_sha256
                    .as_ref()
                    .ok_or("recovered lifetime response hash absent")?;
                if forward
                    .lifetime_settled_response_sha256
                    .as_ref()
                    .is_some_and(|saved| saved != response_sha256)
                {
                    return Err("recovered lifetime response hash differs".into());
                }
                forward.lifetime_settled_response_sha256 = Some(response_sha256.clone());
                let settlement = attempt
                    .settlement
                    .clone()
                    .ok_or("recovered lifetime settlement record absent")?;
                if settlement.operation != "dispatch settle"
                    || settlement.charge
                        != self
                            .config
                            .dispatch_task
                            .as_ref()
                            .ok_or("dispatchTask absent")?
                            .charge
                {
                    return Err("recovered lifetime settlement charge differs".into());
                }
                forward.lifetime_settlement = Some(LifetimeDefiniteSettlement {
                    dispatch_attempt_id: attempt.id,
                    forward_operation_id: forward.operation_id,
                    settlement,
                });
            }
            self.journal.dispatch_attempt = None;
            self.save()?;
        }
        if self.journal.dispatch_hold.is_some() {
            self.journal.connection = Connection::Fenced;
            let note = "dispatch reservation survived controller restart; app delivery requires exact audit";
            if !self
                .journal
                .unresolved_external
                .iter()
                .any(|entry| entry == note)
            {
                self.journal.unresolved_external.push(note.into());
            }
            self.save()?;
        }
        self.retry_pending_slot(AuthoritySlot::Provider)?;
        if let Some(attempt) = &self.journal.provider_attempt {
            if attempt.send_started && attempt.outcome.is_none() {
                let note = format!("provider request {} crossed durable send boundary before controller restart; upstream result uncertain", attempt.id);
                if !self.journal.unresolved_external.contains(&note) {
                    self.journal.unresolved_external.push(note);
                    self.save()?;
                }
            }
        }
        if self.journal.birth_pending.is_some() && self.journal.birth_operation.is_none() {
            return Err("resource birth pending attempt has no lifecycle marker".into());
        }
        if self.journal.birth_pending.is_some()
            != self
                .journal
                .tool_pending
                .as_ref()
                .is_some_and(|pending| pending.operation == "tool birth")
        {
            return Err("resource birth origin and tool pending attempt differ".into());
        }
        if self
            .journal
            .birth_operation
            .as_ref()
            .is_some_and(|operation| operation.no_native_submit)
            && self.journal.birth_pending.is_some()
        {
            return Err("no-submit birth marker conflicts with a pending native birth".into());
        }
        self.retry_pending(true)?;
        if let Some(operation_id) = self
            .journal
            .workspace_attempt
            .as_ref()
            .map(|attempt| attempt.operation_id)
        {
            self.workspace_recover_operation(operation_id, true)?;
        }
        if let Some(operation_id) = self
            .journal
            .workspace_birth
            .as_ref()
            .map(|birth| birth.operation_id)
        {
            self.workspace_recover_birth(operation_id, true)?;
        }
        self.finish_no_birth()?;
        self.retry_pending(false)?;
        if self.journal.hard_reconnect_pending {
            self.journal.connection = Connection::Fenced;
            self.save()?;
        }
        if let Some(charge) = self.journal.settlement_due.clone() {
            let state = self.query()?;
            let status = state
                .pointer("/grain/status")
                .and_then(Value::as_str)
                .ok_or("recovered grain has no status")?;
            if matches!(status, "3" | "4" | "5" | "7") {
                self.transition(
                    json!({"type":"settle","charge":charge}),
                    "settle",
                    "recovered local completion",
                )?;
            } else if matches!(status, "0" | "1" | "2" | "6") {
                self.journal.settlement_due = None;
                self.save()?;
            } else {
                return Err(format!(
                    "recovery settlement has unexpected grain status {status}"
                ));
            }
        }
        if self.journal.parent_hold.is_some()
            && self.journal.child.is_none()
            && self.journal.pending.is_none()
            && self.journal.settlement_due.is_none()
            && matches!(
                self.journal.connection,
                Connection::Hard | Connection::Soft | Connection::Fenced
            )
        {
            let state = self.query()?;
            if matches!(
                state.pointer("/grain/status").and_then(Value::as_str),
                Some("3" | "4")
            ) {
                self.journal.connection = Connection::Fenced;
                let note = "controller restarted with a held allowance but no retained worker completion; effects require acknowledgement";
                if !self.journal.unresolved_external.iter().any(|s| s == note) {
                    self.journal.unresolved_external.push(note.into());
                }
                self.save()?;
            }
        }
        if self.journal.connection == Connection::Fenced {
            let tool_fence = self.fence_tool();
            let dispatch_fence = self.fence_dispatch();
            let provider_fence = self.fence_provider();
            let state = self.query()?;
            let status = state
                .pointer("/grain/status")
                .and_then(Value::as_str)
                .ok_or("recovered grain has no status")?;
            if matches!(status, "1" | "2" | "3" | "4") {
                self.transition(
                    json!({"type":"interrupt"}),
                    "interrupt",
                    "recovered lost controller or hard transport",
                )?;
            } else if !matches!(status, "0" | "5" | "6" | "7") {
                return Err(format!(
                    "fenced recovery has unexpected grain status {status}"
                ));
            }
            tool_fence?;
            let dispatch_held = dispatch_fence? == DispatchFenceOutcome::HeldForAudit;
            provider_fence?;
            self.journal.connection = if dispatch_held {
                Connection::Fenced
            } else {
                Connection::Detached
            };
            self.journal.hard_reconnect_pending = false;
            self.journal.prompt_witness = None;
            self.save()?;
        }
        Ok(())
    }
    /// Operator-only recovery of one held dispatch request. The operator
    /// chooses the fixed charge or zero after auditing external effects; an
    /// uncertain fd3 send is never auto-settled or sent again. The decision
    /// is durable before the signed ordinary AgentGrain settlement.
    fn reconcile_dispatch_audited(&mut self, charge_fixed: bool) -> Result<()> {
        if self.journal.connection != Connection::Fenced
            || self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.dispatch_pending.is_some()
        {
            return Err(
                "dispatch audit requires fenced stopped caller and resolved native attempts".into(),
            );
        }
        let task = self
            .config
            .dispatch_task
            .clone()
            .ok_or("dispatchTask absent")?;
        let attempt = self
            .journal
            .dispatch_attempt
            .clone()
            .ok_or("no retained dispatch attempt for audit")?;
        retained_exact(
            &attempt.request_path,
            attempt.request_bytes,
            &attempt.request_sha256,
            10 * 1024 * 1024,
        )?;
        if attempt.no_send_release_started && charge_fixed {
            return Err("pre-send release can only be audited at zero charge".into());
        }
        if !attempt.send_started && charge_fixed {
            return Err("unsent dispatch cannot incur app attempt charge".into());
        }
        let hold = self
            .journal
            .dispatch_hold
            .clone()
            .ok_or("audited dispatch settlement lacks retained hold")?;
        let (reserve_id, reserve_anchor) = self.verified_dispatch_reserve_hold(&attempt, &hold)?;
        let charge = if charge_fixed {
            task.charge.clone()
        } else {
            "0".to_owned()
        };
        if let Some(previous) = &attempt.audited_charge {
            if previous != &charge {
                return Err("dispatch audit decision cannot be changed after persistence".into());
            }
        } else {
            let id = self.next_id()?;
            self.journal.reconciliation_log.push(json!({
                "decisionId":id.to_string(), "authority":"dispatch",
                "action":"settle-held-dispatch-audited",
                "stage":"operator-audited-requested",
                "attemptId":attempt.id.to_string(),
                "httpOperationId":attempt.http_operation_id,
                "requestPath":attempt.request_path,
                "requestBytes":attempt.request_bytes,
                "requestSha256":attempt.request_sha256,
                "sourceRequestDigest":attempt.source_request_digest,
                "reserveOperationId":reserve_id.to_string(),
                "reserveReceipt":reserve_anchor,
                "dispatchGeneration":attempt.dispatch_generation,
                "dispatchPostRoot":attempt.dispatch_post_root,
                "sendBoundaryDurable":attempt.send_started,
                "dispatchTransactionId":attempt.committed_dispatch_transaction,
                "dispatchEventId":attempt.committed_dispatch_event,
                "permitSha256":attempt.committed_permit_sha256,
                "responseSha256":attempt.response_sha256,
                "auditedCharge":charge,
                "externalEffectsAcknowledged":false
            }));
            self.journal
                .dispatch_attempt
                .as_mut()
                .ok_or("dispatch attempt disappeared")?
                .audited_charge = Some(charge.clone());
            self.save()?;
        }
        let authority = self.dispatch()?;
        let state = self.query_as(&authority)?;
        let status = state
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("audited dispatch signed status absent")?;
        if !matches!(status, "3" | "5" | "7")
            || state.pointer("/grain/reserved").and_then(Value::as_str)
                != Some(hold.reserve.as_str())
        {
            return Err("audited dispatch signed reservation differs".into());
        }
        let before = hold
            .before_generation
            .parse::<u64>()
            .map_err(|_| "audited dispatch hold generation invalid")?;
        let expected = before
            .checked_add(u64::from(status != "3"))
            .ok_or("audited dispatch generation overflow")?
            .to_string();
        if state.pointer("/grain/generation").and_then(Value::as_str) != Some(expected.as_str())
            || (status == "3"
                && attempt.dispatch_post_root.as_deref()
                    != state.get("targetRoot").and_then(Value::as_str))
            || attempt
                .dispatch_generation
                .as_ref()
                .is_some_and(|generation| generation != &hold.before_generation)
        {
            return Err("audited dispatch generation/root differs from confirmed reserve".into());
        }
        if status == "3" && self.fence_dispatch()? != DispatchFenceOutcome::HeldForAudit {
            return Err("audited dispatch fence did not retain reservation".into());
        }
        self.transition_as(
            &authority,
            json!({"type":"settle","charge":charge}),
            "dispatch audit settle",
            "operator audited exact dispatch attempt",
            vec![],
        )?;
        let after = self.query_as(&authority)?;
        if !matches!(
            after.pointer("/grain/status").and_then(Value::as_str),
            Some("0" | "1" | "6")
        ) || after.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
        {
            return Err("audited dispatch settlement lacks signed terminal state".into());
        }
        let note = format!(
            "dispatch request {} external effects require explicit acknowledgement",
            attempt.id
        );
        if !self.journal.unresolved_external.contains(&note) {
            self.journal.unresolved_external.push(note);
        }
        self.journal.dispatch_attempt = None;
        self.journal.reconciliation_log.push(json!({
            "authority":"dispatch", "action":"settle-held-dispatch-audited",
            "stage":"signed-settlement-confirmed", "attemptId":attempt.id.to_string(),
            "auditedCharge":charge, "externalEffectsAcknowledged":false
        }));
        self.save()
    }
    fn reconcile_hold(&mut self, tool: bool, audited: bool) -> Result<()> {
        self.reconcile_hold_with(
            tool,
            if audited {
                HoldProof::OperatorAudited
            } else {
                HoldProof::SameImage
            },
        )
    }
    fn reconcile_hold_with(&mut self, tool: bool, proof: HoldProof) -> Result<()> {
        let audited = proof == HoldProof::OperatorAudited;
        if tool && self.journal.birth_operation.is_some() {
            return Err("resource birth has a durable no-dispatch or refused marker; settle it at zero through recover".into());
        }
        if tool && legacy_custody_audit::zero_phase_active(self) {
            return Err("legacy B44 audit requires its exact zero-charge settlement".into());
        }
        if self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err(
                "reconciliation requires no live worker or unresolved custody attempt".into(),
            );
        }
        let hold = (if tool {
            &self.journal.tool_hold
        } else {
            &self.journal.parent_hold
        })
        .clone()
        .ok_or("no durable held allowance for this authority")?;
        let authority = if tool { self.tool()? } else { self.parent() };
        let label = if tool { "tool" } else { "parent" };
        let decision = self.next_id()?;
        self.journal
            .reconciliation_log
            .push(json!({"decisionId":decision.to_string(),
            "authority":label,"action":"settle-held-allowance","charge":hold.charge,
            "reserveAttempt":hold.reserve_attempt,"originAudited":audited,
            "originProof":proof.label(),
            "stage":"requested","externalEffectsAcknowledged":false}));
        self.save()?;
        let observed = self.query_as(&authority)?;
        let mut status = observed
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("reconciliation grain status absent")?
            .to_owned();
        if !matches!(status.as_str(), "3" | "4" | "5" | "7") {
            if !matches!(status.as_str(), "0" | "1" | "2" | "6") {
                return Err(format!("unexpected reconciliation status {status}"));
            }
            if !hold.reserve_confirmed
                && !hold.reserve_refused
                && (hold.reserve_attempt.is_some()
                    || observed.get("targetRoot").and_then(Value::as_str)
                        != Some(hold.before_target_root.as_str()))
            {
                return Err(
                    "unconfirmed reserve origin changed; exact attempt audit required".into(),
                );
            }
            if hold.reserve_confirmed {
                let effects = format!("{label} confirmed reservation was externally settled; explicit effects acknowledgement required");
                if !self.journal.unresolved_external.contains(&effects) {
                    self.journal.unresolved_external.push(effects);
                }
            }
            if tool {
                self.journal.tool_hold = None;
            } else {
                self.journal.parent_hold = None;
            }
            self.journal
                .reconciliation_log
                .push(json!({"decisionId":decision.to_string(),
                "authority":label,"stage":"confirmed-no-active-reservation",
                "signedStatus":status}));
            return self.save();
        }
        if observed.pointer("/grain/reserved").and_then(Value::as_str)
            != Some(hold.reserve.as_str())
        {
            return Err("signed reserved allowance differs from durable configured hold".into());
        }
        if !hold.reserve_confirmed || hold.reserve_refused {
            return Err("held allowance has no confirmed exact reserve attempt; refusing to settle another operation".into());
        }
        let before_gen = hold
            .before_generation
            .parse::<u64>()
            .map_err(|_| "held generation invalid")?;
        let current_gen = observed
            .pointer("/grain/generation")
            .and_then(Value::as_str)
            .ok_or("signed generation absent")?
            .parse::<u64>()
            .map_err(|_| "signed generation invalid")?;
        let expected_gen = before_gen
            .checked_add(u64::from(matches!(status.as_str(), "5" | "7")))
            .ok_or("held generation overflow")?;
        if current_gen != expected_gen {
            return Err("signed reservation generation differs from confirmed origin".into());
        }
        if observed.get("imageBoundary").and_then(Value::as_str)
            != hold.reserve_boundary.as_deref()
        {
            match proof {
                HoldProof::OperatorAudited => {}
                HoldProof::SameImage => return Err("intervening Mini events prevent automatic reservation identity proof; use audited admin reconciliation after reviewing exact attempts".into()),
                HoldProof::OwnManagedLaw => {
                    // Other resources' events move the image boundary on a
                    // shared Store. What must not have moved is who can act
                    // on this grain: its owner key is this controller's
                    // custody, and the exact managed law admits workers only
                    // for the pinned-generation witness no-op. No journaled
                    // parent attempt is pending, so the signed reservation
                    // is the confirmed one recorded in this hold.
                    if tool {
                        return Err("delegated tool reservation has no managed-law origin proof".into());
                    }
                    if self.journal.pending.is_some() {
                        return Err("parent attempt pending; managed-law origin proof unavailable".into());
                    }
                    let workers = self.managed_worker_subjects()?;
                    if workers.is_empty() {
                        return Err("no managed worker law configured; origin proof unavailable".into());
                    }
                    let policy = self.query_policy()?;
                    let view = policy.get("view").ok_or("signed policy view absent")?.clone();
                    self.require_managed_worker_policy(
                        &view,
                        &workers,
                        status.as_str(),
                        &current_gen.to_string(),
                    )?;
                }
            }
        }
        let effects = format!("{label} reserved operation may have external effects; explicit operator acknowledgement required");
        if !self.journal.unresolved_external.contains(&effects) {
            self.journal.unresolved_external.push(effects);
            self.save()?;
        }
        if matches!(status.as_str(), "3" | "4") {
            self.transition_as(
                &authority,
                if status == "3" {
                    json!({"type":"disconnect"})
                } else {
                    json!({"type":"interrupt"})
                },
                "reconcile fence",
                "operator fenced held allowance",
                vec![],
            )?;
            let observed = self.query_as(&authority)?;
            status = observed
                .pointer("/grain/status")
                .and_then(Value::as_str)
                .ok_or("fenced reconciliation status absent")?
                .to_owned();
        }
        if !matches!(status.as_str(), "5" | "7") {
            return Err(format!(
                "reconciliation fence did not hold allowance: status {status}"
            ));
        }
        self.transition_as(
            &authority,
            json!({"type":"settle","charge":hold.charge}),
            "reconcile settle",
            "operator fixed-charge settlement",
            vec![],
        )?;
        self.journal
            .reconciliation_log
            .push(json!({"decisionId":decision.to_string(),
            "authority":label,"stage":"signed-settlement-confirmed",
            "charge":hold.charge}));
        self.save()
    }
    fn reconcile_provider_audited(&mut self) -> Result<()> {
        if self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
        {
            return Err(
                "provider reconciliation needs stopped worker and resolved native attempts".into(),
            );
        }
        let task = self
            .config
            .provider_task
            .clone()
            .ok_or("providerTask absent")?;
        let authority = self.provider()?;
        let mut attempt = self
            .journal
            .provider_attempt
            .clone()
            .ok_or("no durable provider request for audit")?;
        let request = retained_exact(
            &attempt.request_path,
            attempt.request_bytes,
            &attempt.request_sha256,
            task.max_request_bytes,
        )?;
        if request.is_empty() {
            return Err("retained provider request is empty".into());
        }
        if attempt.outcome.is_some() != attempt.outcome_path.is_some() {
            return Err("provider outcome journal has incomplete evidence binding".into());
        }
        if let Some(path) = &attempt.outcome_path {
            retained_exact(
                path,
                attempt
                    .outcome_bytes
                    .ok_or("provider outcome length absent")?,
                attempt
                    .outcome_sha256
                    .as_deref()
                    .ok_or("provider outcome digest absent")?,
                task.max_response_bytes,
            )?;
        }
        let already_settled = if task.metering && self.journal.provider_hold.is_none() {
            let settled = self.verified_provider_settlement(&attempt)?;
            let retry_result = next_retry_json(&settled.attempt)?;
            let mut args = vec![
                "retry",
                "--attempt",
                settled
                    .attempt
                    .to_str()
                    .ok_or("provider settlement attempt path UTF-8")?,
                "--mode",
                "lookup",
            ];
            if let Some(socket) = &self.config.host_socket {
                args.extend(["--socket", socket.to_str().ok_or("Host socket path UTF-8")?]);
            }
            self.command_output(&self.config.mini, &args)?;
            let lookup: Value =
                serde_json::from_slice(&bounded_regular_file(&retry_result, 131_072)?)
                    .map_err(|e| format!("provider settlement lookup: {e}"))?;
            if lookup.get("type").and_then(Value::as_str) != Some("confirmed")
                || !matches!(
                    lookup.get("confirmation").and_then(Value::as_str),
                    Some("installed" | "replayed")
                )
                || ReserveAnchor::from_confirmed(&lookup)? != settled.receipt
            {
                return Err(
                    "provider settlement is not confirmed on the current native image".into(),
                );
            }
            Some(settled)
        } else {
            None
        };
        let audited_charge = if let Some(settled) = &already_settled {
            settled.charge.clone()
        } else if task.metering {
            match metered_audit_path(attempt.send_started, attempt.outcome.as_deref())? {
                MeteredAuditPath::ProvenNoSend => "0".to_owned(),
                MeteredAuditPath::CompleteResponse => {
                    if attempt.meter_report_path.is_none()
                        && attempt.meter_report_sha256.is_none()
                        && attempt.metered_charge.is_none()
                    {
                        // Audited recovery may run after the prompt lease ended. This
                        // read-only native quote uses the exact retained response and
                        // signed hold; it never authorizes another upstream send.
                        self.provider_meter_quote_inner(attempt.id, false)?;
                        attempt = self
                            .journal
                            .provider_attempt
                            .clone()
                            .ok_or("metered provider attempt disappeared after quote")?;
                    }
                    self.validated_metered_charge(&attempt)?
                }
            }
        } else if !attempt.send_started
            || attempt
                .outcome
                .as_deref()
                .is_some_and(|kind| kind.starts_with("not-sent:"))
        {
            "0".to_owned()
        } else {
            task.charge.clone()
        };
        let id = self.next_id()?;
        self.journal.reconciliation_log.push(json!({
            "decisionId":id.to_string(), "authority":"provider",
            "action":if task.metering {"settle-provider-source-metered-charge"} else {"settle-provider-fixed-charge"},
            "stage":"operator-audited-requested",
            "providerAttemptId":attempt.id.to_string(),
            "requestPath":attempt.request_path,
            "requestBytes":attempt.request_bytes,
            "requestSha256":attempt.request_sha256,
            "outcomePath":attempt.outcome_path,
            "outcomeBytes":attempt.outcome_bytes,
            "outcomeSha256":attempt.outcome_sha256,
            "sendBoundaryDurable":attempt.send_started,
            "outcome":attempt.outcome,
            "auditedCharge":audited_charge,
            "meterReportPath":attempt.meter_report_path,
            "meterReportSha256":attempt.meter_report_sha256,
            "meteringPin":attempt.metering_pin,
            "settlementReceipt":already_settled,
            "externalEffectsAcknowledged":false
        }));
        self.save()?;
        let observed = self.query_as(&authority)?;
        let status = observed
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("signed provider status absent")?
            .to_owned();
        let mut settlement_confirmed_here = false;
        if let Some(hold) = self.journal.provider_hold.clone() {
            if !hold.reserve_confirmed || hold.reserve_refused {
                return Err("provider hold lacks exact confirmed reserve receipt".into());
            }
            if matches!(status.as_str(), "3" | "5" | "7") {
                if observed.pointer("/grain/reserved").and_then(Value::as_str)
                    != Some(hold.reserve.as_str())
                {
                    return Err("signed provider reserve differs from audited hold".into());
                }
                let before = hold
                    .before_generation
                    .parse::<u64>()
                    .map_err(|_| "provider hold generation invalid")?;
                let current = observed
                    .pointer("/grain/generation")
                    .and_then(Value::as_str)
                    .ok_or("signed provider generation absent")?
                    .parse::<u64>()
                    .map_err(|_| "signed provider generation invalid")?;
                let expected = before
                    .checked_add(u64::from(matches!(status.as_str(), "5" | "7")))
                    .ok_or("provider hold generation overflow")?;
                if current != expected {
                    return Err(
                        "signed provider reservation generation differs from held origin".into(),
                    );
                }
                if status == "3" {
                    self.transition_as(
                        &authority,
                        json!({"type":"disconnect"}),
                        "provider audit fence",
                        "operator fenced provider request",
                        vec![],
                    )?;
                }
                self.transition_as(
                    &authority,
                    json!({"type":"settle","charge":audited_charge}),
                    "provider audit settle",
                    if task.metering {
                        "operator audited source-quoted provider charge"
                    } else {
                        "operator audited fixed provider charge"
                    },
                    vec![],
                )?;
                settlement_confirmed_here = true;
            } else {
                // An idle grain alone does not prove that this held request
                // settled with the configured charge on this history. Keep
                // the exact hold for a separate event-boundary audit.
                return Err(format!(
                    "signed provider status {status} cannot identify the held reservation's settlement"
                ));
            }
        } else if already_settled.is_some() {
            if !matches!(status.as_str(), "0" | "1" | "6")
                || observed.pointer("/grain/reserved").and_then(Value::as_str) != Some("0")
            {
                return Err("provider exact settlement has no signed terminal state".into());
            }
            settlement_confirmed_here = true;
        } else if !matches!(status.as_str(), "0" | "1" | "6") {
            return Err("provider attempt has no hold but signed grain remains reserved".into());
        }
        let after = self.query_as(&authority)?;
        if after.pointer("/grain/status").and_then(Value::as_str) == Some("1") {
            self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "provider audit disconnect",
                "operator completed provider audit",
                vec![],
            )?;
        }
        let effects = format!(
            "provider request {} external effects require explicit acknowledgement",
            attempt.id
        );
        if !self.journal.unresolved_external.contains(&effects) {
            self.journal.unresolved_external.push(effects);
        }
        self.journal.provider_attempt = None;
        let settlement_stage = if settlement_confirmed_here {
            "signed-settlement-confirmed"
        } else {
            "operator-audited-terminal-without-held-receipt"
        };
        self.journal.reconciliation_log.push(json!({
            "decisionId":id.to_string(), "authority":"provider",
            "stage":settlement_stage, "providerAttemptId":attempt.id.to_string(),
            "externalEffectsAcknowledged":false
        }));
        self.save()
    }
    fn abort_refused_provider_request(&mut self) -> Result<()> {
        if self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
        {
            return Err(
                "provider abort requires no live worker or unresolved native attempt".into(),
            );
        }
        let attempt = self
            .journal
            .provider_attempt
            .clone()
            .ok_or("no provider request to abort")?;
        let request = fs::read(&attempt.request_path)
            .map_err(|e| format!("retained provider request absent: {e}"))?;
        if request.len() != attempt.request_bytes
            || sha256_file(&attempt.request_path)? != attempt.request_sha256
        {
            return Err("provider abort request differs from durable exact bytes".into());
        }
        if attempt.send_started || attempt.outcome.is_some() {
            return Err("provider send may have started; use audited settlement".into());
        }
        let hold = self.journal.provider_hold.clone();
        if let Some(hold) = &hold {
            if hold.reserve_confirmed || (hold.reserve_attempt.is_some() && !hold.reserve_refused) {
                return Err("provider reserve may have committed; exact lookup or audited settlement required".into());
            }
        }
        let authority = self.provider()?;
        let state = self.query_as(&authority)?;
        let status = state
            .pointer("/grain/status")
            .and_then(Value::as_str)
            .ok_or("signed provider status absent")?;
        if !matches!(status, "0" | "1" | "6")
            || hold.as_ref().is_some_and(|hold| {
                state.get("targetRoot").and_then(Value::as_str)
                    != Some(hold.before_target_root.as_str())
            })
        {
            return Err("signed provider grain differs from definitively unreserved origin".into());
        }
        let id = self.next_id()?;
        self.journal.reconciliation_log.push(json!({
            "decisionId":id.to_string(), "authority":"provider",
            "action":"abort-definitively-unreserved-provider-request",
            "stage":"signed-origin-confirmed", "providerAttemptId":attempt.id.to_string(),
            "requestPath":attempt.request_path,
            "reserveAttempt":hold.as_ref().and_then(|hold| hold.reserve_attempt.as_ref()),
            "sendBoundaryDurable":false, "signedStatus":status,
            "externalEffectsAcknowledged":false
        }));
        if status == "1" {
            self.transition_as(
                &authority,
                json!({"type":"disconnect"}),
                "provider abort disconnect",
                "definitively unreserved request",
                vec![],
            )?;
        }
        self.journal.provider_hold = None;
        self.journal.provider_attempt = None;
        self.save()
    }
    fn abort_unsubmitted_hold(&mut self, tool: bool) -> Result<()> {
        if tool && self.journal.birth_operation.is_some() {
            return Err("resource birth marker requires its own exact zero-charge recovery".into());
        }
        if self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
        {
            return Err("cannot abort a hold with a child or unresolved native attempt".into());
        }
        let hold = (if tool {
            &self.journal.tool_hold
        } else {
            &self.journal.parent_hold
        })
        .clone()
        .ok_or("no held marker to abort")?;
        if hold.reserve_confirmed || (hold.reserve_attempt.is_some() && !hold.reserve_refused) {
            return Err("a reserve may have committed; use signed settlement, not abort".into());
        }
        let authority = if tool { self.tool()? } else { self.parent() };
        let observed = self.query_as(&authority)?;
        let id = self.next_id()?;
        self.journal.reconciliation_log.push(json!({"decisionId":id.to_string(),
            "authority":if tool {"tool"} else {"parent"},
            "action":"abort-unsubmitted-hold","stage":"no-reserve-dispatched-or-definitively-refused",
            "reserveAttempt":hold.reserve_attempt,"signedStatus":observed.pointer("/grain/status"),
            "signedTargetRoot":observed.get("targetRoot")}));
        if tool {
            self.journal.tool_hold = None;
        } else {
            self.journal.parent_hold = None;
        }
        self.save()
    }
    fn needs_startup_recovery(&self) -> bool {
        let j = &self.journal;
        j.connection == Connection::Fenced
            || j.hard_reconnect_pending
            || j.child.is_some()
            || j.pending.is_some()
            || j.tool_pending.is_some()
            || j.provider_pending.is_some()
            || j.dispatch_pending.is_some()
            || j.parent_hold.is_some()
            || j.tool_hold.is_some()
            || j.provider_hold.is_some()
            || j.dispatch_hold.is_some()
            || j.provider_attempt.is_some()
            || j.dispatch_attempt.is_some()
            || j.settlement_due.is_some()
            || j.workspace_attempt.is_some()
            || j.workspace_birth.is_some()
            || j.birth_pending.is_some()
            || j.birth_operation.is_some()
            || !j.unresolved_external.is_empty()
    }

    /// Runs before `serve` admits any input. The supervisor restarted this
    /// controller; it repairs what it can prove and leaves the rest fenced
    /// for the operator exactly as before.
    fn startup_recovery(&mut self) {
        let proof = prove_prior_run_stopped(&self.config.task);
        self.prior_run_stopped = proof.is_ok();
        if !self.needs_startup_recovery() {
            return;
        }
        self.startup_recovery_active = true;
        let result = self.recover().and_then(|()| self.automatic_reconcile());
        self.startup_recovery_active = false;
        let decision = self.journal.next_operation_id;
        self.journal.reconciliation_log.push(json!({
            "decisionId":decision.to_string(),"action":"startup-recovery","automatic":true,
            "priorRunStopped":self.prior_run_stopped,
            "priorRunProof":proof.err(),
            "result":match &result { Ok(()) => "recovered".to_owned(), Err(e) => e.clone() },
            "connection":self.journal.connection,
            "unresolvedExternal":self.journal.unresolved_external,
        }));
        if let Err(error) = self.save() {
            eprintln!("grain-runtime: startup recovery journal: {error}");
        }
        if let Err(error) = result {
            eprintln!("grain-runtime: startup recovery left the task fenced: {error}");
        }
    }

    /// Settle what `recover` fenced when the identity of the held allowance
    /// is machine-provable, then derive the external-effect acknowledgement
    /// when every channel the worker had is accounted for.
    fn automatic_reconcile(&mut self) -> Result<()> {
        if self.journal.parent_hold.is_some()
            && self.child.is_none()
            && self.journal.child.is_none()
            && self.journal.pending.is_none()
        {
            self.reconcile_hold_with(false, HoldProof::OwnManagedLaw)?;
        }
        if self.journal.unresolved_external.is_empty() {
            return Ok(());
        }
        let notes = self.journal.unresolved_external.clone();
        if !notes.iter().all(|note| derivable_effect_note(note)) {
            return Err("an external-effect note needs operator acknowledgement".into());
        }
        let network_none = self.config.commands.iter().all(|command| {
            command.systemd_scope
                && command
                    .args
                    .windows(2)
                    .any(|pair| pair[0] == "--network" && pair[1] == "none")
        });
        if !network_none {
            return Err("a configured worker has network access; effects need operator acknowledgement".into());
        }
        if self.journal.foreground_attempt.is_some()
            || self.journal.workspace_attempt.is_some()
            || self.journal.workspace_birth.is_some()
            || self.journal.application_api_attempt.is_some()
        {
            return Err("an agent effect is still retained for exact recovery".into());
        }
        self.acknowledge_effects_with(Some(
            "derived: scoped --network none worker whose only external channel is the Mini broker; every Mini attempt resolved; no provider or dispatch attempt outstanding",
        ))
    }

    fn acknowledge_effects(&mut self) -> Result<()> {
        self.acknowledge_effects_with(None)
    }

    fn acknowledge_effects_with(&mut self, derived: Option<&str>) -> Result<()> {
        if self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || self.journal.settlement_due.is_some()
        {
            return Err(
                "settle and reconcile every held operation before acknowledging external effects"
                    .into(),
            );
        }
        if self.journal.unresolved_external.is_empty() {
            return Err("no external-effect uncertainty needs acknowledgement".into());
        }
        for authority in [
            Some(self.parent()),
            self.config
                .tool_task
                .as_ref()
                .map(|_| self.tool())
                .transpose()?,
            self.config
                .provider_task
                .as_ref()
                .map(|_| self.provider())
                .transpose()?,
        ]
        .into_iter()
        .flatten()
        {
            let state = self.query_as(&authority)?;
            let status = state
                .pointer("/grain/status")
                .and_then(Value::as_str)
                .ok_or("grain status absent during external-effect acknowledgement")?;
            if matches!(status, "3" | "4" | "5" | "7") {
                return Err(format!(
                    "{} still has an unresolved reserved allowance",
                    authority.task
                ));
            }
        }
        let id = self.next_id()?;
        let acknowledged = std::mem::take(&mut self.journal.unresolved_external);
        self.journal
            .reconciliation_log
            .push(json!({"decisionId":id.to_string(),
            "action":if derived.is_some() {"derive-no-unaccounted-external-effects"} else {"acknowledge-external-effects"},
            "stage":"acknowledged","automatic":derived.is_some(),"basis":derived,
            "externalEffectsAcknowledged":true,"details":acknowledged}));
        self.save()
    }
    fn reconcile_worker_audited(&mut self) -> Result<()> {
        if self.child.is_some() {
            return Err("this controller still owns a live child handle".into());
        }
        let record = self
            .journal
            .child
            .clone()
            .ok_or("no stranded child record")?;
        let evidence = match &record.unit {
            Some(unit) => {
                if record.launch_gate_protocol.as_deref() == Some("mini-grain-launch-gate-v1") {
                    self.launch_gate(&record.program, unit, "fence")?;
                    kill_unit(unit)?;
                }
                prove_worker_unit_stopped(&self.config.task, &record, unit)?;
                if record.launch_gate_protocol.as_deref() == Some("mini-grain-launch-gate-v1") {
                    "durable gate fenced; operator audited unit and external effects"
                } else {
                    "operator asserted no late wrapper/start request; unit currently inactive, empty cgroup, controller MainPID verified"
                }
            }
            None => "explicit operator assertion of physical process audit; no machine proof",
        };
        let id = self.next_id()?;
        self.journal
            .reconciliation_log
            .push(json!({"decisionId":id.to_string(),
            "action":"clear-stranded-child-after-physical-audit",
            "stage":"physical-audit-recorded","operationId":record.operation_id.to_string(),
            "recordedPid":record.pid,"recordedPgid":record.pgid,"recordedUnit":record.unit,
            "machineProven":false,"operatorAudited":true,"evidence":evidence}));
        self.journal.child = None;
        self.journal.connection = Connection::Fenced;
        self.save()
    }
    fn retry_pending(&mut self, tool: bool) -> Result<()> {
        self.retry_pending_slot(if tool {
            AuthoritySlot::Tool
        } else {
            AuthoritySlot::Parent
        })
    }
    fn retry_pending_slot(&mut self, slot: AuthoritySlot) -> Result<()> {
        let pending = self.journal.pending_for(slot);
        if let Some(p) = pending.clone() {
            if !p.attempt.join("call.bin").is_file() {
                match inspected_pre_submit_refusal(&self.config, &p.attempt) {
                    Ok(Some(refusal)) => {
                        if matches!(
                            p.operation.as_str(),
                            "reserve" | "tool reserve" | "dispatch reserve" | "provider reserve"
                        ) {
                            self.journal
                                .hold_for_mut(slot)
                                .as_mut()
                                .ok_or(
                                    "reserve marker disappeared during prepare refusal recovery",
                                )?
                                .reserve_refused = true;
                        }
                        self.journal.reconciliation_log.push(json!({
                            "action":"recognize-native-pre-submit-refusal",
                            "stage":"before-signed-call",
                            "operationId":p.operation_id.to_string(),
                            "operation":p.operation,
                            "attempt":p.attempt,
                            "outcome":refusal,
                            "heldAllowanceReleased":false
                        }));
                        if p.operation == "tool birth" {
                            let origin = self
                                .journal
                                .birth_pending
                                .as_ref()
                                .ok_or("pre-submit birth has no durable origin")?;
                            if origin.operation_id != p.operation_id {
                                return Err(
                                    "pre-submit birth origin differs from pending attempt".into()
                                );
                            }
                            self.journal.birth_pending = None;
                        }
                        *self.journal.pending_for_mut(slot) = None;
                        self.save()?;
                        return Ok(());
                    }
                    Ok(None) => {}
                    Err(reason) => {
                        return Err(format!("pending custody attempt has no call.bin and invalid prepare-refusal marker: {reason}; manual reconciliation required"));
                    }
                }
                // A crashed custody subprocess may still assemble the call and
                // dispatch later. Absence right now is not a negative receipt.
                return Err("pending custody attempt has no call.bin; child lifetime is uncertain; manual reconciliation required".into());
            }
            let attempt = p.attempt.to_str().ok_or("attempt path UTF-8")?;
            let retry_result = next_retry_json(&p.attempt)?;
            let mut args = vec!["retry", "--attempt", attempt, "--mode", "lookup"];
            if let Some(socket) = &self.config.host_socket {
                args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
            }
            // A refused lookup describes the current image, not necessarily
            // the original submit. A prior branch may have committed this
            // exact call before a fork was replaced. Keep the pending attempt.
            self.command_output(&self.config.mini, &args)?;
            let provider_settlement = if slot == AuthoritySlot::Provider
                && matches!(
                    p.operation.as_str(),
                    "provider settle" | "provider audit settle"
                ) {
                Some(self.provider_settlement_record(&p, &retry_result)?)
            } else {
                None
            };
            if let Some(record) = self.confirmed_publication_receipt(&p, &retry_result)? {
                while self.journal.publication_receipts.len() >= 32 {
                    let Some(index) = self
                        .journal
                        .publication_receipts
                        .iter()
                        .position(|old| old.reported)
                    else {
                        return Err(
                            "publication recovery journal is full; retain pending attempt".into(),
                        );
                    };
                    self.journal.publication_receipts.remove(index);
                }
                self.journal.publication_receipts.push(record);
            }
            if p.operation == "tool birth" {
                if slot != AuthoritySlot::Tool
                    || self.journal.born_resource_count()
                        + self
                            .journal
                            .birth_pending
                            .as_ref()
                            .map_or(1, |origin| origin.members().len())
                        > 8 * 1024
                {
                    return Err("resource birth recovery registry is unavailable".into());
                }
                let origin = self
                    .journal
                    .birth_pending
                    .as_ref()
                    .ok_or("resource birth recovery has no durable origin")?;
                let record = self
                    .confirmed_birth_record(&p, origin, &retry_result)?
                    .ok_or("resource birth recovery has no confirmed receipt")?;
                if self
                    .journal
                    .born_resources
                    .iter()
                    .any(|existing| existing.pending.operation_id == record.pending.operation_id)
                {
                    return Err(
                        "resource birth is already registered with a pending attempt".into(),
                    );
                }
                self.journal.born_resources.push(record);
                self.journal.birth_operation = None;
                self.journal.birth_pending = None;
                self.journal.tool_hold = None;
            }
            if matches!(
                p.operation.as_str(),
                "reserve" | "tool reserve" | "dispatch reserve" | "provider reserve"
            ) {
                self.record_reserve_confirmation(slot, &p.attempt, &retry_result)?;
            }
            if matches!(
                p.operation.as_str(),
                "settle"
                    | "tool settle"
                    | "tool release"
                    | "dispatch settle"
                    | "dispatch release"
                    | "dispatch audit settle"
                    | "reconcile settle"
                    | "provider settle"
                    | "provider audit settle"
            ) {
                if let Some(record) = provider_settlement {
                    self.journal.provider_settlement = Some(record);
                }
                if slot == AuthoritySlot::Dispatch {
                    let settled = self.dispatch_settlement_record(&p, &retry_result)?;
                    self.journal
                        .dispatch_attempt
                        .as_mut()
                        .ok_or("dispatch settlement lost retained attempt")?
                        .settlement = Some(settled);
                }
                *self.journal.hold_for_mut(slot) = None;
                if slot == AuthoritySlot::Parent {
                    self.journal.settlement_due = None;
                }
            }
            if p.operation == "disconnect" && slot == AuthoritySlot::Parent {
                self.journal.connection = Connection::Detached;
            }
            *self.journal.pending_for_mut(slot) = None;
            self.save()?;
        }
        Ok(())
    }
}

enum Input {
    Line(String),
    ForegroundTool {
        attachment_id: u64,
        frame: Vec<u8>,
    },
    ForegroundResult {
        attachment_id: u64,
        request_id: String,
    },
    ForegroundAck {
        attachment_id: u64,
        request_id: String,
    },
    TerminalLine {
        attachment_id: u64,
        line: String,
    },
    Disconnect,
    SoftDetach,
    Admin(control::AdminRequest),
    Dispatch(dispatch_custody::Request),
}

fn signal_group(pgid: i32, signal: i32) -> Result<()> {
    if unsafe { libc::kill(-pgid, signal) } == 0 {
        return Ok(());
    }
    let error = io::Error::last_os_error();
    if error.raw_os_error() == Some(libc::ESRCH) {
        Ok(())
    } else {
        Err(format!("signal {signal} to group {pgid}: {error}"))
    }
}

fn prove_controller_unit(task: &str) -> Result<()> {
    let unit = format!("mini-grain-controller@{task}.service");
    let output = Command::new("/usr/bin/systemctl")
        .args([
            "--user",
            "show",
            "-p",
            "MainPID",
            "-p",
            "ActiveState",
            &unit,
        ])
        .output()
        .map_err(|e| format!("controller service proof: {e}"))?;
    if !output.status.success() {
        return Err("controller service is unavailable".into());
    }
    let source = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let main_pid = source
        .lines()
        .find_map(|line| line.strip_prefix("MainPID="))
        .and_then(|value| value.parse::<u32>().ok());
    let active = source.lines().any(|line| line == "ActiveState=active");
    if main_pid != Some(std::process::id()) || !active {
        return Err(format!(
            "systemdScope requires this controller to be active MainPID of {unit}"
        ));
    }
    Ok(())
}

fn kill_unit(unit: &str) -> Result<()> {
    let name = format!("{unit}.service");
    let output = Command::new("/usr/bin/systemctl")
        .args([
            "--user",
            "kill",
            "--signal=SIGKILL",
            "--kill-whom=all",
            &name,
        ])
        .output()
        .map_err(|e| format!("systemd worker kill: {e}"))?;
    if output.status.success() {
        return Ok(());
    }
    // A missing unit is normal before systemd-run creates it or after
    // --collect removes it. The second kill after wrapper exit closes the
    // creation race; unit_inactive is the final physical observation.
    let error = String::from_utf8_lossy(&output.stderr);
    if error.contains("not loaded") || error.contains("not found") || error.contains("No such") {
        Ok(())
    } else {
        Err(format!("systemd worker kill refused: {}", error.trim()))
    }
}

fn launch_gate(state_dir: &Path, program: &Path, unit: &str, action: &str) -> Result<()> {
    let helper = program.with_file_name("launch-gate");
    let output = Command::new(&helper)
        .arg(action)
        .arg(state_dir)
        .arg(unit)
        .output()
        .map_err(|e| format!("launch gate {}: {e}", helper.display()))?;
    if !output.status.success() {
        return Err(format!(
            "launch gate {action} refused for {unit}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(())
}

fn unit_inactive(unit: &str) -> Result<bool> {
    let name = format!("{unit}.service");
    let output = Command::new("/usr/bin/systemctl")
        .args(["--user", "show", "-p", "ActiveState", "--value", &name])
        .output()
        .map_err(|e| format!("systemd unit observation: {e}"))?;
    if !output.status.success() {
        return Err("systemd unit observation failed".into());
    }
    let state = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    Ok(matches!(state.trim(), "inactive" | "failed" | "dead"))
}

fn prove_worker_unit_stopped(task: &str, record: &ChildRecord, unit: &str) -> Result<()> {
    prove_controller_unit(task)?;
    if unit != format!("mini-grain-t{task}-o{}", record.operation_id) {
        return Err("saved worker unit does not match its durable operation ID".into());
    }
    if !unit_inactive(unit)? {
        return Err("recorded worker unit remains active".into());
    }
    let name = format!("{unit}.service");
    let output = Command::new("/usr/bin/systemctl")
        .args([
            "--user",
            "show",
            "-p",
            "ControlGroup",
            "-p",
            "MainPID",
            &name,
        ])
        .output()
        .map_err(|e| format!("worker cgroup observation: {e}"))?;
    if !output.status.success() {
        return Err("worker cgroup observation failed".into());
    }
    let view = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    let main_pid = view
        .lines()
        .find_map(|s| s.strip_prefix("MainPID="))
        .ok_or("worker MainPID observation absent")?;
    if main_pid != "0" {
        return Err("recorded worker unit still has a MainPID".into());
    }
    let control_group = view
        .lines()
        .find_map(|s| s.strip_prefix("ControlGroup="))
        .ok_or("worker ControlGroup observation absent")?;
    if !control_group.is_empty() {
        let relative = Path::new(control_group)
            .strip_prefix("/")
            .map_err(|_| "worker ControlGroup is not absolute")?;
        if relative
            .components()
            .any(|part| !matches!(part, std::path::Component::Normal(_)))
        {
            return Err("worker ControlGroup has invalid components".into());
        }
        let cgroup = Path::new("/sys/fs/cgroup").join(relative);
        let mut pending = vec![cgroup];
        let mut visited = 0usize;
        while let Some(path) = pending.pop() {
            visited += 1;
            if visited > 4096 {
                return Err("worker cgroup tree exceeds audit bound".into());
            }
            let entries = match fs::read_dir(&path) {
                Ok(entries) => entries,
                Err(error) if error.kind() == io::ErrorKind::NotFound => continue,
                Err(error) => return Err(format!("worker cgroup inspect: {error}")),
            };
            let procs = fs::read_to_string(path.join("cgroup.procs"))
                .map_err(|e| format!("worker cgroup.procs inspect: {e}"))?;
            if !procs.trim().is_empty() {
                return Err("recorded worker cgroup still contains processes".into());
            }
            for entry in entries {
                let entry = entry.map_err(|e| e.to_string())?;
                if entry.file_type().map_err(|e| e.to_string())?.is_dir() {
                    pending.push(entry.path());
                }
            }
        }
    }
    if !unit_inactive(unit)? {
        return Err("worker unit became active during physical audit".into());
    }
    Ok(())
}

/// Read-only process table inspection. This counts all non-zombie members,
/// including grandchildren after the leader exits. The child leader stays
/// unreaped until this count reaches zero, keeping its PGID unavailable for
/// reuse while the controller signals it.
fn group_has_live_member(pgid: i32) -> Result<bool> {
    let output = Command::new("/bin/ps")
        .args(["-axo", "pgid=,stat="])
        .output()
        .map_err(|e| format!("process table unavailable: {e}"))?;
    if !output.status.success() {
        return Err("process table inspection failed".into());
    }
    let table = String::from_utf8(output.stdout).map_err(|e| e.to_string())?;
    Ok(table.lines().any(|line| {
        let mut fields = line.split_whitespace();
        fields.next().and_then(|s| s.parse::<i32>().ok()) == Some(pgid)
            && fields.next().is_some_and(|state| !state.starts_with('Z'))
    }))
}

/// WNOWAIT observes exit without reaping the group leader. Reaping it before
/// group cleanup would permit PGID reuse while descendants are being killed.
fn child_exited_unreaped(child: &Child) -> Result<bool> {
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    let rc = unsafe {
        libc::waitid(
            libc::P_PID,
            child.id() as libc::id_t,
            &mut info,
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    };
    if rc != 0 {
        return Err(format!(
            "non-reaping child wait: {}",
            io::Error::last_os_error()
        ));
    }
    Ok(unsafe { info.si_pid() } != 0)
}

const MAX_ACP_FRAME: usize = 1_048_576;

fn read_acp_frame(reader: &mut impl BufRead) -> io::Result<Option<Vec<u8>>> {
    let mut frame = Vec::new();
    loop {
        let available = reader.fill_buf()?;
        if available.is_empty() {
            return if frame.is_empty() {
                Ok(None)
            } else {
                Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "ACP frame lacks newline",
                ))
            };
        }
        let count = available
            .iter()
            .position(|&b| b == b'\n')
            .map_or(available.len(), |index| index + 1);
        if frame.len().saturating_add(count) > MAX_ACP_FRAME {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "ACP frame exceeds 1 MiB",
            ));
        }
        let complete = available[count - 1] == b'\n';
        frame.extend_from_slice(&available[..count]);
        reader.consume(count);
        if complete {
            return Ok(Some(frame));
        }
    }
}

fn acp_send(writer: &mut impl Write, id: i64, method: &str, params: Value) -> Result<()> {
    let request = json!({"jsonrpc":"2.0","id":id,"method":method,"params":params});
    writeln!(writer, "{request}")
        .and_then(|_| writer.flush())
        .map_err(|e| e.to_string())
}

fn forward_display(mut pipe: impl Read + Send + 'static, output: control::OutputHandle) {
    thread::spawn(move || {
        let mut buffer = [0u8; 4096];
        while let Ok(count) = pipe.read(&mut buffer) {
            if count == 0 {
                break;
            }
            let _ = output.try_output(String::from_utf8_lossy(&buffer[..count]).into_owned());
        }
    });
}

fn interrupt_from_input(
    current_pgid: &Arc<AtomicI32>,
    hard_connection: &Arc<AtomicBool>,
    signal_lock: &Arc<Mutex<()>>,
) {
    let pgid = if let Ok(_guard) = signal_lock.lock() {
        let pgid = current_pgid.load(Ordering::SeqCst);
        if pgid > 0 {
            let _ = signal_group(pgid, libc::SIGTERM);
        }
        pgid
    } else {
        0
    };
    if pgid <= 0 {
        return;
    }
    let current_pgid = current_pgid.clone();
    let hard_connection = hard_connection.clone();
    let signal_lock = signal_lock.clone();
    thread::spawn(move || {
        thread::sleep(Duration::from_millis(500));
        if let Ok(_guard) = signal_lock.lock() {
            if hard_connection.load(Ordering::SeqCst) && current_pgid.load(Ordering::SeqCst) == pgid
            {
                let _ = signal_group(pgid, libc::SIGKILL);
            }
        }
    });
}

fn serve(mut rt: Runtime) -> Result<()> {
    let pgid = rt.current_pgid.clone();
    let hard = rt.hard_connection.clone();
    let lock = rt.signal_lock.clone();
    let cancelled = rt.cancelled.clone();
    let completion_phase = rt.completion_phase.clone();
    let current_unit = rt.current_unit.clone();
    let provider_control = rt.provider_control.clone();
    let custody_gate = rt.custody_gate.clone();
    let application_api_send_gate = rt.application_api_send_gate.clone();
    let state_dir = rt.config.state_dir.clone();
    let interrupt: control::HardInterrupt = Arc::new(move |_| {
        cancelled.store(true, Ordering::SeqCst);
        let gateway = provider_control.lock().ok().and_then(|guard| guard.clone());
        if let Some(gateway) = gateway {
            gateway.revoke();
        }
        let _ = completion_phase.compare_exchange(
            PHASE_RUNNING,
            PHASE_CANCELLED,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        interrupt_from_input(&pgid, &hard, &lock);
        let owned = current_unit.lock().ok().and_then(|entry| entry.clone());
        if let Some((unit, program)) = owned {
            let _ = kill_unit(&unit);
            let _ = launch_gate(&state_dir, &program, &unit, "fence");
            let _ = kill_unit(&unit);
        }
        // The systemd unit is the physical worker authority on Linux. Its
        // stop/fence signals must precede even the brief Mini spawn gate.
        let _ = custody_gate.cancel();
        application_api_send_gate.cancel();
    });
    clear_stale_control_socket(&rt.config.control_socket)?;
    let server = control::start(&rt.config.control_socket, interrupt)?;
    let admin_path = rt.config.state_dir.join("admin.sock");
    clear_stale_control_socket(&admin_path)?;
    let admin = control::start_admin(&admin_path)?;
    let dispatch_server = if let Some(task) = &rt.config.dispatch_task {
        clear_stale_control_socket(&task.socket_path)?;
        Some(dispatch_custody::start(&task.socket_path, task.host_uid)?)
    } else {
        None
    };
    rt.output = Some(server.output_handle());
    rt.startup_recovery();
    let (tx, input) = mpsc::channel();
    let admin_tx = tx.clone();
    thread::spawn(move || {
        let _admin = &admin;
        while let Ok(request) = admin.requests.recv() {
            if admin_tx.send(Input::Admin(request)).is_err() {
                break;
            }
        }
    });
    if let Some(dispatch_server) = dispatch_server {
        let dispatch_tx = tx.clone();
        thread::spawn(move || {
            let _dispatch_server = &dispatch_server;
            while let Ok(request) = dispatch_server.requests.recv() {
                if dispatch_tx.send(Input::Dispatch(request)).is_err() {
                    break;
                }
            }
        });
    }
    thread::spawn(move || {
        let _server = &server;
        let mut current = None;
        while let Ok(event) = server.events.recv() {
            let message = match event {
                control::Event::Attached { id, soft } => {
                    current = Some(id);
                    Input::Line(if soft { "attach soft" } else { "attach hard" }.into())
                }
                control::Event::InspectAttached { id } => {
                    current = Some(id);
                    continue;
                }
                control::Event::Line { id, text } if current == Some(id) => {
                    if text.starts_with("terminal ") {
                        Input::TerminalLine {
                            attachment_id: id,
                            line: text,
                        }
                    } else if let Some(request_id) = text.strip_prefix("tool result ") {
                        Input::ForegroundResult {
                            attachment_id: id,
                            request_id: request_id.to_owned(),
                        }
                    } else if let Some(request_id) = text.strip_prefix("tool ack ") {
                        Input::ForegroundAck {
                            attachment_id: id,
                            request_id: request_id.to_owned(),
                        }
                    } else {
                        Input::Line(text)
                    }
                }
                control::Event::Tool { id, frame } if current == Some(id) => {
                    Input::ForegroundTool {
                        attachment_id: id,
                        frame,
                    }
                }
                control::Event::Detached { id, hard } if current == Some(id) => {
                    current = None;
                    if hard {
                        Input::Disconnect
                    } else {
                        Input::SoftDetach
                    }
                }
                _ => continue,
            };
            if tx.send(message).is_err() {
                break;
            }
        }
    });
    loop {
        let next = input.recv().map_err(|e| e.to_string())?;
        let result = match next {
            Input::Line(line) if line == "attach hard" => rt.attach(false),
            Input::Line(line) if line == "attach soft" => rt.attach(true),
            Input::Line(line) if line == "status" => {
                rt.emit(format!(
                    "{}\n",
                    serde_json::to_string_pretty(&rt.journal).unwrap()
                ));
                Ok(())
            }
            Input::TerminalLine {
                attachment_id,
                line,
            } if line.starts_with("terminal status ") => {
                (|| -> Result<()> {
                    let (attachment, request) = terminal::parse_status_command(&line)
                        .ok_or("invalid terminal status command")?;
                    if attachment != attachment_id
                        || !rt.output.as_ref().is_some_and(|output| {
                            output.is_active_framed_attachment(attachment_id)
                        })
                    {
                        return Err("terminal status attachment changed".into());
                    }
                    let journal = serde_json::to_value(&rt.journal)
                        .map_err(|e| format!("terminal status projection: {e}"))?;
                    let delivered = rt.output.as_ref().is_some_and(|output| {
                        output.try_terminal_event_for(
                            attachment,
                            terminal::state(&journal, attachment, request,
                                rt.config.tool_task.as_ref().map_or(0, |tool|
                                    tool.registered_shared_applications.len())),
                        )
                    });
                    if delivered {
                        Ok(())
                    } else {
                        Err("terminal status delivery failed or attachment changed".into())
                    }
                })()
            }
            Input::Line(line) if line == "recover" => rt.recover(),
            Input::Line(line) if line == "conversation new" => rt.conversation_new(),
            Input::ForegroundResult { attachment_id, request_id } =>
                rt.answer_foreground_result(attachment_id, &request_id),
            Input::ForegroundAck { attachment_id, request_id } =>
                rt.answer_foreground_ack(attachment_id, &request_id),
            Input::Admin(request) => {
                if Instant::now() >= request.deadline
                    || request
                        .phase
                        .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst)
                        .is_err()
                {
                    let _ = request
                        .reply
                        .send("admin action expired before dispatch".into());
                    continue;
                }
                if request.command == "inspect application api" {
                    let result = rt.inspect_application_api();
                    request.phase.store(2, Ordering::SeqCst);
                    let _ = request.reply.send(match &result {
                        Ok(value) => value.to_string(),
                        Err(error) => format!("error: {error}"),
                    });
                    continue;
                }
                let outcome = match request.command.as_str() {
                    "reconcile parent" => rt.reconcile_hold(false, false),
                    "reconcile tool" => rt.reconcile_hold(true, false),
                    "reconcile parent audited" => rt.reconcile_hold(false, true),
                    "reconcile tool audited" => rt.reconcile_hold(true, true),
                    "reconcile provider audited" => rt.reconcile_provider_audited(),
                    "reconcile dispatch audited fixed" => rt.reconcile_dispatch_audited(true),
                    "reconcile dispatch audited zero" => rt.reconcile_dispatch_audited(false),
                    "reconcile provider abort" => rt.abort_refused_provider_request(),
                    "reconcile parent abort" => rt.abort_unsubmitted_hold(false),
                    "reconcile tool abort" => rt.abort_unsubmitted_hold(true),
                    "reconcile tool legacy b44" => legacy_custody_audit::audit_b44(&mut rt),
                    "reconcile tool legacy zero" => legacy_custody_audit::settle_b44_zero(&mut rt),
                    "reconcile effects" => rt.acknowledge_effects(),
                    "reconcile worker audited" => rt.reconcile_worker_audited(),
                    "reconcile foreground audited" => rt.reconcile_foreground_audited(),
                    _ => Err("unknown admin reconciliation action".into()),
                };
                request.phase.store(2, Ordering::SeqCst);
                let _ = request.reply.send(match &outcome {
                    Ok(()) => "ok".into(),
                    Err(error) => format!("error: {error}"),
                });
                outcome
            }
            Input::Dispatch(request) => {
                rt.answer_dispatch(request);
                Ok(())
            }
            Input::ForegroundTool { attachment_id, frame } => {
                let outcome = rt.foreground_tool(attachment_id, &frame, &input);
                if let Err(error) = &outcome {
                    let request_id = foreground_request_id(&frame);
                    if let Some(output) = &rt.output {
                        let _ = output.try_tool_event_for(attachment_id, json!({"v":1,
                            "type":"tool-complete","isError":true,"result":error,
                            "requestId":request_id,
                            "operationId":rt.journal.foreground_attempt.as_ref()
                                .map(|attempt| attempt.operation_id.to_string())}));
                    }
                }
                rt.stdin_gone = false;
                outcome
            }
            Input::Line(line) if line == "disconnect" => rt.disconnect(),
            Input::Line(line) if line.starts_with("run ") => {
                let result = rt.run(&line[4..], &input);
                rt.stdin_gone = false;
                result
            }
            Input::Line(line) if line.starts_with("hermes ") => {
                let result = rt.hermes(&line[7..], &input);
                rt.stdin_gone = false;
                result
            }
            Input::TerminalLine {
                attachment_id,
                line,
            } if line.starts_with("terminal hermes ") => {
                (|| -> Result<()> {
                    let (attachment, request, prompt) = terminal::parse_prompt_command(&line)
                        .ok_or("invalid terminal prompt command")?;
                    if attachment != attachment_id
                        || !rt.output.as_ref().is_some_and(|output| {
                            output.is_active_framed_attachment(attachment_id)
                        })
                    {
                        return Err("terminal prompt attachment changed before dispatch".into());
                    }
                    let result = rt.hermes(prompt, &input);
                    rt.stdin_gone = false;
                    let journal = serde_json::to_value(&rt.journal)
                        .map_err(|e| format!("terminal completion projection: {e}"))?;
                    let delivered = rt.output.as_ref().is_some_and(|output| {
                        output.try_terminal_event_for(
                            attachment,
                            terminal::completion(&journal, attachment, request, result.is_ok(),
                                rt.config.tool_task.as_ref().map_or(0, |tool|
                                    tool.registered_shared_applications.len())),
                        )
                    });
                    if delivered {
                        result
                    } else {
                        Err("terminal completion delivery failed or attachment changed".into())
                    }
                })()
            }
            Input::Disconnect => rt.disconnect(),
            Input::SoftDetach => Ok(()),
            Input::TerminalLine { .. } => Err("unknown terminal command".into()),
            Input::Line(_) => Err(
                "expected attach hard|soft, run NAME, hermes PROMPT, conversation new, status, recover, disconnect"
                    .into(),
            ),
        };
        if let Err(e) = result {
            eprintln!("grain-runtime: {e}");
            rt.emit(format!("grain-runtime: {e}\n"));
        }
    }
}

fn clear_stale_control_socket(path: &Path) -> Result<()> {
    let meta = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => return Err(format!("control socket inspection: {e}")),
    };
    if !meta.file_type().is_socket() || meta.uid() != unsafe { libc::geteuid() } {
        return Err("control socket path is not an owned socket".into());
    }
    match UnixStream::connect(path) {
        Ok(_) => Err("another controller still listens on control socket".into()),
        Err(e) if e.kind() == io::ErrorKind::ConnectionRefused => {
            fs::remove_file(path).map_err(|e| format!("stale control socket cleanup: {e}"))
        }
        Err(e) => Err(format!("control socket probe: {e}")),
    }
}

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().collect();
    if args.len() == 2 && args[1] == "tool-id" {
        let mut bytes = [0u8; 16];
        let result =
            File::open("/dev/urandom").and_then(|mut source| source.read_exact(&mut bytes));
        return match result {
            Ok(()) => {
                for byte in bytes {
                    print!("{byte:02x}");
                }
                println!();
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("grain-runtime tool-id: {error}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() == 4 && (args[1] == "tool-result" || args[1] == "tool-ack") {
        let request_id = match args[3].to_str() {
            Some(id) if valid_foreground_request_id(id) => id,
            _ => {
                eprintln!(
                    "grain-runtime tool-result: request ID must be 32 lowercase hex characters"
                );
                return ExitCode::from(2);
            }
        };
        let result = if args[1] == "tool-ack" {
            control::tool_ack_connect(&PathBuf::from(&args[2]), request_id)
        } else {
            control::tool_result_connect(&PathBuf::from(&args[2]), request_id)
        };
        return match result {
            Ok(result) => {
                println!("{result}");
                if (args[1] == "tool-ack"
                    && result.get("type").and_then(Value::as_str) == Some("tool-acknowledged")
                    && result.get("isError").is_none())
                    || (args[1] == "tool-result"
                        && result.get("isError").and_then(Value::as_bool) == Some(false))
                {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(1)
                }
            }
            Err(error) => {
                eprintln!("grain-runtime tool-result: {error}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() == 7 && args[1] == "tool" {
        let mode = match args[3].to_str() {
            Some("hard") => control::Mode::Hard,
            Some("soft") => control::Mode::Soft,
            _ => {
                eprintln!("grain-runtime tool: mode must be hard or soft");
                return ExitCode::from(2);
            }
        };
        let request_id = match args[4].to_str() {
            Some(id) if valid_foreground_request_id(id) => id,
            _ => {
                eprintln!("grain-runtime tool: request ID must be 32 lowercase hex characters");
                return ExitCode::from(2);
            }
        };
        let arguments = match bounded_regular_file(&PathBuf::from(&args[6]), 262_144)
            .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).map_err(|e| e.to_string()))
        {
            Ok(value) => value,
            Err(error) => {
                eprintln!("grain-runtime tool: arguments: {error}");
                return ExitCode::from(2);
            }
        };
        let frame = json!({"requestId":request_id,
            "name":args[5].to_string_lossy(),"arguments":arguments});
        let bytes = match serde_json::to_vec(&frame) {
            Ok(bytes) if bytes.len() <= 262_144 => bytes,
            _ => {
                eprintln!("grain-runtime tool: request exceeds frame limit");
                return ExitCode::from(2);
            }
        };
        eprintln!("grain-runtime tool requestId={request_id}; recover with tool-result, never repeat a lost call");
        return match control::tool_connect(&PathBuf::from(&args[2]), mode, request_id, &bytes) {
            Ok(result) => {
                println!("{result}");
                if result.get("isError").and_then(Value::as_bool) == Some(false) {
                    ExitCode::SUCCESS
                } else {
                    ExitCode::from(1)
                }
            }
            Err(error) => {
                eprintln!("grain-runtime tool: {error}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() == 3 && args[1] == "mcp-stdio" {
        return match mcp::serve_stdio(&PathBuf::from(&args[2])) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("grain-runtime MCP: {e}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() == 3 && args[1] == "connect" {
        return match control::connect(&PathBuf::from(&args[2]), None) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("grain-runtime connect: {e}");
                ExitCode::from(1)
            }
        };
    }
    if (args.len() == 3 || args.len() == 4) && args[1] == "terminal" {
        let mode = if args.len() == 4 {
            match args[3].to_str() {
                Some("hard") => "hard",
                Some("soft") => "soft",
                _ => {
                    eprintln!("grain-runtime terminal: mode must be hard or soft");
                    return ExitCode::from(2);
                }
            }
        } else {
            "hard"
        };
        return match terminal::connect(&PathBuf::from(&args[2]), mode) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("grain-runtime terminal: {e}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() == 4 && args[1] == "connect" {
        let Some(mode) = args[3].to_str() else {
            eprintln!("grain-runtime connect: mode must be hard or soft");
            return ExitCode::from(2);
        };
        if !matches!(mode, "hard" | "soft") {
            eprintln!("grain-runtime connect: mode must be hard or soft");
            return ExitCode::from(2);
        }
        return match control::connect(&PathBuf::from(&args[2]), Some(mode)) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("grain-runtime connect: {e}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() == 4 && args[1] == "admin" {
        let command = match args[3].to_str() {
            Some(command) => command,
            None => {
                eprintln!("grain-runtime admin: command must be UTF-8");
                return ExitCode::from(2);
            }
        };
        return match control::admin_call(&PathBuf::from(&args[2]), command) {
            Ok(response) if response == "ok" => {
                println!("{response}");
                ExitCode::SUCCESS
            }
            Ok(response) => {
                eprintln!("grain-runtime admin: {response}");
                ExitCode::from(1)
            }
            Err(error) => {
                eprintln!("grain-runtime admin: {error}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() != 3 || args[1] != "serve" {
        eprintln!("usage: grain-runtime serve /absolute/config.json | connect /absolute/socket [hard|soft] | terminal /absolute/socket [hard|soft] | tool-id | tool /absolute/socket hard|soft REQUEST_ID_32_HEX NAME /absolute/arguments.json | tool-result /absolute/socket REQUEST_ID_32_HEX | tool-ack /absolute/socket REQUEST_ID_32_HEX | admin /absolute/stateDir/admin.sock 'reconcile parent|tool|effects|worker audited|foreground audited' | mcp-stdio /absolute/socket");
        return ExitCode::from(2);
    }
    let path = PathBuf::from(&args[2]);
    let result = (|| -> Result<()> {
        let bytes = fs::read(&path).map_err(|e| format!("config read: {e}"))?;
        let config: Config =
            serde_json::from_slice(&bytes).map_err(|e| format!("config decode: {e}"))?;
        serve(Runtime::open(config, path)?)
    })();
    if let Err(e) = result {
        eprintln!("grain-runtime: {e}");
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lifetime_reserve_wall_requires_selected_live_hermes_worker() {
        let selected = AllowedCommand {
            name: "hermes-acp".into(),
            program: "/opt/mini/bwrap".into(),
            args: Vec::new(),
            systemd_scope: true,
            wall_time_seconds: Some(1500),
            reserve: "1".into(),
            charge: "0".into(),
        };
        let program = selected.program.as_path();
        assert_eq!(
            checked_lifetime_worker_wall(&selected, 1500, true, true, Some(program), false)
                .unwrap(),
            1500
        );
        assert!(
            checked_lifetime_worker_wall(&selected, 600, true, true, Some(program), false).is_err()
        );
        assert!(
            checked_lifetime_worker_wall(&selected, 1500, false, true, Some(program), false)
                .is_err()
        );
        assert!(checked_lifetime_worker_wall(
            &selected,
            1500,
            true,
            true,
            Some(Path::new("/other/bwrap")),
            false
        )
        .is_err());
        assert!(
            checked_lifetime_worker_wall(&selected, 1500, true, false, Some(program), false)
                .is_err()
        );
        assert!(
            checked_lifetime_worker_wall(&selected, 1500, true, true, Some(program), true).is_err()
        );
    }

    #[test]
    fn lifetime_settlement_record_survives_restart_validation() {
        let directory = std::env::temp_dir().join(format!(
            "mini-lifetime-settlement-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let request_path = directory.join("application-api-0000000000000009.json");
        fs::write(&request_path, b"{}").unwrap();
        let mut journal = Journal::fresh(json!({}));
        journal.next_operation_id = 12;
        journal.application_api_attempt = Some(ApplicationApiAttempt {
            operation_id: 9,
            route_name: "app".into(),
            request_path,
            request_sha256: sha256_bytes(b"{}").unwrap(),
            phase: ApplicationApiPhase::Uncertain,
            binding_sha256: Some("bb".repeat(32)),
            host_invocation: Some("ab".repeat(16)),
            operation_fingerprint: Some("cc".repeat(32)),
            lifetime_committed_receipt: Some(ReserveAnchor {
                transaction_id: "11".into(),
                event_id: "12".into(),
                accepted_count: "13".into(),
                image_boundary: "14".into(),
            }),
            lifetime_settled_response_sha256: Some("dd".repeat(32)),
            lifetime_settlement: Some(test_lifetime_settlement()),
            reply_path: None,
            reply_sha256: None,
            reported: false,
        });
        let bytes = serde_json::to_vec(&journal).unwrap();
        let mut restored: Journal = serde_json::from_slice(&bytes).unwrap();
        restored.validate_application_api(&directory).unwrap();
        restored
            .application_api_attempt
            .as_mut()
            .unwrap()
            .lifetime_settlement
            .as_mut()
            .unwrap()
            .forward_operation_id = 8;
        assert!(restored.validate_application_api(&directory).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    fn test_lifetime_settlement() -> LifetimeDefiniteSettlement {
        LifetimeDefiniteSettlement {
            dispatch_attempt_id: 10,
            forward_operation_id: 9,
            settlement: DispatchSettlement {
                operation_id: 11,
                operation: "dispatch settle".into(),
                attempt: "/private/settle".into(),
                charge: "1".into(),
                source_sha256: "aa".repeat(32),
                call_sha256: "bb".repeat(32),
                outcome_path: "/private/settle/outcome.bin".into(),
                outcome_sha256: "cc".repeat(32),
                receipt: ReserveAnchor {
                    transaction_id: "15".into(),
                    event_id: "16".into(),
                    accepted_count: "17".into(),
                    image_boundary: "18".into(),
                },
            },
        }
    }

    #[test]
    fn lifetime_initial_reserve_plan_echo_requires_exact_retained_bytes() {
        let directory = std::env::temp_dir().join(format!(
            "mini-lifetime-plan-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let path = directory.join("plan.bin");
        fs::write(&path, [0x00, 0xab, 0xff]).unwrap();
        let plan = json!({"canonicalPlanHex":"00abff"});
        assert_eq!(
            checked_lifetime_reserve_plan_hex(&plan, &path).unwrap(),
            "00abff"
        );
        assert!(checked_lifetime_reserve_plan_hex(&json!({}), &path).is_err());
        assert!(
            checked_lifetime_reserve_plan_hex(&json!({"canonicalPlanHex":"00abfe"}), &path)
                .is_err()
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn lifetime_purse_signs_all_source_target_observe_authority_slots() {
        let signer = DispatchSignerPin {
            role: "1".into(),
            index: "0".into(),
            public_key: "ab".repeat(32),
            key_id: "7007".into(),
            key_epoch: "1".into(),
        };
        let slot = |role: &str| {
            json!({"role":role,"index":"0","headerHex":"00",
            "signing":{"decoded":true,"keyId":"7007","keyEpoch":"1",
                "algorithm":"1"}})
        };
        let slots = vec![slot("4"), slot("8"), slot("1")];
        let approved =
            lifetime_purse_signers(&slots, &signer, Path::new("/private/payer.key")).unwrap();
        assert_eq!(approved.len(), 3);
        assert_eq!(
            approved
                .iter()
                .map(|v| v["role"].as_str().unwrap())
                .collect::<Vec<_>>(),
            vec!["4", "8", "1"]
        );
        let mut reordered = slots.clone();
        reordered.swap(1, 2);
        assert!(
            lifetime_purse_signers(&reordered, &signer, Path::new("/private/payer.key")).is_err()
        );
        let mut wrong_key = slots.clone();
        wrong_key[1]["signing"]["keyId"] = json!("8008");
        assert!(
            lifetime_purse_signers(&wrong_key, &signer, Path::new("/private/payer.key")).is_err()
        );
        assert!(
            lifetime_purse_signers(&slots[..2], &signer, Path::new("/private/payer.key")).is_err()
        );
    }

    #[test]
    fn lifetime_http_reply_needs_durable_permit_and_definite_settlement() {
        let receipt = ReserveAnchor {
            transaction_id: "11".into(),
            event_id: "12".into(),
            accepted_count: "13".into(),
            image_boundary: "14".into(),
        };
        let mut attempt = ApplicationApiAttempt {
            operation_id: 9,
            route_name: "app".into(),
            request_path: "/private/forward.json".into(),
            request_sha256: "aa".repeat(32),
            phase: ApplicationApiPhase::DispatchStarted,
            binding_sha256: Some("bb".repeat(32)),
            host_invocation: None,
            operation_fingerprint: Some("cc".repeat(32)),
            lifetime_committed_receipt: None,
            lifetime_settled_response_sha256: None,
            lifetime_settlement: None,
            reply_path: None,
            reply_sha256: None,
            reported: false,
        };
        let good = json!({"type":"http-v3","committedReceipt":receipt,
            "responseSha256":"dd".repeat(32)});
        assert!(verified_lifetime_definite_reply(&attempt, &good, false).is_err());
        attempt.lifetime_committed_receipt = Some(receipt.clone());
        assert!(verified_lifetime_definite_reply(&attempt, &good, false).is_err());
        attempt.lifetime_settled_response_sha256 = Some("dd".repeat(32));
        assert!(verified_lifetime_definite_reply(&attempt, &good, false).is_err());
        attempt.lifetime_settlement = Some(test_lifetime_settlement());
        assert!(verified_lifetime_definite_reply(&attempt, &good, false).is_ok());
        assert!(verified_lifetime_definite_reply(&attempt, &good, true).is_err());
        let wrong = json!({"type":"http-v3","committedReceipt":receipt,
            "responseSha256":"ee".repeat(32)});
        assert!(verified_lifetime_definite_reply(&attempt, &wrong, false).is_err());
    }

    #[test]
    fn lifetime_historical_inspect_is_read_only_and_requires_settled_exact_reply() {
        let receipt = ReserveAnchor {
            transaction_id: "11".into(),
            event_id: "12".into(),
            accepted_count: "13".into(),
            image_boundary: "14".into(),
        };
        let attempt = ApplicationApiAttempt {
            operation_id: 9,
            route_name: "app".into(),
            request_path: "/private/forward.json".into(),
            request_sha256: "aa".repeat(32),
            phase: ApplicationApiPhase::Uncertain,
            binding_sha256: Some("bb".repeat(32)),
            host_invocation: Some("ab".repeat(16)),
            operation_fingerprint: Some("cc".repeat(32)),
            lifetime_committed_receipt: Some(receipt.clone()),
            lifetime_settled_response_sha256: Some("dd".repeat(32)),
            lifetime_settlement: Some(test_lifetime_settlement()),
            reply_path: None,
            reply_sha256: None,
            reported: false,
        };
        let reply = json!({"type":"http-v3","protocol":"mini-spk-agent-api-v3",
            "operationId":"9","bindingSha256":"bb".repeat(32),
            "operationFingerprint":"cc".repeat(32),
            "responseSha256":"dd".repeat(32),"committedReceipt":receipt});
        let bytes = serde_json::to_vec(&reply).unwrap();
        let encoded = bytes
            .iter()
            .map(|byte| format!("{byte:02x}"))
            .collect::<String>();
        let inspection = json!({"type":"inspection-v3","protocol":"mini-spk-agent-api-v3",
            "operationId":"9","bindingSha256":"bb".repeat(32),
            "operationFingerprint":"cc".repeat(32),"state":"definite",
            "definiteReplySha256":sha256_bytes(&bytes).unwrap(),
            "definiteReplyJsonHex":encoded});
        assert_eq!(
            recovered_lifetime_http(&attempt, &inspection, false).unwrap(),
            Some(reply)
        );
        assert!(recovered_lifetime_http(&attempt, &inspection, true).is_err());
        let mut wrong = inspection.clone();
        wrong["definiteReplySha256"] = json!("ee".repeat(32));
        assert!(recovered_lifetime_http(&attempt, &wrong, false).is_err());
        wrong = inspection.clone();
        wrong["operationFingerprint"] = json!("ee".repeat(32));
        assert!(recovered_lifetime_http(&attempt, &wrong, false).is_err());
        wrong = inspection.clone();
        wrong["state"] = json!("uncertain");
        assert!(recovered_lifetime_http(&attempt, &wrong, false).is_err());
        wrong.as_object_mut().unwrap().remove("definiteReplySha256");
        wrong
            .as_object_mut()
            .unwrap()
            .remove("definiteReplyJsonHex");
        assert_eq!(
            recovered_lifetime_http(&attempt, &wrong, false).unwrap(),
            None
        );
        wrong["state"] = json!("definite");
        assert!(recovered_lifetime_http(&attempt, &wrong, false).is_err());
    }

    #[test]
    fn workspace_pin_rejects_foreign_key_and_symlinked_private_directory() {
        let root = std::env::temp_dir().join(format!(
            "mini-workspace-pin-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let state = root.join("state");
        let workspace = state.join("workspace");
        fs::create_dir_all(&workspace).unwrap();
        for dir in [
            workspace.clone(),
            workspace.join("refs"),
            workspace.join("attempts"),
            workspace.join("sources"),
            workspace.join("proposals"),
        ] {
            if !dir.exists() {
                fs::create_dir(&dir).unwrap();
            }
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let config: Config = serde_json::from_value(json!({
            "mini":root.join("mini"),"host":root.join("host"),
            "hostConfig":root.join("host.json"),"hostSocket":root.join("host.sock"),
            "controlSocket":root.join("control.sock"),"custodyKey":root.join("parent.key"),
            "stateDir":state,"cwd":root,"task":"7101","subject":"7",
            "capability":"71","queryCapability":"74","commands":[],
            "toolTask":{"task":"7102","subject":"8","capability":"81",
                "queryCapability":"82","custodyKey":root.join("tool.key"),
                "parentCapability":"73","parentObserveCapability":"75",
                "reserve":"3","charge":"1","allowedPublications":[],
                "resourceWorkspace":workspace}
        }))
        .unwrap();
        let tool = config.tool_task.as_ref().unwrap();
        let config_path = workspace.join("workspace.json");
        let mut pinned = json!({"type":"minidregg-participant-workspace-v1",
            "host":config.host,"config":config.host_config,"key":tool.custody_key,
            "subject":tool.subject,"socket":config.host_socket,
            "birthContext":null,"namespaceRoot":null});
        fs::write(&config_path, serde_json::to_vec(&pinned).unwrap()).unwrap();
        fs::set_permissions(&config_path, fs::Permissions::from_mode(0o600)).unwrap();
        assert_eq!(
            validate_resource_workspace(&config, tool).unwrap(),
            workspace
        );
        pinned["key"] = json!(root.join("parent.key"));
        fs::write(&config_path, serde_json::to_vec(&pinned).unwrap()).unwrap();
        assert!(validate_resource_workspace(&config, tool).is_err());
        pinned["key"] = json!(tool.custody_key);
        fs::write(&config_path, serde_json::to_vec(&pinned).unwrap()).unwrap();
        let proposal_id = 1;
        let source = b"{\"type\":\"intent\"}";
        let request = b"{\"type\":\"minidregg-workspace-proposal-v1\"}";
        fs::write(
            state.join("workspace-proposal-0000000000000001.json"),
            request,
        )
        .unwrap();
        let proposal_dir = workspace.join("proposals").join("1");
        fs::create_dir_all(&proposal_dir).unwrap();
        fs::write(proposal_dir.join("intent.json"), source).unwrap();
        let mut journal = Journal::fresh(json!({}));
        journal.next_operation_id = 3;
        journal.workspace_proposals.push(WorkspaceProposal {
            id: proposal_id,
            request_sha256: sha256_bytes(request).unwrap(),
            intent_sha256: sha256_bytes(source).unwrap(),
            submitted: true,
        });
        journal.workspace_attempt = Some(WorkspaceAttempt {
            operation_id: 2,
            proposal_id,
            intent_sha256: sha256_bytes(source).unwrap(),
            attempt: root.join("forged-attempt"),
            definite: false,
            no_submit: false,
        });
        assert!(journal.validate_workspace(&config).is_err());
        journal.workspace_attempt.as_mut().unwrap().attempt = workspace.join("attempts").join("2");
        assert!(journal.validate_workspace(&config).is_ok());
        fs::write(proposal_dir.join("intent.json"), b"changed source").unwrap();
        assert!(journal.validate_workspace(&config).is_err());
        fs::write(proposal_dir.join("intent.json"), source).unwrap();
        fs::remove_dir(workspace.join("refs")).unwrap();
        std::os::unix::fs::symlink(&root, workspace.join("refs")).unwrap();
        assert!(validate_resource_workspace(&config, tool).is_err());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn foreground_result_identity_is_durable_and_not_a_hermes_session() {
        let directory = std::env::temp_dir().join(format!(
            "mini-foreground-journal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let request = b"{\"requestId\":\"0123456789abcdef0123456789abcdef\",\"name\":\"mini_grain_status\",\"arguments\":{}}";
        let request_path = directory.join("foreground-0000000000000007.request.json");
        let result_path = directory.join("foreground-0000000000000007.result.json");
        let result = b"{\"isError\":false,\"text\":\"{}\"}";
        write_new(&request_path, request).unwrap();
        write_new(&result_path, result).unwrap();
        write_new(
            &foreground_tombstone_path(&directory, "0123456789abcdef0123456789abcdef"),
            &serde_json::to_vec(&ForegroundTombstone {
                request_id: "0123456789abcdef0123456789abcdef".into(),
                operation_id: 7,
                request_sha256: sha256_bytes(request).unwrap(),
            })
            .unwrap(),
        )
        .unwrap();
        let mut journal = Journal::fresh(json!({}));
        journal.next_operation_id = 8;
        journal.foreground_history.push(ForegroundAttempt {
            request_id: "0123456789abcdef0123456789abcdef".into(),
            operation_id: 7,
            name: "mini_grain_status".into(),
            request_path: request_path.clone(),
            request_sha256: sha256_bytes(request).unwrap(),
            phase: ForegroundPhase::Definite,
            result_path: Some(result_path.clone()),
            result_sha256: Some(sha256_bytes(result).unwrap()),
            reported: false,
        });
        journal.validate_foreground(&directory).unwrap();
        journal.foreground_attempt = Some(journal.foreground_history[0].clone());
        assert!(journal.validate_foreground(&directory).is_err());
        journal.foreground_attempt = None;
        let tombstone_path =
            foreground_tombstone_path(&directory, "0123456789abcdef0123456789abcdef");
        let tombstone = fs::read(&tombstone_path).unwrap();
        fs::write(&tombstone_path, b"{} ").unwrap();
        assert!(journal.validate_foreground(&directory).is_err());
        fs::write(&tombstone_path, tombstone).unwrap();
        fs::write(&result_path, b"different").unwrap();
        assert!(journal.validate_foreground(&directory).is_err());
        assert!(journal.hermes_session.is_none());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn foreground_oversize_result_keeps_a_bounded_explicit_effect_notice() {
        let original = json!({"isError":false,"text":"x".repeat(1_048_576)});
        let original_bytes = serde_json::to_vec(&original).unwrap();
        let (retained, bytes) = bounded_foreground_result(original).unwrap();
        assert!(bytes.len() < 1_000_000);
        assert_eq!(retained["isError"], true);
        assert_eq!(retained["originalResultBytes"], original_bytes.len());
        assert_eq!(
            retained["originalResultSha256"],
            sha256_bytes(&original_bytes).unwrap()
        );
        assert_eq!(retained["originalResultSha256"].as_str().unwrap().len(), 64);
        let envelope = serde_json::to_vec(&json!({"v":1,"type":"tool-complete",
            "operationId":"18446744073709551615",
            "requestId":"0123456789abcdef0123456789abcdef","result":retained}))
        .unwrap();
        assert!(envelope.len() <= 1_048_576);
    }

    #[test]
    fn large_payer_approval_reenters_with_exact_bytes_only() {
        let path = std::env::temp_dir().join(format!(
            "mini-payer-approval-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        // A permitted full HTTP projection can make approval JSON larger than
        // the old 64 KiB retry cap even though it fits the source profile.
        let mut approval = b"{\"canonicalHttpHex\":\"".to_vec();
        approval.extend(std::iter::repeat_n(b'a', 80_000));
        approval.extend_from_slice(b"\"}");
        assert!(approval.len() > 65_536);
        retain_exact_private(&path, &approval, 2_097_152).unwrap();
        retain_exact_private(&path, &approval, 2_097_152).unwrap();
        let mut changed = approval.clone();
        changed[32] = b'b';
        assert!(retain_exact_private(&path, &changed, 2_097_152).is_err());
        assert_eq!(fs::read(&path).unwrap(), approval);
        fs::remove_file(path).unwrap();
    }

    #[test]
    fn application_api_journal_rejects_changed_request_and_repeated_id() {
        let directory = std::env::temp_dir().join(format!(
            "mini-api-journal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&directory).unwrap();
        let path = directory.join("application-api-0000000000000007.json");
        let request = b"{\"operation_id\":\"7\"}";
        write_new(&path, request).unwrap();
        let mut journal = Journal::fresh(json!({}));
        journal.next_operation_id = 8;
        journal.application_api_attempt = Some(ApplicationApiAttempt {
            operation_id: 7,
            route_name: "workroom-app".into(),
            request_path: path.clone(),
            request_sha256: sha256_bytes(request).unwrap(),
            phase: ApplicationApiPhase::Prepared,
            binding_sha256: None,
            host_invocation: None,
            operation_fingerprint: None,
            lifetime_committed_receipt: None,
            lifetime_settled_response_sha256: None,
            lifetime_settlement: None,
            reply_path: None,
            reply_sha256: None,
            reported: false,
        });
        journal.validate_application_api(&directory).unwrap();
        journal
            .application_api_history
            .push(journal.application_api_attempt.clone().unwrap());
        assert!(journal.validate_application_api(&directory).is_err());
        journal.application_api_history.clear();
        let mut no_dispatch = journal.application_api_attempt.take().unwrap();
        no_dispatch.phase = ApplicationApiPhase::NoDispatch;
        no_dispatch.reported = true;
        journal.application_api_history.push(no_dispatch);
        let next_path = directory.join("application-api-0000000000000008.json");
        let next_request = b"{\"operation_id\":\"8\"}";
        write_new(&next_path, next_request).unwrap();
        journal.next_operation_id = 9;
        journal.application_api_attempt = Some(ApplicationApiAttempt {
            operation_id: 8,
            route_name: "workroom-app".into(),
            request_path: next_path,
            request_sha256: sha256_bytes(next_request).unwrap(),
            phase: ApplicationApiPhase::Prepared,
            binding_sha256: None,
            host_invocation: None,
            operation_fingerprint: None,
            lifetime_committed_receipt: None,
            lifetime_settled_response_sha256: None,
            lifetime_settlement: None,
            reply_path: None,
            reply_sha256: None,
            reported: false,
        });
        journal.validate_application_api(&directory).unwrap();
        fs::write(&path, b"changed").unwrap();
        assert!(journal.validate_application_api(&directory).is_err());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn acp_failure_cancels_forward_api_and_sets_bounded_exit() {
        let cancelled = AtomicBool::new(false);
        let gate = application_api_tools::ForwardSendGate::new();
        let start = Instant::now();
        let deadline = cancel_application_api_on_acp_failure(&cancelled, &gate);
        assert!(cancelled.load(Ordering::SeqCst));
        assert!(deadline >= start + Duration::from_secs(2));
        assert!(deadline <= Instant::now() + Duration::from_secs(2));
    }

    fn birth_member(
        name: &str,
        target: &str,
        owner: &str,
        control: &str,
    ) -> resource_tools::BornResource {
        resource_tools::BornResource {
            name: name.into(),
            kind: "object".into(),
            target: target.into(),
            owner_capability: owner.into(),
            control_capability: control.into(),
            max_result_bytes: 1024,
        }
    }

    fn birth_pending_for_test() -> BirthPending {
        BirthPending {
            operation_id: 7,
            family: "office".into(),
            ordinal: 0,
            source_sha256: "digest".into(),
            born: birth_member("office-0-app", "100", "1000", "1001"),
            route: None,
            born_bundle: Vec::new(),
            selected_application: None,
            selected_shared: None,
            authored_intent_sha256: None,
            tool_view: json!({}),
            parent_view: json!({}),
            prompt_operation_id: 1,
            session_id: "s".into(),
            work_origin: None,
        }
    }

    #[test]
    fn birth_bundle_shape_is_backward_compatible_and_complete() {
        let legacy = birth_pending_for_test();
        legacy.validate_members().unwrap();
        let encoded = serde_json::to_value(&legacy).unwrap();
        assert!(encoded.get("route").is_none() && encoded.get("bornBundle").is_none());
        let decoded: BirthPending = serde_json::from_value(encoded).unwrap();
        assert_eq!(decoded, legacy);

        let mut app = legacy;
        app.route = Some(ApplicationBirthRoute::Application);
        app.authored_intent_sha256 = Some("abc".into());
        app.born_bundle = vec![
            app.born.clone(),
            birth_member("office-0-package", "101", "1002", "1003"),
            birth_member("office-0-snapshot", "102", "1004", "1005"),
        ];
        app.validate_members().unwrap();
        let mut malformed = app.clone();
        malformed.born_bundle[2].control_capability = "1002".into();
        assert!(malformed.validate_members().is_err());
        malformed = app.clone();
        malformed.born_bundle.pop();
        assert!(malformed.validate_members().is_err());
        malformed = app.clone();
        malformed.route = None;
        assert!(malformed.validate_members().is_err());

        let record = BornResourceRecord {
            pending: app.clone(),
            attempt: "attempt".into(),
            call_sha256: "call".into(),
            outcome_path: "outcome".into(),
            outcome_sha256: "outcome-digest".into(),
            transaction_id: "1".into(),
            event_id: "2".into(),
            accepted_count: "3".into(),
            image_boundary: "4".into(),
            reported: false,
        };
        let mut journal = Journal::fresh(json!({}));
        journal.born_resources.push(record.clone());
        assert_eq!(journal.born_resource_count(), 3);
        journal.validate_birth_registry().unwrap();
        journal.born_resources.push(record);
        assert!(journal.validate_birth_registry().is_err());
    }

    #[test]
    fn birth_ordinal_crash_before_submit_boundary_reclaims_tail_once() {
        let mut journal = Journal::fresh(json!({}));
        journal.birth_next_ordinal.insert("office".into(), 1);
        journal.birth_operation = Some(BirthOperation {
            family: "office".into(),
            ordinal: 0,
            no_native_submit: true,
        });
        // A controller restart reloads the durable marker from journal JSON.
        let bytes = serde_json::to_vec(&journal).unwrap();
        let mut restarted: Journal = serde_json::from_slice(&bytes).unwrap();
        retire_no_birth_operation(&mut restarted).unwrap();
        assert_eq!(restarted.birth_next_ordinal["office"], 0);
        assert!(restarted.birth_operation.is_none());
        let first = serde_json::to_vec(&restarted).unwrap();
        retire_no_birth_operation(&mut restarted).unwrap();
        assert_eq!(serde_json::to_vec(&restarted).unwrap(), first);
    }

    #[test]
    fn birth_ordinal_crash_after_submit_boundary_preserves_identity() {
        let mut journal = Journal::fresh(json!({}));
        journal.birth_next_ordinal.insert("office".into(), 1);
        journal.birth_operation = Some(BirthOperation {
            family: "office".into(),
            ordinal: 0,
            no_native_submit: false,
        });
        journal.birth_pending = Some(birth_pending_for_test());
        journal.tool_pending = Some(Pending {
            operation_id: 7,
            operation: "tool birth".into(),
            attempt: "attempt".into(),
            uncertain: true,
            publication: None,
        });
        let bytes = serde_json::to_vec(&journal).unwrap();
        let mut restarted: Journal = serde_json::from_slice(&bytes).unwrap();
        assert!(retire_no_birth_operation(&mut restarted).is_err());
        // Even an explicit later refusal and zero settlement cannot establish
        // that the original native submit never crossed the send boundary.
        restarted.birth_pending = None;
        restarted.tool_pending = None;
        retire_no_birth_operation(&mut restarted).unwrap();
        assert_eq!(restarted.birth_next_ordinal["office"], 1);
        assert!(restarted.birth_operation.is_none());
        let old: BirthOperation =
            serde_json::from_value(json!({"family":"office","ordinal":0})).unwrap();
        assert!(!old.no_native_submit);
    }

    #[test]
    fn birth_ordinal_no_submit_marker_rejects_occupied_or_nontail_identity() {
        let mut journal = Journal::fresh(json!({}));
        journal.birth_next_ordinal.insert("office".into(), 2);
        journal.birth_operation = Some(BirthOperation {
            family: "office".into(),
            ordinal: 0,
            no_native_submit: true,
        });
        assert!(retire_no_birth_operation(&mut journal).is_err());
        assert_eq!(journal.birth_next_ordinal["office"], 2);
        assert!(journal.birth_operation.is_some());
    }

    #[test]
    fn birth_ordinal_interrupted_journal_save_keeps_consumed_marker() {
        let root = std::env::temp_dir().join(format!(
            "grain-birth-ordinal-save-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir(&root).unwrap();
        let path = root.join("journal.json");
        let mut journal = Journal::fresh(json!({}));
        journal.birth_next_ordinal.insert("office".into(), 1);
        journal.birth_operation = Some(BirthOperation {
            family: "office".into(),
            ordinal: 0,
            no_native_submit: true,
        });
        atomic_json(&path, &journal).unwrap();
        std::fs::write(path.with_extension("tmp"), b"unresolved").unwrap();
        assert!(persist_retired_no_birth_operation(&path, &mut journal).is_err());
        assert_eq!(journal.birth_next_ordinal["office"], 1);
        assert!(journal.birth_operation.is_some());
        let disk: Journal = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(disk.birth_next_ordinal["office"], 1);
        assert!(disk.birth_operation.is_some());
        std::fs::remove_file(path.with_extension("tmp")).unwrap();
        persist_retired_no_birth_operation(&path, &mut journal).unwrap();
        assert_eq!(journal.birth_next_ordinal["office"], 0);
        let disk: Journal = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        assert_eq!(disk.birth_next_ordinal["office"], 0);
        assert!(disk.birth_operation.is_none());
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn prepare_refusal_requires_exact_attempt_and_native_inspection() {
        let root = std::env::temp_dir().join(format!(
            "grain-pre-submit-refusal-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let attempt = root.join("attempt");
        fs::create_dir_all(&attempt).unwrap();
        let host = root.join("host");
        fs::write(&host, b"#!/bin/sh\n[ \"$2\" = inspect ] && [ \"$3\" = outcome ] || exit 1\nprintf '{\"type\":\"refused\",\"phase\":\"70726570617265\",\"detail\":\"7374616c65546172676574\"}\\n' > \"$5\"\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let original_config = root.join("operator-config.json");
        let copied_config = attempt.join("config.json");
        fs::write(&original_config, b"pinned config").unwrap();
        fs::write(&copied_config, b"pinned config").unwrap();
        let socket = root.join("mini.sock");
        let config: Config = serde_json::from_value(json!({
            "mini":root.join("mini"),"host":host,"hostConfig":original_config,
            "hostSocket":socket,"controlSocket":root.join("control.sock"),
            "custodyKey":root.join("parent.key"),"stateDir":root.join("state"),
            "cwd":root,"task":"7101","subject":"7","capability":"71",
            "queryCapability":"74","commands":[]
        }))
        .unwrap();
        let request = attempt.join("signed-observation.bin");
        fs::write(&request, b"retained signed observation").unwrap();
        let manifest = attempt.join("attempt.json");
        fs::write(
            &manifest,
            serde_json::to_vec(&json!({
                "format":"minidregg-resource-client-attempt-v1", "operation":"submit",
                "host":config.host,"config":copied_config,"socket":config.host_socket
            }))
            .unwrap(),
        )
        .unwrap();
        let frame = attempt.join("pre-submit-refusal.frame");
        fs::write(&frame, b"\xffcanonical outcome bytes").unwrap();
        let marker = attempt.join("pre-submit-refusal.json");
        fs::write(
            &marker,
            serde_json::to_vec(&json!({
                "type":"minidregg-pre-submit-refusal-v1","stage":"prepare","operation":1,
                "frameSha256":sha256_file(&frame).unwrap(),
                "requestSha256":sha256_file(&request).unwrap(),
                "hostConfigSha256":sha256_file(&copied_config).unwrap(),
                "attemptManifestSha256":sha256_file(&manifest).unwrap()
            }))
            .unwrap(),
        )
        .unwrap();
        let decoded = inspected_pre_submit_refusal(&config, &attempt)
            .unwrap()
            .unwrap();
        assert_eq!(decoded["type"], "refused");
        assert_eq!(decoded["phase"], "70726570617265");
        fs::write(&request, b"altered signed observation").unwrap();
        assert!(inspected_pre_submit_refusal(&config, &attempt).is_err());
        fs::write(&request, b"retained signed observation").unwrap();
        fs::write(attempt.join("call.bin"), b"a call may have been dispatched").unwrap();
        assert!(inspected_pre_submit_refusal(&config, &attempt).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn publish_returns_only_its_own_confirmed_receipt_without_reporting_it() {
        let root = std::env::temp_dir().join(format!(
            "grain-current-publication-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        let state = root.join("state");
        fs::create_dir(&state).unwrap();
        fs::write(state.join("status"), b"1").unwrap();
        let mini = root.join("controlled-mini");
        let script = r#"#!/bin/sh
set -eu
state='__STATE__'
command=$1
shift
dir=
intent=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dir) dir=$2; shift 2 ;;
    --intent) intent=$2; shift 2 ;;
    *) shift ;;
  esac
done
mkdir -p "$dir"
if [ "$command" = query ]; then
  status=$(cat "$state/status")
  printf '{"page":{"root":"100","grain":{"task":"7102","generation":"1","status":"%s","remaining":"10","reserved":"3"}}}\n' "$status" > "$dir/view.json"
  printf '%s\n' '{"signing":[{"authorityRoot":"200"}],"imageBoundary":"300"}' > "$dir/challenge.json"
  exit 0
fi
[ "$command" = submit ] || exit 40
printf call > "$dir/call.bin"
printf outcome > "$dir/outcome.bin"
if grep -q '"type": "reserve"' "$intent"; then
  printf 3 > "$state/status"
elif grep -q '"type": "settle"' "$intent"; then
  printf 1 > "$state/status"
elif grep -q '"type": "disconnect"' "$intent"; then
  printf 0 > "$state/status"
fi
printf '%s\n' '{"type":"confirmed","confirmation":"installed","imageBoundary":"300","transactionId":"11","eventId":"12","acceptedCount":"13"}' > "$dir/outcome.json"
"#
        .replace("__STATE__", state.to_str().unwrap());
        fs::write(&mini, script).unwrap();
        fs::set_permissions(&mini, fs::Permissions::from_mode(0o700)).unwrap();
        let config = Config {
            mini,
            host: root.join("host"),
            host_config: root.join("host-config.json"),
            host_socket: None,
            control_socket: state.join("control.sock"),
            custody_key: root.join("parent.key"),
            state_dir: state.clone(),
            cwd: root.clone(),
            task: "7101".into(),
            subject: "7".into(),
            capability: "71".into(),
            query_capability: "74".into(),
            policy_control_capability: Some("72".into()),
            foreground_tool: None,
            dispatch_task: None,
            tool_task: Some(ToolTask {
                task: "7102".into(),
                subject: "8".into(),
                capability: "81".into(),
                query_capability: "82".into(),
                custody_key: root.join("tool.key"),
                parent_capability: "73".into(),
                parent_observe_capability: "75".into(),
                reserve: "3".into(),
                charge: "1".into(),
                allowed_publications: vec![PublicationGrant {
                    kind: "object".into(),
                    target: "7003".into(),
                    capability: "93".into(),
                    observe_capability: "94".into(),
                }],
                allowed_reads: vec![],
                resource_workspace: None,
                allowed_birth_families: vec![],
                allowed_application_families: vec![],
                allowed_session_families: vec![],
                registered_shared_applications: vec![],
                allowed_application_api_routes: vec![],
                allowed_application_lifetime_routes: vec![],
                agent_api_host_sha256: None,
                lifetime_api_host_sha256: None,
                current_birth_host_sha256: None,
            }),
            provider_task: None,
            commands: vec![],
        };
        let mut runtime = Runtime::open(config, root.join("config.json")).unwrap();
        runtime.journal.connection = Connection::Hard;
        runtime.journal.child = Some(ChildRecord {
            operation_id: 41,
            pid: 1,
            program: root.join("hermes-acp"),
            pgid: 1,
            unit: None,
            launch_gate_protocol: None,
        });
        runtime.journal.prompt_witness = Some(json!({"task":"7101","before":{"generation":"1"}}));
        runtime.journal.hermes_session = Some(HermesSession {
            id: "current-session".into(),
            workspace: root.clone(),
            load_verified: true,
            state_fingerprint: None,
            retention_issue: None,
            pending_prompt: true,
        });
        runtime.prompt_active = true;
        runtime.save().unwrap();
        let mut stale = PublicationReceipt {
            prompt_operation_id: 40,
            session_id: "prior-session".into(),
            work_origin: None,
            operation_id: 2,
            attempt: root.join("old-attempt"),
            source_sha256: String::new(),
            call_sha256: String::new(),
            outcome_path: root.join("old-outcome"),
            outcome_sha256: String::new(),
            targets: vec!["7003".into()],
            transaction_id: "91".into(),
            event_id: "92".into(),
            accepted_count: "93".into(),
            image_boundary: "94".into(),
            reported: false,
        };
        runtime.journal.publication_receipts.push(stale.clone());
        runtime.save().unwrap();

        let response = runtime
            .tool_call(
                "mini_publish",
                &json!({"publications":[{"kind":"object","target":"7003",
                    "expectedTargetRoot":"700","payload":{"type":"scalar","actions":[]}}]}),
            )
            .unwrap();
        assert_eq!(response["grain"]["status"], "0");
        assert_eq!(response["targetRoot"], "100");
        let receipt = &response["publicationReceipt"];
        assert_eq!(receipt["type"], "confirmed-mini-publication-v1");
        assert_eq!(receipt["scope"], "historical-accepted-transition");
        assert_eq!(receipt["promptOperationId"], 41);
        assert_eq!(receipt["transactionId"], "11");
        assert_eq!(receipt["eventId"], "12");
        assert_eq!(receipt["acceptedCount"], "13");
        assert_eq!(receipt["imageBoundary"], "300");
        assert_eq!(receipt["publicationTargetIds"], json!(["7003"]));
        assert_eq!(runtime.journal.publication_receipts.len(), 2);
        assert_eq!(
            receipt["toolOperationId"],
            runtime.journal.publication_receipts[1].operation_id
        );
        assert!(!runtime.journal.publication_receipts[1].reported);
        let persisted: Value =
            serde_json::from_slice(&fs::read(state.join("journal.json")).unwrap()).unwrap();
        assert_eq!(persisted["publicationReceipts"][1]["reported"], false);

        let prior = vec![2];
        let ids = vec!["7003".to_owned()];
        assert!(current_publication_receipt(
            &runtime.journal.publication_receipts,
            &prior,
            42,
            "current-session",
            None,
            &ids
        )
        .is_err());
        assert!(current_publication_receipt(
            &runtime.journal.publication_receipts,
            &prior,
            41,
            "wrong-session",
            None,
            &ids
        )
        .is_err());
        stale.operation_id = runtime.journal.publication_receipts[1].operation_id + 1;
        stale.prompt_operation_id = 41;
        stale.session_id = "current-session".into();
        runtime.journal.publication_receipts.push(stale);
        assert!(current_publication_receipt(
            &runtime.journal.publication_receipts,
            &prior,
            41,
            "current-session",
            None,
            &ids
        )
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn joint_grants_match_native_observation_footprint() {
        let authority = Authority {
            task: "7102".into(),
            subject: "8".into(),
            capability: "81".into(),
            query_capability: "82".into(),
            custody_key: PathBuf::from("/private/tool.key"),
        };
        let publications = vec![json!({"kind":"object","target":"7003",
            "capability":"93","observeCapability":"94"})];
        let grants =
            grain_observation_grants(&authority, Some(("7101", "74")), &publications).unwrap();
        assert_eq!(
            grants,
            vec![
                json!({"kind":"object","target":"7102","capability":"82"}),
                json!({"kind":"object","target":"7101","capability":"74"}),
                json!({"kind":"object","target":"7003","capability":"94"}),
            ]
        );
    }

    #[test]
    fn provider_send_requires_confirmed_reserved_coordinates() {
        let hold = HeldCharge {
            reserve: "3".into(),
            charge: "1".into(),
            before_generation: "4".into(),
            before_target_root: "old-root".into(),
            reserve_attempt: None,
            reserve_confirmed: true,
            reserve_refused: false,
            reserve_boundary: Some("accepted-reserve-image".into()),
            reserve_call_sha256: None,
            reserve_source_sha256: None,
            reserve_outcome_path: None,
            reserve_outcome_sha256: None,
            reserve_anchor: None,
        };
        let current = json!({"grain":{"status":"3","reserved":"3","generation":"4"},
            "imageBoundary":"accepted-reserve-image"});
        assert!(provider_reserve_coordinates(&current, &hold));
        let mut replaced = current.clone();
        replaced["imageBoundary"] = json!("later-same-amount-reserve");
        // Intervening provider writes are checked by the native continuity
        // receipt, while these signed fields still bind the held allowance.
        assert!(provider_reserve_coordinates(&replaced, &hold));
        replaced = current.clone();
        replaced["grain"]["generation"] = json!("5");
        assert!(!provider_reserve_coordinates(&replaced, &hold));
        replaced = current.clone();
        replaced["grain"]["reserved"] = json!("2");
        assert!(!provider_reserve_coordinates(&replaced, &hold));
    }

    #[test]
    fn provider_retry_replays_exact_retained_response_without_new_reserve() {
        let dir =
            std::env::temp_dir().join(format!("grain-provider-replay-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let request_path = dir.join("request");
        let response_path = dir.join("response");
        let headers_path = dir.join("response-headers");
        let request_bytes = br#"{"model":"local","messages":[]}"#;
        let response_bytes = br#"{"choices":[]}"#;
        let headers = b"HTTP/1.1 200 OK\r\nContent-Type: application/json\r\n\r\n";
        write_new(&request_path, request_bytes).unwrap();
        write_new(&response_path, response_bytes).unwrap();
        write_new(&headers_path, headers).unwrap();
        let retained = ProviderReplay {
            prompt_operation_id: 42,
            parent_generation: "3".into(),
            request_path: request_path.clone(),
            request_bytes: request_bytes.len(),
            request_sha256: sha256_file(&request_path).unwrap(),
            response_path: response_path.clone(),
            response_bytes: response_bytes.len(),
            response_sha256: sha256_file(&response_path).unwrap(),
            status: 200,
            content_type: "application/json".into(),
            response_headers_path: Some(headers_path.clone()),
            response_headers_bytes: Some(headers.len()),
            response_headers_sha256: Some(sha256_file(&headers_path).unwrap()),
            meter_report_path: None,
            meter_report_sha256: None,
            metered_charge: None,
        };
        let request = provider::ProviderRequest {
            lease: provider::LeaseId {
                prompt_operation_id: 42,
                parent_generation: "3".into(),
            },
            model: "local".into(),
            exact_body: request_bytes.to_vec(),
        };
        match Runtime::provider_replay(std::slice::from_ref(&retained), &request).unwrap() {
            Some(provider::ForwardPermit::Replay { exact_response, .. }) => {
                assert_eq!(exact_response, response_bytes)
            }
            _ => panic!("same-body retry must use retained response"),
        }
        let mut other_prompt = provider::ProviderRequest {
            lease: provider::LeaseId {
                prompt_operation_id: 43,
                parent_generation: "4".into(),
            },
            model: "local".into(),
            exact_body: request_bytes.to_vec(),
        };
        assert!(
            Runtime::provider_replay(std::slice::from_ref(&retained), &other_prompt)
                .unwrap()
                .is_none()
        );
        other_prompt.lease = request.lease.clone();
        other_prompt.exact_body.push(b' ');
        assert!(
            Runtime::provider_replay(std::slice::from_ref(&retained), &other_prompt)
                .unwrap()
                .is_none()
        );
        fs::write(
            &headers_path,
            b"HTTP/1.1 200 OK\r\nContent-Type: text/plain\r\n\r\n",
        )
        .unwrap();
        assert!(Runtime::provider_replay(std::slice::from_ref(&retained), &request).is_err());
        fs::write(&headers_path, headers).unwrap();
        fs::write(&response_path, b"changed").unwrap();
        assert!(Runtime::provider_replay(&[retained], &request).is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn metered_quote_binds_tariff_hold_and_source_settle_charge() {
        let pin = ProviderMeteringPin {
            provider_resource_id: "7004".into(),
            metadata_version: 1,
            model: "fixture".into(),
            tariff_version: "1".into(),
            tariff_digest: "123".into(),
            input_micro_per_million: "1".into(),
            output_micro_per_million: "2".into(),
            max_input_tokens: Some(2),
            max_output_tokens: Some(3),
        };
        let mut report = json!({
            "type":"minidregg-provider-metering-v1", "status":"quoted-reported-usage",
            "providerResourceId":"7004", "model":"fixture", "tariffVersion":"1",
            "tariffDigest":"123", "requestDigest":"101", "responseDigest":"102",
            "requestBytes":"20", "responseBytes":"30", "promptTokens":"2",
            "completionTokens":"3", "totalTokens":"5", "reserve":"10", "charge":"7",
            "operation":{"type":"settle","charge":"7"},
            "claim":"provider-reported usage under operator tariff; not invoice-verified"
        });
        assert_eq!(
            provider_quote_charge(&report, &pin, "10", 20, 30).unwrap(),
            "7"
        );
        report["charge"] = json!("11");
        report["operation"]["charge"] = json!("11");
        assert!(provider_quote_charge(&report, &pin, "10", 20, 30).is_err());
        report["charge"] = json!("7");
        report["operation"]["charge"] = json!("6");
        assert!(provider_quote_charge(&report, &pin, "10", 20, 30).is_err());
        report["operation"]["charge"] = json!("7");
        report["tariffDigest"] = json!("124");
        assert!(provider_quote_charge(&report, &pin, "10", 20, 30).is_err());
        report["tariffDigest"] = json!("123");
        report["responseBytes"] = json!("31");
        assert!(provider_quote_charge(&report, &pin, "10", 20, 30).is_err());
        report["responseBytes"] = json!("30");
        report["promptTokens"] = json!("3");
        assert!(provider_quote_charge(&report, &pin, "10", 20, 30).is_err());
        report["promptTokens"] = json!("2");
        report["completionTokens"] = json!("4");
        assert!(provider_quote_charge(&report, &pin, "10", 20, 30).is_err());
    }

    #[test]
    fn metered_maximum_charge_uses_pinned_token_caps_and_rounds_up() {
        let pin = ProviderMeteringPin {
            provider_resource_id: "7004".into(),
            metadata_version: 1,
            model: "fixture".into(),
            tariff_version: "1".into(),
            tariff_digest: "123".into(),
            input_micro_per_million: "500000".into(),
            output_micro_per_million: "1000000".into(),
            max_input_tokens: Some(3),
            max_output_tokens: Some(2),
        };
        let maximum = provider_max_charge_bound(&pin, 3, 2).unwrap();
        assert_eq!(maximum, 4);
        assert!(maximum <= 4);
        assert!(maximum > 3);
    }

    #[test]
    fn metered_audit_never_turns_uncertain_send_into_zero_charge() {
        assert_eq!(
            metered_audit_path(false, None).unwrap(),
            MeteredAuditPath::ProvenNoSend
        );
        assert_eq!(
            metered_audit_path(true, Some("not-sent:before-upstream")).unwrap(),
            MeteredAuditPath::ProvenNoSend
        );
        assert_eq!(
            metered_audit_path(true, Some("received:200:application/json")).unwrap(),
            MeteredAuditPath::CompleteResponse
        );
        assert!(metered_audit_path(true, None).is_err());
        assert!(metered_audit_path(true, Some("uncertain:lost-reply")).is_err());
        assert!(metered_audit_path(false, Some("received:200:application/json")).is_err());
    }

    #[test]
    fn metered_recovery_accepts_only_the_exact_fenced_reservation() {
        let hold = HeldCharge {
            reserve: "3".into(),
            charge: "0".into(),
            before_generation: "8".into(),
            before_target_root: "17".into(),
            reserve_attempt: None,
            reserve_confirmed: true,
            reserve_refused: false,
            reserve_boundary: None,
            reserve_call_sha256: None,
            reserve_source_sha256: None,
            reserve_outcome_path: None,
            reserve_outcome_sha256: None,
            reserve_anchor: None,
        };
        let fenced = json!({"grain":{"status":"5","generation":"9","reserved":"3"}});
        assert!(!provider_reserve_coordinates(&fenced, &hold));
        assert!(provider_audit_coordinates(&fenced, &hold));
        for changed in [
            json!({"grain":{"status":"5","generation":"8","reserved":"3"}}),
            json!({"grain":{"status":"5","generation":"9","reserved":"2"}}),
            json!({"grain":{"status":"6","generation":"9","reserved":"3"}}),
        ] {
            assert!(!provider_audit_coordinates(&changed, &hold));
        }
    }

    #[test]
    fn provider_profile_selects_one_pinned_service_without_cross_task_tariff() {
        let profile = json!({"providerMeterings":[
            {"providerResourceId":"7950","model":"bonsai2-27b-ptq1"},
            {"providerResourceId":"7951","model":"bonsai2-27b-ptq1"}]});
        assert_eq!(
            select_provider_metering(&profile, "7950").unwrap()["providerResourceId"],
            "7950"
        );
        assert_eq!(
            select_provider_metering(&profile, "7951").unwrap()["providerResourceId"],
            "7951"
        );
        assert!(select_provider_metering(&profile, "7952").is_err());
        let mut duplicate = profile.clone();
        duplicate["providerMeterings"][1]["providerResourceId"] = json!("7950");
        assert!(select_provider_metering(&duplicate, "7950").is_err());
        let mut mixed = profile;
        mixed["providerMetering"] = json!({"providerResourceId":"7950"});
        assert!(select_provider_metering(&mixed, "7950").is_err());
        let legacy = json!({"providerMetering":{"providerResourceId":"7004"}});
        assert_eq!(
            select_provider_metering(&legacy, "7004").unwrap()["providerResourceId"],
            "7004"
        );
    }

    #[test]
    fn provider_quote_metadata_preserves_scalar_v1_and_pins_multi_v2() {
        let mut pin: ProviderMeteringPin = serde_json::from_value(json!({
            "providerResourceId":"7004","model":"fixture","tariffVersion":"1",
            "tariffDigest":"123"
        }))
        .unwrap();
        assert_eq!(pin.metadata_version, 1);
        let scalar = provider_metering_metadata(&pin, 200, "application/json", "50").unwrap();
        assert_eq!(
            scalar,
            json!({"status":"200","contentType":"application/json","reserve":"50"})
        );
        assert!(scalar.get("version").is_none());
        pin.metadata_version = 2;
        let multi = provider_metering_metadata(&pin, 200, "application/json", "50").unwrap();
        assert_eq!(multi["version"], "2");
        assert_eq!(multi["providerResourceId"], "7004");
        assert_eq!(multi["reserve"], "50");
        pin.metadata_version = 3;
        assert!(provider_metering_metadata(&pin, 200, "application/json", "50").is_err());
    }

    #[test]
    fn configured_systemd_scope_uses_camel_case() {
        let command: AllowedCommand = serde_json::from_value(json!({
            "name":"hermes-acp","program":"/opt/mini/bwrap",
            "args":["--","/agent/hermes-acp"],"systemdScope":true,
            "reserve":"5","charge":"5"
        }))
        .unwrap();
        assert!(command.systemd_scope);
        assert!(serde_json::to_value(command)
            .unwrap()
            .get("systemdScope")
            .is_some());
        let legacy: AllowedCommand = serde_json::from_value(json!({
            "name":"hermes-acp","program":"/opt/mini/bwrap",
            "args":["--","/agent/hermes-acp"],"systemdScope":true,
            "reserve":"5","charge":"5"
        }))
        .unwrap();
        assert!(serde_json::to_value(&legacy)
            .unwrap()
            .get("wallTimeSeconds")
            .is_none());
        let mut bounded = legacy;
        bounded.wall_time_seconds = Some(1200);
        assert_eq!(
            serde_json::to_value(bounded).unwrap()["wallTimeSeconds"],
            json!(1200)
        );
    }

    #[test]
    fn provider_iteration_limit_preserves_default_and_refuses_invalid_values() {
        assert_eq!(provider_max_iterations(None).unwrap(), 6);
        assert_eq!(provider_max_iterations(Some(1)).unwrap(), 1);
        assert_eq!(provider_max_iterations(Some(2)).unwrap(), 2);
        assert_eq!(provider_max_iterations(Some(6)).unwrap(), 6);
        assert!(provider_max_iterations(Some(0)).is_err());
        assert!(provider_max_iterations(Some(7)).is_err());
    }

    #[test]
    fn provider_iteration_config_accepts_only_bounded_integer_form() {
        let base = json!({
            "task":"7004", "subject":"9", "capability":"101",
            "queryCapability":"101", "custodyKey":"/private/provider-task.key",
            "parentCapability":"75", "parentObserveCapability":"75",
            "reserve":"3", "charge":"0", "metering":true,
            "model":"pinned-model", "upstreamUrl":"https://example.test/v1/chat/completions",
            "providerKeyFile":"/private/provider.key", "gatewayBind":"127.0.0.1:18762",
            "maxRequestBytes":1048576, "maxResponseBytes":8388608,
            "timeoutSeconds":30
        });
        let omitted: ProviderTask = serde_json::from_value(base.clone()).unwrap();
        assert_eq!(provider_max_iterations(omitted.max_iterations).unwrap(), 6);
        let mut explicit = base;
        explicit["maxIterations"] = json!(2);
        let configured: ProviderTask = serde_json::from_value(explicit.clone()).unwrap();
        assert_eq!(
            provider_max_iterations(configured.max_iterations).unwrap(),
            2
        );
        assert_eq!(provider_required_network(&configured).unwrap(), "none");
        let mut fixture = configured.clone();
        fixture.local_fixture_host_network = true;
        assert!(provider_required_network(&fixture).is_err());
        fixture.upstream_url = "http://127.0.0.1:18762/v1/chat/completions".into();
        assert_eq!(provider_required_network(&fixture).unwrap(), "host");
        for invalid in [json!(-1), json!(1.5), json!("2"), json!(256)] {
            explicit["maxIterations"] = invalid;
            assert!(serde_json::from_value::<ProviderTask>(explicit.clone()).is_err());
        }
    }

    #[test]
    fn provider_network_route_is_launcher_positional_not_an_injected_argument() {
        let mut command: AllowedCommand = serde_json::from_value(json!({
            "name":"hermes-acp", "program":"/opt/mini/bwrap",
            "args":["--workspace","/work","--runtime-root","/agent-root",
                "--network","none","--","/agent/hermes-acp"],
            "systemdScope":true, "wallTimeSeconds":600,
            "reserve":"3", "charge":"0"
        }))
        .unwrap();
        assert!(provider_command_route(&command, "none"));
        assert!(!provider_command_route(&command, "host"));
        command.args[5] = "host".into();
        command.args.extend(["--network".into(), "none".into()]);
        assert!(!provider_command_route(&command, "none"));
        command.args[7] = "/agent/other".into();
        command.args.push("/agent/hermes-acp".into());
        assert!(!provider_command_route(&command, "host"));
    }

    #[test]
    fn legacy_launcher_cannot_arm_a_recoverable_worker() {
        // Even an executable that exits successfully is insufficient: the
        // paired bwrap launcher must advertise the exact gate ExecStart contract
        // before the controller creates a gate or child marker.
        assert!(Runtime::prove_launcher_gate(Path::new("/bin/true")).is_err());
    }

    #[test]
    fn acp_frame_refuses_oversized_line_before_json_allocation() {
        let bytes = vec![b'x'; MAX_ACP_FRAME + 1];
        let mut reader = io::BufReader::new(io::Cursor::new(bytes));
        let error = read_acp_frame(&mut reader).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("exceeds 1 MiB"));
    }

    #[test]
    fn retained_lookup_uses_next_native_retry_result() {
        let dir = std::env::temp_dir().join(format!("grain-retry-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        assert_eq!(next_retry_json(&dir).unwrap(), dir.join("retry-0001.json"));
        fs::write(dir.join("retry-0001.bin"), b"partial native retry").unwrap();
        assert_eq!(next_retry_json(&dir).unwrap(), dir.join("retry-0002.json"));
        fs::remove_dir_all(dir).unwrap();
    }

    #[test]
    fn hard_stop_reaps_a_descendant_after_the_group_leader_exits() {
        let mut command = Command::new("/bin/sh");
        command
            .arg("-c")
            .arg("sleep 30 & wait")
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        unsafe {
            command.pre_exec(|| {
                if libc::setsid() < 0 {
                    Err(io::Error::last_os_error())
                } else {
                    Ok(())
                }
            });
        }
        let mut child = command.spawn().expect("test group leader");
        let pgid = child.id() as i32;
        thread::sleep(Duration::from_millis(80));
        assert!(group_has_live_member(pgid).unwrap());
        signal_group(pgid, libc::SIGTERM).unwrap();
        for _ in 0..20 {
            if !group_has_live_member(pgid).unwrap() {
                break;
            }
            thread::sleep(Duration::from_millis(50));
        }
        if group_has_live_member(pgid).unwrap() {
            signal_group(pgid, libc::SIGKILL).unwrap();
        }
        assert!(
            !group_has_live_member(pgid).unwrap(),
            "descendant survived group stop"
        );
        child.wait().unwrap();
    }

    #[test]
    fn managed_law_candidates_recognize_only_own_prior_generation() {
        // Recorded 09-28 case: grain paused at generation 2 after a hard
        // fence, installed law still for generation 1 (this controller's).
        assert_eq!(managed_law_candidates("0", 3, Some(1)).unwrap(), vec![3, 2, 1]);
        // Without a journaled own install the stale law still refuses.
        assert_eq!(managed_law_candidates("0", 3, None).unwrap(), vec![3, 2]);
        // A journaled generation ahead of the grain is never accepted.
        assert_eq!(managed_law_candidates("5", 2, Some(4)).unwrap(), vec![2]);
        assert_eq!(managed_law_candidates("5", 2, Some(1)).unwrap(), vec![2, 1]);
        assert_eq!(managed_law_candidates("2", 2, Some(2)).unwrap(), vec![2]);
        assert!(managed_law_candidates("0", 0, None).is_err());
    }

    #[test]
    fn derived_effect_acknowledgement_covers_only_accounted_channels() {
        for note in [
            "worker operation 12 stopped after controller restart; external effects need acknowledgement",
            "controller restarted with a held allowance but no retained worker completion; effects require acknowledgement",
            "parent reserved operation may have external effects; explicit operator acknowledgement required",
            "Hermes prompt 9: ACP stream closed",
        ] {
            assert!(derivable_effect_note(note), "{note}");
        }
        for note in [
            "tool reserved operation may have external effects; explicit operator acknowledgement required",
            "delegated tool reservation fenced with uncertain external effects",
            "dispatch reservation survived controller restart; app delivery requires exact audit",
            "provider request 4 crossed durable send boundary before controller restart; upstream result uncertain",
            "parent confirmed reservation was externally settled; explicit effects acknowledgement required",
            "worker operation 12 stopped after controller restart; external effects need acknowledgement; and more",
        ] {
            assert!(!derivable_effect_note(note), "{note}");
        }
    }

    fn restart_resolution_fixture(tag: &str) -> (PathBuf, Runtime) {
        let root = std::env::temp_dir().join(format!(
            "grain-restart-resolution-{tag}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        let state = root.join("state");
        fs::create_dir(&state).unwrap();
        fs::set_permissions(&state, fs::Permissions::from_mode(0o700)).unwrap();
        let sim = root.join("sim");
        fs::create_dir(&sim).unwrap();
        fs::write(sim.join("status"), b"3").unwrap();
        fs::write(sim.join("lookup"), b"absent").unwrap();
        let mini = root.join("controlled-mini");
        let script = r#"#!/bin/sh
set -eu
sim='__SIM__'
command=$1
shift
dir=
intent=
attempt=
action=
while [ "$#" -gt 0 ]; do
  case "$1" in
    --dir) dir=$2; shift 2 ;;
    --intent) intent=$2; shift 2 ;;
    --attempt) attempt=$2; shift 2 ;;
    --action) action=$2; shift 2 ;;
    *) shift ;;
  esac
done
if [ "$command" = workspace ] && [ "$action" = recover ]; then
  n=1
  while [ -e "$attempt/retry-000$n.json" ]; do n=$((n + 1)); done
  printf lookup > "$attempt/retry-000$n.bin"
  if [ "$(cat "$sim/lookup")" = confirmed ]; then
    printf '%s\n' '{"type":"confirmed","confirmation":"replayed","imageBoundary":"300","transactionId":"21","eventId":"22","acceptedCount":"23"}' > "$attempt/retry-000$n.json"
    cat "$attempt/retry-000$n.json"
    exit 0
  fi
  printf '%s\n' '{"type":"absent"}' > "$attempt/retry-000$n.json"
  echo 'mini: host returned absent' >&2
  exit 1
fi
mkdir -p "$dir"
if [ "$command" = query ]; then
  status=$(cat "$sim/status")
  reserved=0
  [ "$status" = 3 ] && reserved=3
  printf '{"page":{"root":"100","grain":{"task":"7102","generation":"1","status":"%s","remaining":"10","reserved":"%s"}}}\n' "$status" "$reserved" > "$dir/view.json"
  printf '%s\n' '{"signing":[{"authorityRoot":"200"}],"imageBoundary":"300"}' > "$dir/challenge.json"
  exit 0
fi
[ "$command" = submit ] || exit 40
printf call > "$dir/call.bin"
printf outcome > "$dir/outcome.bin"
if grep -q '"type": "settle"' "$intent"; then
  printf 1 > "$sim/status"
elif grep -q '"type": "disconnect"' "$intent"; then
  printf 0 > "$sim/status"
fi
printf '%s\n' '{"type":"confirmed","confirmation":"installed","imageBoundary":"300","transactionId":"11","eventId":"12","acceptedCount":"13"}' > "$dir/outcome.json"
"#
        .replace("__SIM__", sim.to_str().unwrap());
        fs::write(&mini, script).unwrap();
        fs::set_permissions(&mini, fs::Permissions::from_mode(0o700)).unwrap();
        let host_config = root.join("host-config.json");
        fs::write(&host_config, b"{\"pinned\":true}").unwrap();
        let workspace = state.join("resource-workspace");
        for dir in [
            workspace.clone(),
            workspace.join("refs"),
            workspace.join("attempts"),
            workspace.join("sources"),
            workspace.join("proposals"),
        ] {
            fs::create_dir(&dir).unwrap();
            fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
        }
        let config: Config = serde_json::from_value(json!({
            "mini":mini,"host":root.join("host"),"hostConfig":host_config,
            "controlSocket":state.join("control.sock"),"custodyKey":root.join("parent.key"),
            "stateDir":state,"cwd":root,"task":"7101","subject":"7",
            "capability":"71","queryCapability":"74","policyControlCapability":"72",
            "commands":[],
            "toolTask":{"task":"7102","subject":"8","capability":"81",
                "queryCapability":"82","custodyKey":root.join("tool.key"),
                "parentCapability":"73","parentObserveCapability":"75",
                "reserve":"3","charge":"1","allowedPublications":[],
                "resourceWorkspace":workspace}
        }))
        .unwrap();
        let pinned = json!({"type":"minidregg-participant-workspace-v1",
            "host":config.host,"config":config.host_config,"key":root.join("tool.key"),
            "subject":"8","socket":null,"birthContext":null,"namespaceRoot":null});
        let pin_path = workspace.join("workspace.json");
        fs::write(&pin_path, serde_json::to_vec(&pinned).unwrap()).unwrap();
        fs::set_permissions(&pin_path, fs::Permissions::from_mode(0o600)).unwrap();
        let request = b"{\"type\":\"minidregg-workspace-proposal-v1\",\"action\":\"invoke\"}";
        let intent = b"{\"type\":\"intent\",\"field\":\"2\",\"value\":\"1\"}";
        write_new(&state.join("workspace-proposal-0000000000000001.json"), request).unwrap();
        let proposal = workspace.join("proposals").join("1");
        fs::create_dir(&proposal).unwrap();
        fs::write(proposal.join("intent.json"), intent).unwrap();
        let attempt = workspace.join("attempts").join("2");
        fs::create_dir(&attempt).unwrap();
        fs::set_permissions(&attempt, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(attempt.join("intent.json"), intent).unwrap();
        fs::write(attempt.join("config.json"), b"{\"pinned\":true}").unwrap();
        fs::write(attempt.join("call.bin"), b"exact signed call").unwrap();
        let mut runtime = Runtime::open(config, root.join("config.json")).unwrap();
        runtime.journal.next_operation_id = 3;
        runtime.process_first_operation_id = 3;
        runtime.journal.workspace_proposals.push(WorkspaceProposal {
            id: 1,
            request_sha256: sha256_bytes(request).unwrap(),
            intent_sha256: sha256_bytes(intent).unwrap(),
            submitted: true,
        });
        runtime.journal.workspace_attempt = Some(WorkspaceAttempt {
            operation_id: 2,
            proposal_id: 1,
            intent_sha256: sha256_bytes(intent).unwrap(),
            attempt,
            definite: false,
            no_submit: false,
        });
        runtime.journal.tool_hold = Some(HeldCharge {
            reserve: "3".into(),
            charge: "1".into(),
            before_generation: "1".into(),
            before_target_root: "100".into(),
            reserve_attempt: None,
            reserve_confirmed: true,
            reserve_refused: false,
            reserve_boundary: Some("300".into()),
            reserve_call_sha256: None,
            reserve_source_sha256: None,
            reserve_outcome_path: None,
            reserve_outcome_sha256: None,
            reserve_anchor: None,
        });
        runtime.save().unwrap();
        (root, runtime)
    }

    #[test]
    fn restart_lookup_absent_after_proven_stop_resolves_refused_and_settles() {
        let (root, mut runtime) = restart_resolution_fixture("stopped");
        runtime.prior_run_stopped = true;
        runtime.startup_recovery_active = true;
        let result = runtime.workspace_recover_operation(2, true).unwrap();
        assert_eq!(result["resolution"], "refused");
        assert_eq!(result["basis"], "absent-after-submitter-stop");
        assert_eq!(result["resolvedBy"], "restart-recovery");
        assert_eq!(result["outcome"]["type"], "absent");
        assert_eq!(result["toolCharge"], "1");
        assert!(runtime.journal.workspace_attempt.is_none());
        assert!(runtime.journal.tool_hold.is_none());
        let listed = runtime.workspace_attempts(&json!({})).unwrap();
        assert!(listed["pending"].is_null());
        assert_eq!(listed["resolutions"][0]["operationId"], "2");
        let one = runtime
            .workspace_attempts(&json!({"operationId":"2"}))
            .unwrap();
        assert_eq!(one["resolution"], "refused");
        // Journal validation accepts exactly one terminal record per ID.
        let config = runtime.config.clone();
        runtime.journal.validate_workspace(&config).unwrap();
        let mut forged = runtime.journal.clone();
        let duplicate = forged.workspace_resolutions[0].clone();
        forged.workspace_resolutions.push(duplicate);
        assert!(forged.validate_workspace(&config).is_err());
        let mut invented = runtime.journal.clone();
        invented.workspace_resolutions[0].resolution = "maybe".into();
        assert!(invented.validate_workspace(&config).is_err());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn restart_lookup_absent_without_stop_proof_is_uncertain_until_confirmed() {
        let (root, mut runtime) = restart_resolution_fixture("unproven");
        runtime.prior_run_stopped = false;
        let result = runtime.workspace_recover_operation(2, true).unwrap();
        assert_eq!(result["resolution"], "uncertain");
        assert_eq!(result["basis"], "absent-but-submitter-not-proven-stopped");
        assert_eq!(result["resolvedBy"], "lookup");
        assert!(runtime.journal.tool_hold.is_none());
        // Re-lookup never resubmits; a later confirmation upgrades it.
        let calls_before = fs::read(runtime.journal.workspace_resolutions[0].attempt.join("call.bin")).unwrap();
        let again = runtime
            .workspace_recover(&json!({"operationId":"2"}))
            .unwrap();
        assert_eq!(again["resolution"], "uncertain");
        fs::write(root.join("sim").join("lookup"), b"confirmed").unwrap();
        let upgraded = runtime
            .workspace_recover(&json!({"operationId":"2"}))
            .unwrap();
        assert_eq!(upgraded["resolution"], "performed");
        assert_eq!(upgraded["basis"], "later-exact-lookup");
        assert_eq!(upgraded["outcome"]["confirmation"], "replayed");
        assert_eq!(
            fs::read(runtime.journal.workspace_resolutions[0].attempt.join("call.bin")).unwrap(),
            calls_before
        );
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn restart_lookup_confirmed_resolves_performed() {
        let (root, mut runtime) = restart_resolution_fixture("confirmed");
        fs::write(root.join("sim").join("lookup"), b"confirmed").unwrap();
        runtime.prior_run_stopped = false;
        let result = runtime.workspace_recover_operation(2, true).unwrap();
        assert_eq!(result["resolution"], "performed");
        assert_eq!(result["basis"], "exact-lookup");
        assert_eq!(result["outcome"]["acceptedCount"], "23");
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn restart_without_call_needs_stop_proof_to_resolve_refused() {
        let (root, mut runtime) = restart_resolution_fixture("nocall");
        let attempt = runtime.journal.workspace_attempt.as_ref().unwrap().attempt.clone();
        fs::remove_file(attempt.join("call.bin")).unwrap();
        runtime.prior_run_stopped = false;
        assert!(runtime.workspace_recover_operation(2, true).is_err());
        assert!(runtime.journal.workspace_attempt.is_some());
        runtime.prior_run_stopped = true;
        let result = runtime.workspace_recover_operation(2, true).unwrap();
        assert_eq!(result["resolution"], "refused");
        assert_eq!(result["basis"], "no-call-after-submitter-stop");
        assert_eq!(result["toolCharge"], "0");
        fs::remove_dir_all(&root).unwrap();
    }
}
