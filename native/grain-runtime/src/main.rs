//! Physical controller for one Mini agent-grain task. Semantic admission is
//! exclusively a signed call to the native Lean host through `mini`.
mod application_tools;
#[cfg(test)]
mod birth_lifecycle_tests;
mod control;
mod custody_gate;
mod legacy_custody_audit;
mod mcp;
mod provider;
mod provider_profile;
#[cfg(test)]
mod publication_refusal_tests;
mod resource_tools;
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
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_birth_families: Vec<resource_tools::AllowedBirthFamily>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_application_families: Vec<application_tools::ApplicationFamily>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    allowed_session_families: Vec<application_tools::SessionFamily>,
    /// Explicit operator enablement for the qualified current-author Host
    /// image. The family allowlists alone never enable op30/31 delivery.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    current_birth_host_sha256: Option<String>,
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
    provider_hold: Option<HeldCharge>,
    #[serde(default)]
    provider_attempt: Option<ProviderAttempt>,
    #[serde(default)]
    provider_settlement: Option<ProviderSettlement>,
    /// Bounded exact-body replay for completed responses in the current ACP
    /// prompt. SDK retries receive these bytes without another upstream send.
    #[serde(default)]
    provider_replays: Vec<ProviderReplay>,
    /// Confirmed native publication receipts retained independently of ACP
    /// tool-result delivery. Never synthesize a tool response from this list.
    #[serde(default)]
    publication_receipts: Vec<PublicationReceipt>,
    /// Ordinals are consumed before dispatch, including definitive refusals.
    /// An uncertain pending attempt prevents allocating another ID.
    #[serde(default)]
    birth_next_ordinal: BTreeMap<String, u16>,
    #[serde(default)]
    birth_operation: Option<BirthOperation>,
    #[serde(default)]
    birth_pending: Option<BirthPending>,
    #[serde(default)]
    born_resources: Vec<BornResourceRecord>,
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
struct PublicationPending {
    prompt_operation_id: u64,
    session_id: String,
    source_sha256: String,
    targets: Vec<String>,
}

#[derive(Clone, Serialize, Deserialize, Debug)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PublicationReceipt {
    prompt_operation_id: u64,
    session_id: String,
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
    authored_intent_sha256: Option<String>,
    tool_view: Value,
    parent_view: Value,
    prompt_operation_id: u64,
    session_id: String,
}

#[derive(Clone, Copy, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum ApplicationBirthRoute {
    Application,
    Session,
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
    targets: &[String],
) -> Result<&'a PublicationReceipt> {
    let mut matching = records.iter().filter(|record| {
        !prior_operation_ids.contains(&record.operation_id)
            && record.prompt_operation_id == prompt_operation_id
            && record.session_id == session_id
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
            AuthoritySlot::Provider => &self.provider_pending,
        }
    }
    fn pending_for_mut(&mut self, slot: AuthoritySlot) -> &mut Option<Pending> {
        match slot {
            AuthoritySlot::Parent => &mut self.pending,
            AuthoritySlot::Tool => &mut self.tool_pending,
            AuthoritySlot::Provider => &mut self.provider_pending,
        }
    }
    fn hold_for(&self, slot: AuthoritySlot) -> &Option<HeldCharge> {
        match slot {
            AuthoritySlot::Parent => &self.parent_hold,
            AuthoritySlot::Tool => &self.tool_hold,
            AuthoritySlot::Provider => &self.provider_hold,
        }
    }
    fn hold_for_mut(&mut self, slot: AuthoritySlot) -> &mut Option<HeldCharge> {
        match slot {
            AuthoritySlot::Parent => &mut self.parent_hold,
            AuthoritySlot::Tool => &mut self.tool_hold,
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
            provider_hold: None,
            provider_attempt: None,
            provider_settlement: None,
            provider_replays: Vec::new(),
            publication_receipts: Vec::new(),
            birth_next_ordinal: BTreeMap::new(),
            birth_operation: None,
            birth_pending: None,
            born_resources: Vec::new(),
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
            &t.allowed_birth_families,
            &t.allowed_reads,
            &t.allowed_publications,
            &peer_targets,
            &peer_capabilities,
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
    completion_phase: Arc<AtomicU8>,
    current_unit: Arc<Mutex<Option<(String, PathBuf)>>>,
    provider_control: Arc<Mutex<Option<provider::GatewayControl>>>,
    provider_lease: Option<provider::LeaseId>,
    prompt_active: bool,
    output: Option<control::OutputHandle>,
}

impl Runtime {
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
            j
        } else {
            let j = Journal::fresh(binding);
            atomic_json(&path, &j)?;
            j
        };
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
            completion_phase: Arc::new(AtomicU8::new(PHASE_IDLE)),
            current_unit: Arc::new(Mutex::new(None)),
            provider_control: Arc::new(Mutex::new(None)),
            provider_lease: None,
            prompt_active: false,
            output: None,
        };
        // We have no live Child handle after a controller crash. A recycled
        // PID/PGID must never be killed. Fence the task and refuse new work.
        if rt.journal.child.is_some()
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
                application_tools::plan_session_birth(
                    family,
                    tool,
                    &self.config.task,
                    &app_record.pending.born.target,
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
            .cloned()
            .collect();
        if pending.is_empty()
            && self
                .journal
                .born_resources
                .iter()
                .all(|record| record.reported)
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
            .filter(|record| !record.reported)
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
    fn renew_worker_policy(&mut self, attaching_from_paused: bool) -> Result<()> {
        let mut workers = Vec::new();
        if let Some(tool) = &self.config.tool_task {
            workers.push(tool.subject.clone());
        }
        if let Some(provider) = &self.config.provider_task {
            if workers.iter().any(|subject| subject == &provider.subject) {
                return Err("provider and tool witness subjects must be distinct".into());
            }
            workers.push(provider.subject.clone());
        }
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
        let candidates = if status == "0" {
            let paused_generation = current_generation
                .checked_sub(1)
                .ok_or("paused generation has no prior value")?;
            let mut values = vec![current_generation];
            if let Some(prior) = paused_generation.checked_sub(1) {
                values.push(prior);
            }
            values
        } else {
            vec![current_generation]
        };
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
            let source = if workers.len() == 1 {
                json!({"owner":self.config.subject,"workerSubject":workers[0],
                    "workerGeneration":candidate.to_string()})
            } else {
                json!({"owner":self.config.subject,"workerSubjects":workers,
                    "workerGeneration":candidate.to_string()})
            };
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
        let provider_evidence = if slot == AuthoritySlot::Provider {
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
            let child = self
                .journal
                .child
                .as_ref()
                .ok_or("publication has no worker")?;
            let session = self
                .journal
                .hermes_session
                .as_ref()
                .ok_or("publication has no retained Hermes session")?;
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
            Some((child.operation_id, session.id.clone(), targets))
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
                |(prompt_operation_id, session_id, targets)| -> Result<PublicationPending> {
                    Ok(PublicationPending {
                        prompt_operation_id,
                        session_id,
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
        let metering = profile
            .get("providerMetering")
            .ok_or("pinned Host profile has no provider metering tariff")?;
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
        let metadata = json!({"status":status.to_string(),"contentType":content_type,
            "reserve":hold.reserve.clone()});
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
        let metadata = json!({"status":status.to_string(),"contentType":content_type,
            "reserve":reserve});
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
        self.journal.birth_operation = None;
        self.save()
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
        // A caller-selected application must already be a complete exact
        // locally accepted bundle. Reject an unknown/stale selector before
        // consuming an ordinal, attaching, or holding any allowance.
        let selected_app_birth = if route == Some(ApplicationBirthRoute::Session) {
            let family = tool
                .allowed_session_families
                .iter()
                .find(|family| family.name == family_name)
                .ok_or("session family is not allowlisted")?;
            let name = selected_application
                .as_deref()
                .ok_or("session application selector absent")?;
            let record = self
                .journal
                .born_resources
                .iter()
                .find(|record| {
                    record.pending.route == Some(ApplicationBirthRoute::Application)
                        && record.pending.family == family.application_family
                        && record.pending.born.name == name
                })
                .ok_or("session application has no confirmed local birth")?;
            self.verify_born_record(record)?;
            Some(record.pending.born.clone())
        } else {
            None
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
        let prompt_operation_id = self
            .journal
            .child
            .as_ref()
            .ok_or("resource birth has no active worker")?
            .operation_id;
        let session_id = self
            .journal
            .hermes_session
            .as_ref()
            .ok_or("resource birth has no retained Hermes session")?
            .id
            .clone();
        let next_ordinal = ordinal.checked_add(1).ok_or("birth ordinal exhausted")?;
        self.journal
            .birth_next_ordinal
            .insert(family_name.to_owned(), next_ordinal);
        self.journal.birth_operation = Some(BirthOperation {
            family: family_name.to_owned(),
            ordinal,
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
                let app = selected_app_birth
                    .as_ref()
                    .ok_or("session application selection disappeared")?;
                let read = resource_tools::born_read(app);
                let read_nonce = self.next_id()?;
                let observation =
                    resource_tools::read_resource(&self.config, &tool, &read, read_nonce)?;
                if observation.get("target").and_then(Value::as_str) != Some(app.target.as_str()) {
                    return Err("fresh signed application read differs from retained birth".into());
                }
                application_tools::plan_session_birth(
                    family,
                    &tool,
                    &self.config.task,
                    &app.target,
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
            authored_intent_sha256,
            tool_view,
            parent_view,
            prompt_operation_id,
            session_id,
        };
        origin.validate_members()?;
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

    fn tool_call(&mut self, name: &str, arguments: &Value) -> Result<Value> {
        if self.cancelled.load(Ordering::SeqCst)
            || self.journal.connection == Connection::Fenced
            || self.journal.child.is_none()
            || self.journal.pending.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || !self.prompt_active
        {
            return Err("Hermes task is not running under this controller".into());
        }
        if self.journal.tool_pending.is_some()
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
                resource_tools::read_resource(&self.config, &configured, &read, nonce)
            }
            "mini_create_resource" => self.create_resource(arguments, None),
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
                let prompt_operation_id = self
                    .journal
                    .child
                    .as_ref()
                    .ok_or("publication has no active worker")?
                    .operation_id;
                let session_id = self
                    .journal
                    .hermes_session
                    .as_ref()
                    .ok_or("publication has no retained Hermes session")?
                    .id
                    .clone();
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
                    &target_ids,
                )?;
                tool_view["publicationReceipt"] = publication_receipt_json(receipt);
                Ok(tool_view)
            }
            _ => Err("tool is not delegated".into()),
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
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
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
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
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
        let provider_retry = self.retry_pending_slot(AuthoritySlot::Provider);
        let tool_fenced = tool_retry.and_then(|_| self.fence_tool());
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
        match (stopped.and(custody_stopped), fenced, tool_fenced, provider_fenced) {
            (Ok(()), Ok(()), Ok(()), Ok(())) => {
                self.journal.connection = Connection::Detached;
                self.journal.hard_reconnect_pending = false;
                self.journal.prompt_witness = None;
                self.save()
            }
            (a, b, c, d) => Err(format!(
                "hard disconnect unresolved: local stop={a:?}; Mini fence={b:?}; tool fence={c:?}; provider fence={d:?}"
            )),
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
            || self.journal.child.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
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
                Ok(Input::Admin(request)) => {
                    let _ = request
                        .reply
                        .send("worker is running; stop and fence it first".into());
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
                    if !seen.insert(&record.pending.born.name) {
                        return Err("duplicate confirmed application name".into());
                    }
                    if applications.len() < 64 {
                        applications.push(record.pending.born.name.clone());
                    }
                }
            }
            applications.reverse();
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
            || self.journal.child.is_some()
            || self.journal.settlement_due.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
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
        self.mark_hold(false, &spec.reserve, &spec.charge)?;
        self.transition(
            json!({"type":"reserve","amount":spec.reserve}),
            "reserve",
            "hermes-acp prompt",
        )?;
        let parent = self.query()?;
        let before = parent.get("grain").ok_or("reserved parent grain absent")?;
        if before.get("status").and_then(Value::as_str) != Some("3")
            && before.get("status").and_then(Value::as_str) != Some("4")
        {
            return Err("parent grain is not reserved after prompt allowance".into());
        }
        self.journal.prompt_witness = Some(json!({"task":self.config.task,
            "expectedTargetRoot":parent.get("targetRoot").ok_or("parent root absent")?,
            "before":{"generation":before.get("generation"),"status":before.get("status"),
                "remaining":before.get("remaining"),"reserved":before.get("reserved")}}));
        self.save()?;
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
        loop {
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
                Ok(Input::Admin(request)) => {
                    let _ = request
                        .reply
                        .send("Hermes is running; stop and fence it first".into());
                }
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
            let msg = match rx.recv_timeout(Duration::from_millis(20)) {
                Ok(Ok(v)) => v,
                Ok(Err(e)) => return Err(format!("ACP wire: {e}")),
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    return Err("Hermes ACP stream closed".into())
                }
                Err(mpsc::RecvTimeoutError::Timeout) => continue,
            };
            if msg.get("id") == Some(&json!(id)) {
                if let Some(error) = msg.get("error") {
                    return Err(format!("Hermes ACP: {error}"));
                }
                if let Some(result) = msg.get("result") {
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
        self.retry_pending(true)?;
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
            provider_fence?;
            self.journal.connection = Connection::Detached;
            self.journal.hard_reconnect_pending = false;
            self.journal.prompt_witness = None;
            self.save()?;
        }
        Ok(())
    }
    fn reconcile_hold(&mut self, tool: bool, audited: bool) -> Result<()> {
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
        if !audited
            && observed.get("imageBoundary").and_then(Value::as_str)
                != hold.reserve_boundary.as_deref()
        {
            return Err("intervening Mini events prevent automatic reservation identity proof; use audited admin reconciliation after reviewing exact attempts".into());
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
    fn acknowledge_effects(&mut self) -> Result<()> {
        if self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.parent_hold.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
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
            "action":"acknowledge-external-effects","stage":"acknowledged",
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
                            "reserve" | "tool reserve" | "provider reserve"
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
                "reserve" | "tool reserve" | "provider reserve"
            ) {
                self.record_reserve_confirmation(slot, &p.attempt, &retry_result)?;
            }
            if matches!(
                p.operation.as_str(),
                "settle"
                    | "tool settle"
                    | "tool release"
                    | "reconcile settle"
                    | "provider settle"
                    | "provider audit settle"
            ) {
                if let Some(record) = provider_settlement {
                    self.journal.provider_settlement = Some(record);
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
    TerminalLine { attachment_id: u64, line: String },
    Disconnect,
    SoftDetach,
    Admin(control::AdminRequest),
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
    });
    clear_stale_control_socket(&rt.config.control_socket)?;
    let server = control::start(&rt.config.control_socket, interrupt)?;
    let admin_path = rt.config.state_dir.join("admin.sock");
    clear_stale_control_socket(&admin_path)?;
    let admin = control::start_admin(&admin_path)?;
    rt.output = Some(server.output_handle());
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
    thread::spawn(move || {
        let _server = &server;
        let mut current = None;
        while let Ok(event) = server.events.recv() {
            let message = match event {
                control::Event::Attached { id, soft } => {
                    current = Some(id);
                    Input::Line(if soft { "attach soft" } else { "attach hard" }.into())
                }
                control::Event::Line { id, text } if current == Some(id) => {
                    if text.starts_with("terminal ") {
                        Input::TerminalLine {
                            attachment_id: id,
                            line: text,
                        }
                    } else {
                        Input::Line(text)
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
                            terminal::state(&journal, attachment, request),
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
                let outcome = match request.command.as_str() {
                    "reconcile parent" => rt.reconcile_hold(false, false),
                    "reconcile tool" => rt.reconcile_hold(true, false),
                    "reconcile parent audited" => rt.reconcile_hold(false, true),
                    "reconcile tool audited" => rt.reconcile_hold(true, true),
                    "reconcile provider audited" => rt.reconcile_provider_audited(),
                    "reconcile provider abort" => rt.abort_refused_provider_request(),
                    "reconcile parent abort" => rt.abort_unsubmitted_hold(false),
                    "reconcile tool abort" => rt.abort_unsubmitted_hold(true),
                    "reconcile tool legacy b44" => legacy_custody_audit::audit_b44(&mut rt),
                    "reconcile tool legacy zero" => legacy_custody_audit::settle_b44_zero(&mut rt),
                    "reconcile effects" => rt.acknowledge_effects(),
                    "reconcile worker audited" => rt.reconcile_worker_audited(),
                    _ => Err("unknown admin reconciliation action".into()),
                };
                request.phase.store(2, Ordering::SeqCst);
                let _ = request.reply.send(match &outcome {
                    Ok(()) => "ok".into(),
                    Err(error) => format!("error: {error}"),
                });
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
                            terminal::completion(&journal, attachment, request, result.is_ok()),
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
        eprintln!("usage: grain-runtime serve /absolute/config.json | connect /absolute/socket [hard|soft] | terminal /absolute/socket [hard|soft] | admin /absolute/stateDir/admin.sock 'reconcile parent|tool|effects|worker audited' | mcp-stdio /absolute/socket");
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
            authored_intent_sha256: None,
            tool_view: json!({}),
            parent_view: json!({}),
            prompt_operation_id: 1,
            session_id: "s".into(),
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
                allowed_birth_families: vec![],
                allowed_application_families: vec![],
                allowed_session_families: vec![],
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
            &ids
        )
        .is_err());
        assert!(current_publication_receipt(
            &runtime.journal.publication_receipts,
            &prior,
            41,
            "wrong-session",
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
}
