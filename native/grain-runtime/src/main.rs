//! Physical controller for one Mini agent-grain task. Semantic admission is
//! exclusively a signed call to the native Lean host through `mini`.
mod control;
mod mcp;
mod provider;
mod provider_profile;
mod resource_tools;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
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
    model: String,
    upstream_url: String,
    provider_key_file: PathBuf,
    gateway_bind: String,
    max_request_bytes: usize,
    max_response_bytes: usize,
    timeout_seconds: u64,
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

fn exact_provider_reserve(state: &Value, hold: &HeldCharge) -> bool {
    hold.reserve_confirmed
        && hold.reserve_boundary.as_deref().is_some_and(|boundary| {
            state.get("imageBoundary").and_then(Value::as_str) == Some(boundary)
        })
        && state.pointer("/grain/status").and_then(Value::as_str) == Some("3")
        && state.pointer("/grain/reserved").and_then(Value::as_str) == Some(hold.reserve.as_str())
        && state.pointer("/grain/generation").and_then(Value::as_str)
            == Some(hold.before_generation.as_str())
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
        if !command.program.is_absolute() || command.program == c.mini || command.program == c.host
        {
            return Err(format!("invalid executable for {}", command.name));
        }
        if command.systemd_scope
            && command.program.file_name().and_then(|s| s.to_str()) != Some("bwrap")
        {
            return Err("systemdScope requires the grain-host bwrap launcher".into());
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
    }
    if let Some(p) = &c.provider_task {
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
        let bind = p
            .gateway_bind
            .parse::<std::net::SocketAddr>()
            .map_err(|_| "providerTask.gatewayBind must be a socket address")?;
        if !bind.ip().is_loopback() || bind.port() == 0 {
            return Err("providerTask.gatewayBind must pin a loopback port".into());
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
        if !c.commands.iter().any(|command| {
            command.systemd_scope
                && command.args.iter().any(|arg| arg == "--network")
                && command.args.iter().any(|arg| arg == "host")
        }) {
            return Err(
                "providerTask requires an explicit scoped host-network Hermes command".into(),
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
    fn worker_env(&self, command: &mut Command, unit: &Option<String>, broker: Option<&Path>) {
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
            if let Some(tool) = &self.config.tool_task {
                command.env("MINI_GRAIN_TOOL_CUSTODY_KEY", &tool.custody_key);
            }
            if let Some(provider) = &self.config.provider_task {
                command.env("MINI_GRAIN_PROVIDER_CUSTODY_KEY", &provider.custody_key);
                command.env("MINI_GRAIN_PROVIDER_KEY_FILE", &provider.provider_key_file);
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
            "imageBoundary":challenge.get("imageBoundary")}),
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
    fn renew_worker_policy(&mut self) -> Result<()> {
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
        if !matches!(status, "1" | "2") {
            return Err("parent is not attached for policy renewal".into());
        }
        let policy = self.query_policy()?;
        let view = policy.get("view").ok_or("signed policy view absent")?;
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
        };
        *self.journal.hold_for_mut(slot) = Some(hold);
        self.save()
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
        let attempt = self.config.state_dir.join(format!("attempt-{id:016}"));
        let source_path = self.config.state_dir.join(format!("source-{id:016}.json"));
        write_new(
            &source_path,
            serde_json::to_string_pretty(&source).unwrap().as_bytes(),
        )?;
        let pending = Some(Pending {
            operation_id: id,
            operation: label.into(),
            attempt: attempt.clone(),
            uncertain: false,
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
        let result = self.command_output(&cfg.mini, &args);
        match result {
            Ok(()) => {
                if reserving {
                    let receipt: Value = serde_json::from_slice(
                        &fs::read(attempt.join("outcome.json"))
                            .map_err(|e| format!("reserve receipt missing: {e}"))?,
                    )
                    .map_err(|e| format!("reserve receipt invalid: {e}"))?;
                    if receipt.get("type").and_then(Value::as_str) != Some("confirmed") {
                        return Err("native reserve returned without confirmed receipt".into());
                    }
                    let boundary = receipt
                        .get("imageBoundary")
                        .and_then(Value::as_str)
                        .ok_or("reserve receipt lacks image boundary")?
                        .to_owned();
                    let hold = self
                        .journal
                        .hold_for_mut(slot)
                        .as_mut()
                        .ok_or("reserve marker disappeared")?;
                    hold.reserve_confirmed = true;
                    hold.reserve_boundary = Some(boundary);
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
                    // A missing file after subprocess exit is still not a
                    // negative native receipt: an older client/host could
                    // have sent the call before its directory entry became
                    // durable. Keep the exact pending attempt and hold.
                    if let Some(p) = self.journal.pending_for_mut(slot) {
                        p.uncertain = true;
                    }
                    self.save()?;
                    return Err(format!("{label} has no retained call.bin after custody failure; disposition requires audit: {e}"));
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
    fn handle_tool(&mut self, request: mcp::BrokerRequest) {
        if request.prompt_epoch != 1 {
            let _ = request.reply.send(json!({"isError":true,
                "text":"tool request was queued outside the active prompt"}));
            return;
        }
        let outcome = self.tool_call(&request.name, &request.arguments);
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
                let recorded = self.provider_record_outcome(attempt_id, outcome);
                let settle = recorded.as_ref().ok().copied().flatten();
                let _ = reply.send(recorded.map(|_| ()));
                if let Some(charge) = settle {
                    if let Err(error) = self.provider_settle(charge) {
                        eprintln!("provider fixed-charge settlement unresolved: {error}");
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
        if self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
        {
            return Err("prior provider request needs exact reconciliation".into());
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
        Ok(provider::ForwardPermit {
            attempt_id: id,
            lease: request.lease,
            exact_body: request.exact_body,
        })
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
            || !exact_provider_reserve(&provider_state, hold)
        {
            return Err(
                "signed parent or exact provider reserve boundary changed before upstream send"
                    .into(),
            );
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
        let (kind, bytes, charge) = match outcome {
            provider::ProviderOutcome::Received {
                status,
                content_type,
                exact_body,
            } => {
                if !attempt.send_started {
                    return Err("provider response without durable send boundary".into());
                }
                (
                    format!("received:{status}:{content_type}"),
                    exact_body,
                    Some("configured"),
                )
            }
            provider::ProviderOutcome::NotSent { reason } => {
                (format!("not-sent:{reason}"), Vec::new(), Some("0"))
            }
            provider::ProviderOutcome::Uncertain {
                partial_body,
                reason,
            } => (format!("uncertain:{reason}"), partial_body, None),
        };
        let path = self
            .config
            .state_dir
            .join(format!("provider-{attempt_id:016}.controller-outcome"));
        write_new(&path, &bytes)?;
        let digest = sha256_file(&path)?;
        let attempt = self
            .journal
            .provider_attempt
            .as_mut()
            .ok_or("provider attempt disappeared before outcome journal")?;
        attempt.outcome_path = Some(path);
        attempt.outcome_bytes = Some(bytes.len());
        attempt.outcome_sha256 = Some(digest);
        attempt.outcome = Some(kind.clone());
        if charge.is_none() {
            self.journal.unresolved_external.push(format!(
                "provider request {attempt_id} may have reached upstream; exact response uncertain"
            ));
        }
        self.save()?;
        Ok(charge)
    }
    fn provider_settle(&mut self, charge: &str) -> Result<()> {
        let authority = self.provider()?;
        let configured = self
            .config
            .provider_task
            .as_ref()
            .ok_or("providerTask absent")?;
        let charge = if charge == "configured" {
            configured.charge.clone()
        } else {
            charge.to_owned()
        };
        if self.journal.provider_pending.is_some() {
            return Err("provider transition needs exact retry".into());
        }
        self.transition_as(
            &authority,
            json!({"type":"settle","charge":charge}),
            "provider settle",
            "gateway fixed-charge settlement",
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
    fn tool_call(&mut self, name: &str, arguments: &Value) -> Result<Value> {
        if self.cancelled.load(Ordering::SeqCst)
            || self.journal.connection == Connection::Fenced
            || self.journal.child.is_none()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || !self.prompt_active
        {
            return Err("Hermes task is not running under this controller".into());
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
                let read =
                    resource_tools::select_read(&configured.allowed_reads, arguments)?.clone();
                let nonce = self.next_id()?;
                resource_tools::read_resource(&self.config, &configured, &read, nonce)
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
                    let allowed = tool
                        .allowed_publications
                        .iter()
                        .find(|g| g.kind == kind && g.target == target)
                        .ok_or("publication target is not delegated")?;
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
                    if self.journal.tool_pending.is_none() && !self.cancelled.load(Ordering::SeqCst)
                    {
                        let release = self.transition_as(
                            &authority,
                            json!({"type":"settle","charge":"0"}),
                            "tool release",
                            "definitively refused publication",
                            vec![],
                        );
                        if release.is_ok() {
                            let _ = self.transition_as(
                                &authority,
                                json!({"type":"disconnect"}),
                                "tool disconnect",
                                "refused publication cleanup",
                                vec![],
                            );
                        }
                    }
                    return Err(error);
                }
                self.check_not_cancelled()?;
                self.transition_as(
                    &authority,
                    json!({"type":"disconnect"}),
                    "tool disconnect",
                    "Hermes delegated tool detach",
                    vec![],
                )?;
                self.query_as(&authority)
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
        self.emit("hard transport attached to soft reservation; loss will cancel the task\n");
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
        self.transition(op, "attach", "controller attach")?;
        self.renew_worker_policy()?;
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
        let soft_reserved = self.journal.connection == Connection::Soft;
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
                    if soft_reserved {
                        json!({"type":"cancel"})
                    } else {
                        json!({"type":"disconnect"})
                    },
                    "disconnect",
                    "hard connection lost",
                )
            }
        });
        match (stopped, fenced, tool_fenced, provider_fenced) {
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
        self.worker_env(&mut command, &unit, None);
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
                Ok(Input::Line(_)) => eprintln!("command running; only disconnect is accepted"),
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
                    upstream_url: task.upstream_url.clone(),
                    pinned_model: task.model.clone(),
                    provider_key: key,
                    private_dir: self.config.state_dir.clone(),
                    max_request_bytes: task.max_request_bytes,
                    max_response_bytes: task.max_response_bytes,
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
        let unit = self.worker_unit(id, &spec);
        if let Some(unit) = &unit {
            Self::prove_launcher_gate(&spec.program)?;
            self.launch_gate(&spec.program, unit, "init")?;
        }
        let broker_path = self.config.state_dir.join(format!("mcp-{id:016}.sock"));
        let broker = mcp::start_broker(&broker_path)?;
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
        self.worker_env(&mut command, &unit, Some(&broker_path));
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
                    current.pending_prompt = false;
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
        let outcome = match &session {
            Ok(session_id) => {
                self.prompt_active = true;
                let prompt_sent = (|| -> Result<()> {
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
                        active.endpoint.control().activate(provider::Lease {
                            id: lease_id.clone(),
                            worker_token: active.token.clone(),
                        })?;
                        self.provider_lease = Some(lease_id);
                    }
                    broker.activate_prompt();
                    acp_send(
                        &mut child_stdin,
                        3,
                        "session/prompt",
                        json!({
                            "sessionId":session_id,"prompt":[{"type":"text","text":prompt}]
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
                    Ok(request) => self.handle_tool(request),
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
                Ok(Input::Line(_)) => {
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
        self.retry_pending(true)?;
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
            if matches!(status, "1" | "3") {
                self.transition(
                    json!({"type":"disconnect"}),
                    "disconnect",
                    "recovered hard connection loss",
                )?;
            } else if matches!(status, "2" | "4") {
                self.transition(
                    json!({"type":"cancel"}),
                    "cancel",
                    "recovered hard transport loss during soft reservation",
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
            let op = if status == "3" {
                json!({"type":"disconnect"})
            } else {
                json!({"type":"cancel"})
            };
            self.transition_as(
                &authority,
                op,
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
        let attempt = self
            .journal
            .provider_attempt
            .clone()
            .ok_or("no durable provider request for audit")?;
        let request = fs::read(&attempt.request_path)
            .map_err(|e| format!("retained provider request absent: {e}"))?;
        if request.is_empty()
            || request.len() > task.max_request_bytes
            || request.len() != attempt.request_bytes
            || sha256_file(&attempt.request_path)? != attempt.request_sha256
        {
            return Err("retained provider request differs from durable exact bytes".into());
        }
        if attempt.outcome.is_some() != attempt.outcome_path.is_some() {
            return Err("provider outcome journal has incomplete evidence binding".into());
        }
        if let Some(path) = &attempt.outcome_path {
            let meta =
                fs::metadata(path).map_err(|e| format!("provider outcome evidence absent: {e}"))?;
            if meta.len() > task.max_response_bytes as u64
                || Some(meta.len() as usize) != attempt.outcome_bytes
                || Some(sha256_file(path)?) != attempt.outcome_sha256
            {
                return Err("provider outcome evidence differs from durable exact bytes".into());
            }
        }
        let id = self.next_id()?;
        self.journal.reconciliation_log.push(json!({
            "decisionId":id.to_string(), "authority":"provider",
            "action":"settle-provider-fixed-charge", "stage":"operator-audited-requested",
            "providerAttemptId":attempt.id.to_string(),
            "requestPath":attempt.request_path,
            "requestBytes":attempt.request_bytes,
            "requestSha256":attempt.request_sha256,
            "outcomePath":attempt.outcome_path,
            "outcomeBytes":attempt.outcome_bytes,
            "outcomeSha256":attempt.outcome_sha256,
            "sendBoundaryDurable":attempt.send_started,
            "outcome":attempt.outcome,
            "configuredCharge":task.charge,
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
                let charge = if !attempt.send_started
                    || attempt
                        .outcome
                        .as_deref()
                        .is_some_and(|kind| kind.starts_with("not-sent:"))
                {
                    "0".to_owned()
                } else {
                    task.charge.clone()
                };
                self.transition_as(
                    &authority,
                    json!({"type":"settle","charge":charge}),
                    "provider audit settle",
                    "operator audited fixed provider charge",
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
            if matches!(
                p.operation.as_str(),
                "reserve" | "tool reserve" | "provider reserve"
            ) {
                let receipt: Value =
                    serde_json::from_slice(&fs::read(&retry_result).map_err(|e| e.to_string())?)
                        .map_err(|e| e.to_string())?;
                if receipt.get("type").and_then(Value::as_str) != Some("confirmed") {
                    return Err("reserve lookup did not confirm exact attempt".into());
                }
                let boundary = receipt
                    .get("imageBoundary")
                    .and_then(Value::as_str)
                    .ok_or("reserve lookup lacks image boundary")?
                    .to_owned();
                let hold = self
                    .journal
                    .hold_for_mut(slot)
                    .as_mut()
                    .ok_or("reserve lookup has no held-charge marker")?;
                hold.reserve_confirmed = true;
                hold.reserve_boundary = Some(boundary);
            }
            *self.journal.pending_for_mut(slot) = None;
            if matches!(
                p.operation.as_str(),
                "settle"
                    | "tool settle"
                    | "tool release"
                    | "reconcile settle"
                    | "provider settle"
                    | "provider audit settle"
            ) {
                *self.journal.hold_for_mut(slot) = None;
                if slot == AuthoritySlot::Parent {
                    self.journal.settlement_due = None;
                }
            }
            if p.operation == "disconnect" && slot == AuthoritySlot::Parent {
                self.journal.connection = Connection::Detached;
            }
            self.save()?;
        }
        Ok(())
    }
}

enum Input {
    Line(String),
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
                control::Event::Line { id, text } if current == Some(id) => Input::Line(text),
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
            Input::Disconnect => rt.disconnect(),
            Input::SoftDetach => Ok(()),
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
        eprintln!("usage: grain-runtime serve /absolute/config.json | connect /absolute/socket [hard|soft] | admin /absolute/stateDir/admin.sock 'reconcile parent|tool|effects|worker audited' | mcp-stdio /absolute/socket");
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
    fn provider_send_requires_exact_confirmed_reserve_boundary() {
        let hold = HeldCharge {
            reserve: "3".into(),
            charge: "1".into(),
            before_generation: "4".into(),
            before_target_root: "old-root".into(),
            reserve_attempt: None,
            reserve_confirmed: true,
            reserve_refused: false,
            reserve_boundary: Some("accepted-reserve-image".into()),
        };
        let current = json!({"grain":{"status":"3","reserved":"3","generation":"4"},
            "imageBoundary":"accepted-reserve-image"});
        assert!(exact_provider_reserve(&current, &hold));
        let mut replaced = current.clone();
        replaced["imageBoundary"] = json!("later-same-amount-reserve");
        assert!(!exact_provider_reserve(&replaced, &hold));
        replaced = current.clone();
        replaced["grain"]["generation"] = json!("5");
        assert!(!exact_provider_reserve(&replaced, &hold));
        replaced = current.clone();
        replaced["grain"]["reserved"] = json!("2");
        assert!(!exact_provider_reserve(&replaced, &hold));
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
