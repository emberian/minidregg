//! Physical controller for one Mini agent-grain task. Semantic admission is
//! exclusively a signed call to the native Lean host through `mini`.
mod control;
mod mcp;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::fs::{FileTypeExt, MetadataExt, PermissionsExt};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitCode, Stdio};
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::mpsc::{self, Receiver};
use std::sync::Arc;
use std::sync::Mutex;
use std::thread;
use std::time::Duration;

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
#[serde(deny_unknown_fields)]
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
    child: Option<ChildRecord>,
    settlement_due: Option<String>,
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
}

impl Journal {
    fn fresh(binding: Value) -> Self {
        Self {
            format: "minidregg-grain-runtime-v1".into(),
            binding,
            next_operation_id: 1,
            connection: Connection::Detached,
            pending: None,
            tool_pending: None,
            child: None,
            settlement_due: None,
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
    }
    Ok(())
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
    current_unit: Arc<Mutex<Option<String>>>,
    output: Option<control::OutputHandle>,
}

impl Runtime {
    fn emit(&self, message: impl Into<String>) {
        if let Some(output) = &self.output {
            let _ = output.try_output(message);
        }
    }
    fn worker_unit(&self, id: u64, spec: &AllowedCommand) -> Option<String> {
        spec.systemd_scope
            .then(|| format!("mini-grain-t{}-o{id}", self.config.task))
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
            current_unit: Arc::new(Mutex::new(None)),
            output: None,
        };
        // We have no live Child handle after a controller crash. A recycled
        // PID/PGID must never be killed. Fence the task and refuse new work.
        if rt.journal.child.is_some() {
            rt.journal.connection = Connection::Fenced;
            rt.save()?;
        } else if rt.journal.connection == Connection::Hard {
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
            "authorityRoot":challenge.pointer("/signing/0/authorityRoot")}),
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
        let tool = match &self.config.tool_task {
            Some(t) => t.clone(),
            None => return Ok(()),
        };
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
        let source = json!({"subject":self.config.subject,"intentNonce":id.to_string(),
            "declarationNonce":id.to_string(),"task":self.config.task,
            "owner":self.config.subject,"workerSubject":tool.subject,
            "workerGeneration":generation,
            "control":self.config.policy_control_capability.as_ref().ok_or("policy control capability absent")?,
            "domain":view.get("domain").ok_or("policy domain absent")?,
            "semantics":view.get("semantics").ok_or("policy semantics absent")?,
            "expectedPreRoot":policy.get("authorityRoot").ok_or("policy authority root absent")?,
            "expectedVersion":view.get("version").ok_or("policy version absent")?,
            "expectedAddress":view.get("address").ok_or("policy address absent")?,
            "grants":[{"kind":"object","target":self.config.task,
                "capability":self.config.query_capability}]});
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
                if refusal || !attempt.join("call.bin").is_file() {
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
    fn transition_as(
        &mut self,
        authority: &Authority,
        op: Value,
        label: &str,
        payload: &str,
        publications: Vec<Value>,
    ) -> Result<()> {
        let tool_authority = authority.task != self.config.task;
        if (if tool_authority {
            &self.journal.tool_pending
        } else {
            &self.journal.pending
        })
        .is_some()
        {
            return Err("this Mini authority has an unresolved transition".into());
        }
        let observed = self.query_as(authority)?;
        let before = observed.get("grain").ok_or("missing observed grain")?;
        let id = self.next_id()?;
        let joint = !publications.is_empty();
        let mut grants = vec![json!({"kind":"object","target":authority.task,
            "capability":authority.capability})];
        if joint {
            grants.push(json!({"kind":"object","target":authority.task,
                "capability":authority.query_capability}));
            for target in &publications {
                grants.push(json!({"kind":target["kind"],"target":target["target"],
                    "capability":target["capability"]}));
                grants.push(json!({"kind":target["kind"],"target":target["target"],
                    "capability":target["observeCapability"]}));
            }
        }
        let parent_witness = if joint {
            let t = self
                .config
                .tool_task
                .as_ref()
                .ok_or("tool task absent for joint publication")?;
            let mut witness = self
                .journal
                .prompt_witness
                .clone()
                .ok_or("parent prompt witness absent")?;
            witness["capability"] = json!(t.parent_capability);
            witness["observeCapability"] = json!(t.parent_observe_capability);
            grants.push(json!({"kind":"object","target":self.config.task,
                "capability":t.parent_capability}));
            grants.push(json!({"kind":"object","target":self.config.task,
                "capability":t.parent_observe_capability}));
            Some(witness)
        } else {
            None
        };
        let mut grain = json!({"task":authority.task,"subject":authority.subject,
            "capability":authority.capability,"schemaVersion":"1",
            "expectedAuthorityRoot":observed.get("authorityRoot").ok_or("missing authority root")?,
            "expectedTargetRoot":observed.get("targetRoot").ok_or("missing target root")?,
            "context":{"operationId":id.to_string(),"payload":payload},
            "before":{"generation":before.get("generation"),"status":before.get("status"),
                "remaining":before.get("remaining"),"reserved":before.get("reserved")},
            "operation":op,"publications":publications,
            "observeCapability":if joint { json!(authority.query_capability) } else { Value::Null }});
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
        if tool_authority {
            self.journal.tool_pending = pending;
        } else {
            self.journal.pending = pending;
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
                if tool_authority {
                    self.journal.tool_pending = None;
                } else {
                    self.journal.pending = None;
                }
                if label == "settle" && !tool_authority {
                    self.journal.settlement_due = None;
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
                    if tool_authority {
                        self.journal.tool_pending = None;
                    } else {
                        self.journal.pending = None;
                    }
                    self.save()?;
                    return Err(format!("{label} refused by Mini: {}", explicit.unwrap()));
                }
                if !attempt.join("call.bin").is_file() {
                    // The custody subprocess has completed, and it always
                    // materializes call.bin before submission. This case is
                    // a local construction failure, unlike a crash while
                    // the custody subprocess might still be running.
                    if tool_authority {
                        self.journal.tool_pending = None;
                    } else {
                        self.journal.pending = None;
                    }
                    self.save()?;
                    return Err(format!("{label} did not produce a signed call: {e}"));
                }
                if let Some(p) = if tool_authority {
                    &mut self.journal.tool_pending
                } else {
                    &mut self.journal.pending
                } {
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
        let outcome = self.tool_call(&request.name, &request.arguments);
        let response = match outcome {
            Ok(value) => json!({"isError":false,"text":value.to_string()}),
            Err(error) => json!({"isError":true,"text":error}),
        };
        let _ = request.reply.send(response);
    }
    fn tool_call(&mut self, name: &str, arguments: &Value) -> Result<Value> {
        if self.cancelled.load(Ordering::SeqCst)
            || self.journal.connection == Connection::Fenced
            || self.journal.child.is_none()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
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
    fn attach(&mut self, soft: bool) -> Result<()> {
        if self.journal.connection == Connection::Fenced
            || self.journal.child.is_some()
            || self.journal.pending.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.settlement_due.is_some()
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
        self.save()?;
        self.emit(format!(
            "attached {} to Mini grain {}\n",
            if soft { "soft" } else { "hard" },
            self.config.task
        ));
        Ok(())
    }
    fn stop_and_reap_owned(
        &mut self,
        completed_charge: Option<&str>,
    ) -> Result<std::process::ExitStatus> {
        let unit = self.journal.child.as_ref().and_then(|c| c.unit.clone());
        let child = self.child.as_mut().ok_or("no live owned child")?;
        let pgid = child.id() as i32;
        // The leader remains unreaped until group cleanup, so its PID cannot
        // be recycled while signals address the process group.
        if group_has_live_member(pgid)? {
            signal_group(pgid, libc::SIGTERM)?;
        }
        if let Some(unit) = &unit {
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
        }
        let _signal_guard = self
            .signal_lock
            .lock()
            .map_err(|_| "signal lock poisoned")?;
        let status = child.wait().map_err(|e| format!("child wait: {e}"))?;
        self.child = None;
        self.current_pgid.store(0, Ordering::SeqCst);
        *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
        self.journal.child = None;
        if let Some(charge) = completed_charge {
            self.journal.settlement_due = Some(charge.to_owned());
        }
        self.save()?;
        Ok(status)
    }
    fn kill_child(&mut self) -> Result<()> {
        if self.child.is_none() {
            return Ok(());
        }
        self.stop_and_reap_owned(None).map(|_| ())
    }
    fn disconnect(&mut self) -> Result<()> {
        if self.journal.connection == Connection::Soft
            && !self.hard_connection.load(Ordering::SeqCst)
        {
            return Ok(());
        }
        let soft_reserved = self.journal.connection == Connection::Soft;
        self.cancelled.store(true, Ordering::SeqCst);
        self.journal.connection = Connection::Fenced;
        self.hard_connection.store(false, Ordering::SeqCst);
        // Signal first on detection; neither filesystem sync nor Mini's
        // potentially slow replay may precede local physical interruption.
        let stopped = self.kill_child();
        self.save()?;
        let tool_fenced = self.fence_tool();
        let fenced = self.transition(
            if soft_reserved {
                json!({"type":"cancel"})
            } else {
                json!({"type":"disconnect"})
            },
            "disconnect",
            "hard connection lost",
        );
        match (stopped, fenced, tool_fenced) {
            (Ok(()), Ok(()), Ok(())) => {
                self.journal.connection = Connection::Detached;
                self.journal.prompt_witness = None;
                self.save()
            }
            (a, b, c) => Err(format!(
                "hard disconnect unresolved: local stop={a:?}; Mini fence={b:?}; tool fence={c:?}"
            )),
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
                _ => {}
            }
        }
        let id = self.next_id()?;
        let unit = self.worker_unit(id, &spec);
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
        });
        self.save()?;
        *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = unit.clone();
        let signal_lock = self.signal_lock.clone();
        let spawn_guard = signal_lock.lock().map_err(|_| "signal lock poisoned")?;
        if self.cancelled.load(Ordering::SeqCst) {
            drop(spawn_guard);
            *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
            self.journal.child = None;
            self.save()?;
            return self.disconnect();
        }
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(e) => {
                drop(spawn_guard);
                *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
                self.journal.child = None;
                self.save()?;
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
            unit,
        });
        if let Err(e) = self.save() {
            let _ = self.kill_child();
            return Err(e);
        }
        loop {
            if child_exited_unreaped(self.child.as_ref().unwrap())? {
                let status = self.stop_and_reap_owned(Some(&spec.charge))?;
                self.transition(
                    json!({"type":"settle","charge":spec.charge}),
                    "settle",
                    &format!("command:{name}:exit:{status}"),
                )?;
                self.journal.settlement_due = None;
                self.save()?;
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
                    self.hard_connection.store(true, Ordering::SeqCst);
                    self.emit(
                        "hard transport attached to soft reservation; loss will cancel the task\n",
                    );
                }
                Ok(Input::Line(_)) => eprintln!("command running; only disconnect is accepted"),
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
                _ => {}
            }
        }
        let id = self.next_id()?;
        let unit = self.worker_unit(id, &spec);
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
        self.worker_env(&mut command, &unit, Some(&broker_path));
        unsafe {
            command.pre_exec(|| {
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
        });
        self.save()?;
        *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = unit.clone();
        let signal_lock = self.signal_lock.clone();
        let spawn_guard = signal_lock.lock().map_err(|_| "signal lock poisoned")?;
        if self.cancelled.load(Ordering::SeqCst) {
            drop(spawn_guard);
            *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
            self.journal.child = None;
            self.save()?;
            return self.disconnect();
        }
        let mut child = match command.spawn() {
            Ok(child) => child,
            Err(e) => {
                drop(spawn_guard);
                *self.current_unit.lock().map_err(|_| "unit lock poisoned")? = None;
                self.journal.child = None;
                self.save()?;
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
            unit,
        });
        if let Err(e) = self.save() {
            let _ = self.kill_child();
            return Err(e);
        }
        let (tx, rx) = mpsc::channel::<Result<Value>>();
        thread::spawn(move || {
            for line in io::BufReader::new(child_stdout).lines() {
                let msg = line
                    .map_err(|e| e.to_string())
                    .and_then(|s| serde_json::from_str::<Value>(&s).map_err(|e| e.to_string()));
                if tx.send(msg).is_err() {
                    return;
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
            self.acp_response(1, &rx, input, &mut child_stdin, &display_tx, &broker)?;
            acp_send(
                &mut child_stdin,
                2,
                "session/new",
                json!({
                    "cwd":self.config.cwd,"mcpServers":[{"name":"mini-grain",
                        "command":broker_program,"args":["mcp-stdio",broker_socket],"env":[]}]
                }),
            )?;
            let response =
                self.acp_response(2, &rx, input, &mut child_stdin, &display_tx, &broker)?;
            response
                .get("sessionId")
                .or_else(|| response.get("session_id"))
                .and_then(Value::as_str)
                .map(str::to_owned)
                .ok_or("Hermes omitted session ID".into())
        })();
        let outcome = match session {
            Ok(session_id) => acp_send(
                &mut child_stdin,
                3,
                "session/prompt",
                json!({
                    "sessionId":session_id,"prompt":[{"type":"text","text":prompt}]
                }),
            )
            .and_then(|_| self.acp_response(3, &rx, input, &mut child_stdin, &display_tx, &broker)),
            Err(e) => Err(e),
        };
        if self.journal.connection == Connection::Fenced {
            return outcome.map(|_| ());
        }
        if let Err(error) = &outcome {
            let stopped = self.stop_and_reap_owned(None);
            self.journal.connection = Connection::Fenced;
            self.hard_connection.store(false, Ordering::SeqCst);
            self.journal
                .unresolved_external
                .push(format!("Hermes prompt {id}: {error}"));
            self.save()?;
            let fence = self.transition(
                json!({"type":"disconnect"}),
                "disconnect",
                "Hermes ACP fault",
            );
            return Err(format!("Hermes ACP outcome uncertain: {error}; local stop={stopped:?}; Mini fence={fence:?}"));
        }
        // The ACP server has finished the prompt. Close stdin and reap its
        // process. Provider usage may still be uncertain; charge is explicitly
        // the configured budget unit, not an attested invoice.
        drop(child_stdin);
        let exit = self.stop_and_reap_owned(Some(&spec.charge))?;
        self.transition(
            json!({"type":"settle","charge":spec.charge}),
            "settle",
            &format!("hermes-acp exit:{exit}"),
        )?;
        self.journal.settlement_due = None;
        self.journal.prompt_witness = None;
        self.save()?;
        outcome.map(|_| ())
    }
    fn acp_response(
        &mut self,
        id: i64,
        rx: &Receiver<Result<Value>>,
        input: &Receiver<Input>,
        writer: &mut impl Write,
        display: &mpsc::SyncSender<String>,
        broker: &mcp::BrokerEndpoint,
    ) -> Result<Value> {
        loop {
            while let Ok(request) = broker.requests.try_recv() {
                self.handle_tool(request);
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
                    self.hard_connection.store(true, Ordering::SeqCst);
                    self.emit(
                        "hard transport attached to soft reservation; loss will cancel the task\n",
                    );
                }
                Ok(Input::Line(_)) => {
                    eprintln!("Hermes prompt running; only disconnect is accepted")
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
        if self.journal.child.is_some() {
            return Err("prior controller died with active child; PID reuse prevents automatic kill; operator process audit required".into());
        }
        self.retry_pending(true)?;
        self.retry_pending(false)?;
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
        if self.journal.connection == Connection::Fenced {
            let tool_fence = self.fence_tool();
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
            } else if !matches!(status, "0" | "5" | "6" | "7") {
                return Err(format!(
                    "fenced recovery has unexpected grain status {status}"
                ));
            }
            tool_fence?;
            self.journal.connection = Connection::Detached;
            self.journal.prompt_witness = None;
            self.save()?;
        }
        Ok(())
    }
    fn retry_pending(&mut self, tool: bool) -> Result<()> {
        let pending = if tool {
            &self.journal.tool_pending
        } else {
            &self.journal.pending
        };
        if let Some(p) = pending.clone() {
            if !p.attempt.join("call.bin").is_file() {
                // A crashed custody subprocess may still assemble the call and
                // dispatch later. Absence right now is not a negative receipt.
                return Err("pending custody attempt has no call.bin; child lifetime is uncertain; manual reconciliation required".into());
            }
            let attempt = p.attempt.to_str().ok_or("attempt path UTF-8")?;
            let mut args = vec!["retry", "--attempt", attempt, "--mode", "lookup"];
            if let Some(socket) = &self.config.host_socket {
                args.extend(["--socket", socket.to_str().ok_or("socket path UTF-8")?]);
            }
            self.command_output(&self.config.mini, &args)?;
            if tool {
                self.journal.tool_pending = None;
            } else {
                self.journal.pending = None;
            }
            if p.operation == "settle" && !tool {
                self.journal.settlement_due = None;
            }
            if p.operation == "disconnect" && !tool {
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
    let current_unit = rt.current_unit.clone();
    let interrupt: control::HardInterrupt = Arc::new(move |_| {
        cancelled.store(true, Ordering::SeqCst);
        interrupt_from_input(&pgid, &hard, &lock);
        if let Ok(unit) = current_unit.lock() {
            if let Some(unit) = unit.as_deref() {
                let _ = kill_unit(unit);
            }
        }
    });
    clear_stale_control_socket(&rt.config.control_socket)?;
    let server = control::start(&rt.config.control_socket, interrupt)?;
    rt.output = Some(server.output_handle());
    let (tx, input) = mpsc::channel();
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
            Input::Line(_) => {
                Err("expected attach hard|soft, run NAME, status, recover, disconnect".into())
            }
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
        return match control::connect(&PathBuf::from(&args[2])) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) => {
                eprintln!("grain-runtime connect: {e}");
                ExitCode::from(1)
            }
        };
    }
    if args.len() != 3 || args[1] != "serve" {
        eprintln!("usage: grain-runtime serve /absolute/config.json | connect /absolute/socket | mcp-stdio /absolute/socket");
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
