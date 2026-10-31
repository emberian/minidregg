//! `grain-runtime create SPEC.json`: birth one member AgentGrain (a parent
//! task and its tool task) on a live Store, delegate the worker its parent
//! witness, initialize the controller-private resource workspace, and write
//! the controller config that `serve` opens. Every signed step goes through
//! the ordinary `mini` client and is admitted by the Lean Host; this command
//! authors no native state itself.
//!
//! Lost replies: each signed step owns a fixed attempt directory under
//! ROOT/create. A rerun with the same spec never resubmits: an attempt whose
//! outcome is absent is resolved with `mini retry --mode lookup`, and only a
//! confirmed outcome lets the next step run. A different spec against an
//! existing ROOT is refused.
use crate::*;

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Key {
    key: PathBuf,
    subject: String,
    /// Genesis keys that commit to no next key need `--no-prerotation`.
    no_prerotation: bool,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Grant {
    kind: String,
    target: String,
    capability: String,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Sponsor {
    key: PathBuf,
    subject: String,
    /// The account capability that pays the births and fees.
    account_capability: String,
    /// Capabilities the birth intent presents (factory observation, account).
    grants: Vec<Grant>,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Template {
    issuer: String,
    owner_budget: String,
    lifetime: String,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Capabilities {
    parent_observe: String,
    parent_control: String,
    tool_observe: String,
    tool_control: String,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Budgets {
    parent: String,
    tool: String,
    witness_max_cost: String,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Worker {
    launcher: PathBuf,
    runtime_root: PathBuf,
    workspace: PathBuf,
    /// `none` (production: provider through the bridge) or `host` (fixture).
    network: String,
    wall_time_seconds: u64,
    reserve: String,
    charge: String,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Charges {
    reserve: String,
    charge: String,
}

/// The provider purse: a third grain owned by its own worker subject, born
/// in the same intent, witnessed by the parent like the tool task. `gateway`
/// carries the providerTask fields the operator chooses (providers table,
/// credential broker, gateway bind, model, reserve, token and byte bounds,
/// onBehalfOf, provider row pin); the identity fields are filled here.
#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ProviderPurse {
    key: Key,
    task: String,
    observe_capability: String,
    control_capability: String,
    budget: String,
    gateway: serde_json::Map<String, Value>,
}

/// Application calls use their own grain and signer, independent of the
/// foreground tool allowance and the provider purse. The transport contains
/// the operator's socket and peer pins; identity and parent witnesses are
/// filled from the admitted birth and delegation, as for the provider.
#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct DispatchPurse {
    key: Key,
    task: String,
    observe_capability: String,
    control_capability: String,
    budget: String,
    transport: serde_json::Map<String, Value>,
}

#[derive(Deserialize, Serialize, Clone)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Spec {
    #[serde(rename = "type")]
    kind: String,
    mini: PathBuf,
    host: PathBuf,
    host_config: PathBuf,
    host_socket: PathBuf,
    genesis: PathBuf,
    namespace_root: PathBuf,
    root: PathBuf,
    nonce: String,
    sponsor: Sponsor,
    template: Template,
    owner: Key,
    worker_key: Key,
    task: String,
    tool_task: String,
    capabilities: Capabilities,
    budgets: Budgets,
    worker: Worker,
    tool_charges: Charges,
    #[serde(default)]
    provider: Option<ProviderPurse>,
    #[serde(default)]
    dispatch: Option<DispatchPurse>,
    #[serde(default)]
    room: Option<Value>,
    /// `S`, `M` or `L`: grant upstream Hermes's sandbox toolsets up to the
    /// class bounds (docs/HERMES-TOOLS-2026-10-27.md); absent, none.
    #[serde(default)]
    sandbox: Option<String>,
}

const SPEC_TYPE: &str = "mini-grain-create-v1";

fn canonical_decimal(value: &str, what: &str) -> Result<()> {
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) || (value.len() > 1 && value.starts_with('0')) {
        return Err(format!("{what} must be canonical decimal: {value:?}"));
    }
    Ok(())
}

fn absolute(path: &Path, what: &str) -> Result<()> {
    if !path.is_absolute()
        || path.components().any(|c| !matches!(c, std::path::Component::RootDir | std::path::Component::Normal(_)))
    {
        return Err(format!("{what} must be a canonical absolute path: {}", path.display()));
    }
    Ok(())
}

fn executable(path: &Path, what: &str) -> Result<()> {
    absolute(path, what)?;
    let meta = fs::metadata(path).map_err(|e| format!("{what} {}: {e}", path.display()))?;
    if !meta.is_file() || meta.permissions().mode() & 0o111 == 0 {
        return Err(format!("{what} is not an executable file: {}", path.display()));
    }
    Ok(())
}

fn private_key(path: &Path, what: &str) -> Result<()> {
    absolute(path, what)?;
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{what} {}: {e}", path.display()))?;
    if !meta.is_file() || meta.permissions().mode() & 0o077 != 0 || meta.uid() != unsafe { libc::geteuid() } {
        return Err(format!("{what} must be a regular 0600 file owned by this account: {}", path.display()));
    }
    Ok(())
}

fn readable(path: &Path, what: &str) -> Result<()> {
    absolute(path, what)?;
    if !fs::metadata(path).map_err(|e| format!("{what} {}: {e}", path.display()))?.is_file() {
        return Err(format!("{what} is not a regular file: {}", path.display()));
    }
    Ok(())
}

fn directory(path: &Path, what: &str) -> Result<()> {
    absolute(path, what)?;
    if !fs::metadata(path).map_err(|e| format!("{what} {}: {e}", path.display()))?.is_dir() {
        return Err(format!("{what} is not a directory: {}", path.display()));
    }
    Ok(())
}

impl Spec {
    /// Refuse every missing or malformed input before anything is signed.
    fn check(&self, phase: &Phase) -> Result<()> {
        self.check_values()?;
        self.check_paths(phase)
    }

    /// The birth is signed by the operator's sponsor; a resident running as
    /// its own uid never holds that key, so once the birth is confirmed the
    /// sponsor key is no longer asked for.
    fn birth_confirmed(&self) -> Result<bool> {
        confirmed(&self.root.join("create/birth/outcome.json"))
    }

    /// Whether this run still authors or looks up the birth, and so reads genesis.
    /// The operator's birth phase always does; the resident's half only until the
    /// birth outcome is confirmed.
    fn needs_genesis(&self, phase: &Phase) -> Result<bool> {
        Ok(matches!(phase, Phase::Birth { .. }) || !self.birth_confirmed()?)
    }

    /// Values only: no filesystem access.
    fn check_values(&self) -> Result<()> {
        if self.kind != SPEC_TYPE {
            return Err(format!("spec type must be {SPEC_TYPE}"));
        }
        for (value, what) in [
            (&self.nonce, "nonce"), (&self.sponsor.subject, "sponsor.subject"),
            (&self.sponsor.account_capability, "sponsor.accountCapability"),
            (&self.template.issuer, "template.issuer"), (&self.template.owner_budget, "template.ownerBudget"),
            (&self.template.lifetime, "template.lifetime"), (&self.owner.subject, "owner.subject"),
            (&self.worker_key.subject, "workerKey.subject"), (&self.task, "task"), (&self.tool_task, "toolTask"),
            (&self.capabilities.parent_observe, "capabilities.parentObserve"),
            (&self.capabilities.parent_control, "capabilities.parentControl"),
            (&self.capabilities.tool_observe, "capabilities.toolObserve"),
            (&self.capabilities.tool_control, "capabilities.toolControl"),
            (&self.budgets.parent, "budgets.parent"), (&self.budgets.tool, "budgets.tool"),
            (&self.budgets.witness_max_cost, "budgets.witnessMaxCost"),
            (&self.worker.reserve, "worker.reserve"), (&self.worker.charge, "worker.charge"),
            (&self.tool_charges.reserve, "toolCharges.reserve"), (&self.tool_charges.charge, "toolCharges.charge"),
        ] {
            canonical_decimal(value, what)?;
        }
        if self.sponsor.grants.is_empty() {
            return Err("sponsor.grants must name the capabilities the birth presents".into());
        }
        for grant in &self.sponsor.grants {
            canonical_decimal(&grant.target, "sponsor.grants[].target")?;
            canonical_decimal(&grant.capability, "sponsor.grants[].capability")?;
            if !matches!(grant.kind.as_str(), "object" | "account") {
                return Err("sponsor.grants[].kind must be object or account".into());
            }
        }
        if let Some(p) = &self.provider {
            for (value, what) in [(&p.key.subject, "provider.key.subject"), (&p.task, "provider.task"),
                (&p.observe_capability, "provider.observeCapability"), (&p.control_capability, "provider.controlCapability"),
                (&p.budget, "provider.budget")] {
                canonical_decimal(value, what)?;
            }
            if [&self.task, &self.tool_task].contains(&&p.task)
                || [&self.owner.subject, &self.worker_key.subject].contains(&&p.key.subject) {
                return Err("provider task and subject must be distinct from the parent and tool".into());
            }
            for owned in ["task", "subject", "capability", "queryCapability", "custodyKey", "parentCapability", "parentObserveCapability"] {
                if p.gateway.contains_key(owned) {
                    return Err(format!("provider.gateway must not set {owned}; create fills it"));
                }
            }
        }
        if let Some(d) = &self.dispatch {
            for (value, what) in [(&d.key.subject, "dispatch.key.subject"), (&d.task, "dispatch.task"),
                (&d.observe_capability, "dispatch.observeCapability"), (&d.control_capability, "dispatch.controlCapability"),
                (&d.budget, "dispatch.budget")] {
                canonical_decimal(value, what)?;
            }
            if [&self.task, &self.tool_task].contains(&&d.task)
                || [&self.owner.subject, &self.worker_key.subject].contains(&&d.key.subject)
                || [&self.owner.key, &self.worker_key.key].contains(&&d.key.key)
                || self.provider.as_ref().is_some_and(|p| p.task == d.task || p.key.subject == d.key.subject || p.key.key == d.key.key) {
                return Err("dispatch task, subject and key must be distinct from parent, tool and provider".into());
            }
            for owned in ["task", "subject", "capability", "queryCapability", "custodyKey", "parentCapability", "parentObserveCapability"] {
                if d.transport.contains_key(owned) {
                    return Err(format!("dispatch.transport must not set {owned}; create fills it"));
                }
            }
            // Decode before signing a birth: unknown or incomplete transport
            // fields must not leave a successfully born but unusable grain.
            let task: DispatchTask = serde_json::from_value(d.controller("0"))
                .map_err(|e| format!("dispatch.transport: {e}"))?;
            for (value, name) in [(&task.reserve, "dispatch.reserve"), (&task.charge, "dispatch.charge")] {
                canonical_decimal(value, name)?;
            }
            if task.reserve.parse::<u64>().ok().zip(task.charge.parse::<u64>().ok())
                .is_none_or(|(r, c)| r == 0 || c > r) {
                return Err("dispatch charge must fit a positive u64 reserve".into());
            }
            if task.host_uid == 0 || !task.socket_path.is_absolute()
                || task.operator_socket.as_ref().is_none_or(|p| !p.is_absolute() || p == &self.host_socket || p == &task.socket_path)
                || task.reserve_signer.is_none() {
                return Err("dispatch requires an external non-root host, distinct operator socket and reserve signer".into());
            }
        }
        if self.task == self.tool_task {
            return Err("task and toolTask must differ".into());
        }
        let mut caps = vec![&self.capabilities.parent_observe, &self.capabilities.parent_control,
            &self.capabilities.tool_observe, &self.capabilities.tool_control];
        if let Some(p) = &self.provider { caps.extend([&p.observe_capability, &p.control_capability]); }
        if let Some(d) = &self.dispatch { caps.extend([&d.observe_capability, &d.control_capability]); }
        if caps.iter().collect::<std::collections::BTreeSet<_>>().len() != caps.len() {
            return Err("all parent, tool, provider and dispatch capability IDs must be distinct".into());
        }
        if !matches!(self.worker.network.as_str(), "none" | "host") {
            return Err(format!("worker.network must be none or host, not {:?}", self.worker.network));
        }
        if self.worker.wall_time_seconds == 0 || self.worker.wall_time_seconds > 3600 {
            return Err("worker.wallTimeSeconds must be in 1..=3600".into());
        }
        if self.owner.key == self.worker_key.key || self.owner.subject == self.worker_key.subject {
            return Err("owner and worker must be distinct subjects with distinct keys".into());
        }
        if let Some(class) = &self.sandbox {
            crate::sandbox_tools::Sandbox::for_class(class)?;
            if self.worker.network != "none" || self.room.is_none() {
                return Err("sandbox tools need worker.network none and a room".into());
            }
        }
        Ok(())
    }

    fn check_paths(&self, phase: &Phase) -> Result<()> {
        executable(&self.mini, "mini")?;
        executable(&self.host, "host")?;
        readable(&self.host_config, "hostConfig")?;
        absolute(&self.host_socket, "hostSocket")?;
        let live = match phase { Phase::Birth { socket } => socket, Phase::Whole => &self.host_socket };
        if !fs::metadata(live).map(|m| m.file_type().is_socket()).unwrap_or(false) {
            return Err(format!("the Host socket is not a live socket: {}", live.display()));
        }
        // Genesis describes the deployment for the birth only. A confirmed birth
        // is past that: the resident half of a split create never reads it (the
        // deployment's genesis file is the operator's, 0600, and holds sponsor and
        // enrollment material).
        if self.needs_genesis(phase)? {
            readable(&self.genesis, "genesis")?;
        }
        directory(&self.namespace_root, "namespaceRoot")?;
        absolute(&self.root, "root")?;
        // Linux sockaddr_un holds 108 bytes including NUL; the control and
        // admin sockets live in ROOT/state.
        if self.root.join("state/control.sock").as_os_str().len() >= 100 {
            return Err("root is too long for the controller's Unix sockets".into());
        }
        if matches!(phase, Phase::Birth { .. }) || !self.birth_confirmed()? {
            private_key(&self.sponsor.key, "sponsor.key")?;
        }
        if matches!(phase, Phase::Birth { .. }) {
            // The operator's part: everything else belongs to the resident.
            return Ok(());
        }
        private_key(&self.owner.key, "owner.key")?;
        private_key(&self.worker_key.key, "workerKey.key")?;
        if let Some(p) = &self.provider {
            private_key(&p.key.key, "provider.key.key")?;
        }
        if let Some(d) = &self.dispatch {
            private_key(&d.key.key, "dispatch.key.key")?;
        }
        executable(&self.worker.launcher, "worker.launcher")?;
        if self.worker.launcher.file_name().and_then(|n| n.to_str()) != Some("bwrap") {
            return Err("worker.launcher must be the bwrap launcher".into());
        }
        directory(&self.worker.runtime_root, "worker.runtimeRoot")?;
        executable(&self.worker.runtime_root.join("hermes-acp"), "worker.runtimeRoot/hermes-acp")?;
        directory(&self.worker.workspace, "worker.workspace")?;
        match self.worker.network.as_str() {
            "none" => {
                if self.provider.is_some() {
                    executable(&self.worker.runtime_root.join("grain-provider-bridge"),
                        "worker.runtimeRoot/grain-provider-bridge (required by --network none with a provider)")?;
                }
            }
            "host" => {
                if self.provider.as_ref().is_some_and(|p| p.gateway.get("localFixtureHostNetwork") != Some(&json!(true))) {
                    return Err("worker.network host is a fixture topology; a provider task then needs localFixtureHostNetwork".into());
                }
            }
            _ => unreachable!("checked in check_values"),
        }
        Ok(())
    }

    fn birth_intent(&self, genesis: &Value) -> Value {
        let workers = ordered_worker_subjects(
            Some(&self.worker_key.subject),
            self.provider.as_ref().map(|v| v.key.subject.as_str()),
            self.dispatch.as_ref().map(|v| v.key.subject.as_str()),
        );
        let mut resources = vec![
            json!({"kind":"object","storage":"grain","target":self.task,"owner":self.owner.subject,
                "ownerCapability":self.capabilities.parent_observe,"controlCapability":self.capabilities.parent_control,
                "budget":self.budgets.parent,"workerGeneration":"1"}),
            json!({"kind":"object","storage":"grain","target":self.tool_task,"owner":self.worker_key.subject,
                "ownerCapability":self.capabilities.tool_observe,"controlCapability":self.capabilities.tool_control,
                "budget":self.budgets.tool}),
        ];
        if let Some(p) = &self.provider {
            resources.push(json!({"kind":"object","storage":"grain","target":p.task,"owner":p.key.subject,
                "ownerCapability":p.observe_capability,"controlCapability":p.control_capability,"budget":p.budget}));
        }
        if let Some(d) = &self.dispatch {
            resources.push(json!({"kind":"object","storage":"grain","target":d.task,"owner":d.key.subject,
                "ownerCapability":d.observe_capability,"controlCapability":d.control_capability,"budget":d.budget}));
        }
        resources[0]["workerSubjects"] = json!(workers);
        let resources = Value::Array(resources);
        json!({"subject":self.sponsor.subject,"nonce":self.nonce,
            "birth":{"genesis":genesis,
                "template":{"issuer":self.template.issuer,"ownerBudget":self.template.owner_budget,"lifetime":self.template.lifetime},
                "creator":self.sponsor.subject,"nonce":self.nonce,
                "resources":resources,
                "sourceCapabilities":[self.sponsor.account_capability],"funding":[],"feePayer":self.sponsor.subject},
            "grants":self.sponsor.grants})
    }

    fn controller(&self, witness: &str, provider_witness: Option<&str>, dispatch_witness: Option<&str>, consent_readiness: Option<bool>) -> Value {
        let state = self.root.join("state");
        let mut args = vec![
            "--workspace".to_owned(), self.worker.workspace.display().to_string(),
            "--runtime-root".to_owned(), self.worker.runtime_root.display().to_string(),
            "--network".to_owned(), self.worker.network.clone(),
        ];
        args.extend(["--".to_owned(), "/agent/hermes-acp".to_owned()]);
        let mut tool = json!({"task":self.tool_task,"subject":self.worker_key.subject,
            "capability":self.capabilities.tool_observe,"queryCapability":self.capabilities.tool_observe,
            "custodyKey":self.worker_key.key,"parentCapability":witness,"parentObserveCapability":witness,
            "reserve":self.tool_charges.reserve,"charge":self.tool_charges.charge,"allowedPublications":[],
            "resourceWorkspace":state.join("resource-workspace")});
        if let Some(room) = &self.room {
            tool["room"] = room.clone();
        }
        let mut config = json!({"mini":self.mini,"host":self.host,"hostConfig":self.host_config,
            "hostSocket":self.host_socket,"custodyKey":self.owner.key,"stateDir":state,
            "controlSocket":state.join("control.sock"),"cwd":self.root,"task":self.task,
            "subject":self.owner.subject,"capability":self.capabilities.parent_observe,
            "queryCapability":self.capabilities.parent_observe,
            "policyControlCapability":self.capabilities.parent_control,"toolTask":tool,
            "commands":[{"name":"hermes-acp","program":self.worker.launcher,"args":args,
                "systemdScope":true,"wallTimeSeconds":self.worker.wall_time_seconds,
                "reserve":self.worker.reserve,"charge":self.worker.charge}]});
        if let (Some(provider), Some(witness)) = (&self.provider, provider_witness) {
            let mut task = provider.gateway.clone();
            for (key, value) in [("task", json!(provider.task)), ("subject", json!(provider.key.subject)),
                ("capability", json!(provider.observe_capability)), ("queryCapability", json!(provider.observe_capability)),
                ("custodyKey", json!(provider.key.key)), ("parentCapability", json!(witness)),
                ("parentObserveCapability", json!(witness))] {
                task.insert(key.into(), value);
            }
            config["providerTask"] = Value::Object(task);
        }
        if let (Some(dispatch), Some(witness)) = (&self.dispatch, dispatch_witness) {
            config["dispatchTask"] = dispatch.controller(witness);
        }
        if let Some(enabled) = consent_readiness {
            config["consentFullReadiness"] = json!(enabled);
        }
        if let Some(class) = &self.sandbox {
            let sandbox = crate::sandbox_tools::Sandbox::for_class(class).expect("sandbox class checked in validate");
            config["sandbox"] = serde_json::to_value(sandbox).expect("sandbox serializes");
        }
        config
    }
}

impl DispatchPurse {
    fn controller(&self, witness: &str) -> Value {
        let mut task = self.transport.clone();
        for (key, value) in [("task", json!(self.task)), ("subject", json!(self.key.subject)),
            ("capability", json!(self.observe_capability)), ("queryCapability", json!(self.observe_capability)),
            ("custodyKey", json!(self.key.key)), ("parentCapability", json!(witness)),
            ("parentObserveCapability", json!(witness))] {
            task.insert(key.into(), value);
        }
        Value::Object(task)
    }
}

fn run(command: &mut Command, what: &str) -> Result<Vec<u8>> {
    run_with_limit(command, what, deadline::NATIVE_CALL)
}

fn run_with_limit(command: &mut Command, what: &str, limit: Duration) -> Result<Vec<u8>> {
    // A timeout is a lost reply: the signed step is then resolved by lookup.
    let output = deadline::output(command.stdin(Stdio::null()), limit)
        .map_err(|e| deadline::describe(what, e))?;
    if !output.status.success() {
        return Err(format!("{what} exited {}: {}", output.status, String::from_utf8_lossy(&output.stderr).trim()));
    }
    Ok(output.stdout)
}

/// New dispatch controllers will use lifecycle authoring, so establish full
/// consent on their actual signing provider before Whole performs signed work.
/// Existing published configs keep their exact opt-in state; plain grains keep
/// the thin-consent path. An unsupported cohort is an error, never an opt-out.
fn provision_consent_readiness(spec: &Spec, work: &Path) -> Result<Option<bool>> {
    let config_path = spec.root.join("controller.json");
    match fs::symlink_metadata(&config_path) {
        Ok(_) => {
            let existing: Config = serde_json::from_slice(&bounded_regular_file(&config_path, 524_288)?)
                .map_err(|e| format!("existing controller config: {e}"))?;
            return Ok(existing.consent_full_readiness);
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => return Err(format!("existing controller config: {e}")),
    }
    if spec.dispatch.is_none() { return Ok(None); }
    let pins = json!({"mini":spec.mini, "miniSha256":sha256_file(&spec.mini)?,
        "host":spec.host, "hostSha256":sha256_pinned_file(&spec.host)?,
        "hostConfig":spec.host_config, "hostConfigSha256":sha256_file(&spec.host_config)?});
    let output = run_with_limit(Command::new(&spec.mini).arg("consent-full-ready")
        .arg("--host").arg(&spec.host).arg("--config").arg(&spec.host_config),
        "prepare dispatch controller full consent", deadline::startup_limit(None)?)?;
    let receipt = ConsentFullReadiness::parse(&output)?;
    let after = json!({"mini":spec.mini, "miniSha256":sha256_file(&spec.mini)?,
        "host":spec.host, "hostSha256":sha256_pinned_file(&spec.host)?,
        "hostConfig":spec.host_config, "hostConfigSha256":sha256_file(&spec.host_config)?});
    if after != pins { return Err("full-consent provisioning inputs changed during preparation".into()); }
    let bytes = serde_json::to_vec_pretty(&json!({"type":"mini-grain-create-consent-readiness-v1",
        "inputs":pins,"receipt":receipt})).map_err(|e| e.to_string())?;
    let path = work.join("consent-full-readiness.json");
    match fs::read(&path) {
        Ok(old) if old == bytes => {}
        Ok(_) => return Err("retained full-consent provisioning receipt differs".into()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => write_private_new(&path, &bytes)?,
        Err(e) => return Err(format!("full-consent provisioning receipt: {e}")),
    }
    Ok(Some(true))
}

fn confirmed(outcome: &Path) -> Result<bool> {
    let bytes = match fs::read(outcome) {
        Ok(bytes) => bytes,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(false),
        Err(e) => return Err(format!("{}: {e}", outcome.display())),
    };
    let value: Value = serde_json::from_slice(&bytes).map_err(|e| format!("{}: {e}", outcome.display()))?;
    match value["type"].as_str() {
        Some("confirmed") => Ok(true),
        Some("refused") => Err(format!("the Host refused this step ({}): {}", outcome.display(), value)),
        _ => Ok(false),
    }
}

/// Resolve one signed step. A fresh attempt directory runs `submit`; an
/// existing one without a confirmed outcome is only ever looked up.
fn signed_step(spec: &Spec, attempt: &Path, what: &str, submit: impl FnOnce() -> Result<()>) -> Result<()> {
    signed_step_on(spec, &spec.host_socket, attempt, what, submit)
}

fn signed_step_on(spec: &Spec, socket: &Path, attempt: &Path, what: &str, submit: impl FnOnce() -> Result<()>) -> Result<()> {
    let outcome = attempt.join("outcome.json");
    if !attempt.exists() {
        // A submitter may exit nonzero after the reply was lost; the outcome
        // file and the lookup below decide, not its status.
        if let Err(error) = submit() {
            eprintln!("grain-runtime create: {what}: {error}; resolving by exact lookup");
        }
    }
    if confirmed(&outcome)? {
        return Ok(());
    }
    if !attempt.join("call.bin").exists() {
        return Err(format!("{what}: no signed call was retained at {}; nothing was submitted, remove only that attempt directory after inspecting it", attempt.display()));
    }
    run(Command::new(&spec.mini).arg("retry").arg("--attempt").arg(attempt).args(["--mode", "lookup"])
        .arg("--socket").arg(socket), &format!("{what} lookup"))?;
    if confirmed(&outcome)? {
        return Ok(());
    }
    Err(format!("{what}: undecided after exact lookup; rerun `grain-runtime create` with the same spec to look it up again (attempt {})", attempt.display()))
}

/// How many fresh read-and-author generations one create tries before it stops
/// and says so; each is one signed read and one Host authoring, never a fee.
const AUTHOR_GENERATIONS: usize = 8;

/// Read authority and author through the live Host before signing a fresh birth.
/// Read-only generations are retained separately: a crash before submit can
/// acquire a fresh window without replacing any possibly admitted signed call.
/// The Host authors only against the exact image the signed read observed, so a
/// World that moved in between (a clock tick, a certify) refuses that
/// generation; the next generation reads again.
fn author_birth(spec: &Spec, socket: &Path, source: &Path, genesis: &Value, work: &Path) -> Result<PathBuf> {
    let factory = genesis["factoryId"].as_str().ok_or("genesis lacks factoryId")?;
    let grants: Vec<_> = spec.sponsor.grants.iter()
        .filter(|grant| grant.kind == "object" && grant.target == factory).collect();
    if grants.len() != 1 {
        return Err("grain birth requires exactly one sponsor factory observation grant".into());
    }
    let mut last = String::new();
    for _ in 0..AUTHOR_GENERATIONS {
        let generation = (0u64..).find_map(|number| {
            let path = work.join(format!("birth-author-{number}"));
            match fs::DirBuilder::new().mode(0o700).create(&path) {
                Ok(()) => Some(Ok(path)),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => None,
                Err(error) => Some(Err(format!("create birth author generation: {error}"))),
            }
        }).ok_or("birth author generation exhausted")??;
        let query_source = generation.join("factory-query.json");
        let query = json!({"subject":spec.sponsor.subject,"nonce":spec.nonce,
            "purpose":{"type":"query","kind":"object","target":factory,"view":"resource"},
            "grants":[grants[0]]});
        write_private_new(&query_source, &serde_json::to_vec(&query).map_err(|e| e.to_string())?)?;
        let observation = generation.join("factory-query");
        if let Err(error) = run(Command::new(&spec.mini).arg("query").arg("--host").arg(&spec.host)
            .arg("--config").arg(&spec.host_config).arg("--socket").arg(socket)
            .arg("--intent").arg(&query_source).args(["--intent-kind", "intent", "--view", "resource"])
            .arg("--key").arg(&spec.sponsor.key).arg("--dir").arg(&observation), "mini query birth factory") {
            last = error;
            continue;
        }
        let author = generation.join("author");
        match run(Command::new(&spec.mini).arg("current-resource-intent").arg("--host").arg(&spec.host)
            .arg("--config").arg(&spec.host_config).arg("--socket").arg(socket)
            .arg("--source").arg(source).arg("--signed-observation").arg(observation.join("signed-observation.bin"))
            .arg("--dir").arg(&author), "mini author current grain birth") {
            Ok(_) if author.join("intent.bin").is_file() => return Ok(author.join("intent.bin")),
            Ok(_) => last = format!("mini author current grain birth left no intent in {}", author.display()),
            Err(error) => last = error,
        }
    }
    Err(format!("grain birth: {AUTHOR_GENERATIONS} read-and-author generations without an intent; last: {last}"))
}

fn submit_birth(spec: &Spec, socket: &Path, source: &Path, genesis: &Value, work: &Path) -> Result<()> {
    let birth = work.join("birth");
    signed_step_on(spec, socket, &birth, "grain birth", || {
        let authored = author_birth(spec, socket, source, genesis, work)?;
        run(Command::new(&spec.mini).arg("submit").arg("--host").arg(&spec.host)
            .arg("--config").arg(&spec.host_config).arg("--socket").arg(socket)
            .arg("--intent").arg(&authored).args(["--intent-kind", "binary"])
            .arg("--key").arg(&spec.sponsor.key).arg("--dir").arg(&birth), "mini submit birth").map(|_| ())
    })
}

fn init_workspace(spec: &Spec, key: &Key, dir: &Path) -> Result<()> {
    if dir.join("workspace.json").exists() {
        return Ok(());
    }
    if dir.exists() {
        return Err(format!("a partial workspace exists at {}; inspect it before rerunning", dir.display()));
    }
    let mut command = Command::new(&spec.mini);
    command.args(["workspace", "--action", "init", "--host"]).arg(&spec.host)
        .arg("--config").arg(&spec.host_config).arg("--socket").arg(&spec.host_socket)
        .arg("--key").arg(&key.key).arg("--subject").arg(&key.subject)
        .arg("--namespace-root").arg(&spec.namespace_root).arg("--dir").arg(dir);
    if key.no_prerotation {
        command.arg("--no-prerotation");
    }
    run(&mut command, "workspace init")?;
    Ok(())
}

fn write_private_new(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new().write(true).create_new(true).mode(0o600).open(path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    file.write_all(bytes).map_err(|e| format!("{}: {e}", path.display()))
}

/// The owner delegates RECIPIENT observe+mutate on the parent (its witness).
fn delegate_witness(spec: &Spec, work: &Path, owner_ws: &Path, id: &str, recipient: &str) -> Result<String> {
    let proposal = owner_ws.join(format!("proposals/{id}/proposal.json"));
    if !proposal.exists() {
        let request = work.join(format!("{id}-request.json"));
        if !request.exists() {
            write_private_new(&request, json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                "name":"parent","recipient":recipient,"verbs":["observe","mutate"],
                "maxCost":spec.budgets.witness_max_cost}).to_string().as_bytes())?;
        }
        run(Command::new(&spec.mini).args(["workspace", "--action", "propose", "--dir"]).arg(owner_ws)
            .arg("--request").arg(&request).args(["--proposal-id", id]), &format!("propose {id}"))?;
    }
    let attempt = owner_ws.join(format!("attempts/{id}"));
    signed_step(spec, &attempt, &format!("{id} delegation"), || {
        run(Command::new(&spec.mini).args(["workspace", "--action", "submit", "--dir"]).arg(owner_ws)
            .arg("--intent").arg(owner_ws.join(format!("proposals/{id}/intent.json")))
            .arg("--attempt").arg(&attempt), &format!("submit {id}")).map(|_| ())
    })?;
    let value: Value = serde_json::from_slice(&fs::read(&proposal).map_err(|e| format!("{id} proposal: {e}"))?)
        .map_err(|e| format!("{id} proposal: {e}"))?;
    let child = value["delegation"]["childCapability"].as_str()
        .ok_or_else(|| format!("{id} proposal names no childCapability"))?.to_owned();
    canonical_decimal(&child, "witness capability")?;
    Ok(child)
}

/// Who runs this create. `Whole` is the ordinary single-account create (and
/// the resident's part once the birth is confirmed). `Birth` is the
/// operator's part for a resident under its own uid: only the sponsor-signed
/// birth, through the operator's own socket; root then gives ROOT to the
/// resident, which runs `Whole` through its own operator route.
pub(crate) enum Phase { Whole, Birth { socket: PathBuf } }

pub(crate) fn create(spec_path: &Path) -> Result<Value> {
    create_phase(spec_path, Phase::Whole)
}

pub(crate) fn create_phase(spec_path: &Path, phase: Phase) -> Result<Value> {
    let spec_bytes = fs::read(spec_path).map_err(|e| format!("spec {}: {e}", spec_path.display()))?;
    let spec: Spec = serde_json::from_slice(&spec_bytes).map_err(|e| format!("spec: {e}"))?;
    spec.check(&phase)?;
    let spec_sha = sha256_bytes(&spec_bytes)?;
    let work = spec.root.join("create");
    // An existing EMPTY root is a fresh one: root pre-creates it for the
    // operator's birth phase in a directory the operator may not write.
    let empty_root = fs::read_dir(&spec.root).is_ok_and(|mut d| d.next().is_none());
    if spec.root.exists() && !empty_root {
        let recorded = fs::read_to_string(work.join("spec.sha256")).map_err(|_| {
            format!("root {} exists and is not a create of this spec; refusing to overwrite retained state", spec.root.display())
        })?;
        if recorded.trim() != spec_sha {
            return Err("root was created from a different spec; refusing".into());
        }
    } else {
        if !empty_root {
            fs::DirBuilder::new().mode(0o700).create(&spec.root).map_err(|e| format!("root: {e}"))?;
        }
        fs::DirBuilder::new().mode(0o700).create(&work).map_err(|e| format!("root/create: {e}"))?;
        write_private_new(&work.join("spec.json"), &spec_bytes)?;
        write_private_new(&work.join("spec.sha256"), format!("{spec_sha}\n").as_bytes())?;
    }

    let consent_readiness = if matches!(phase, Phase::Whole) {
        provision_consent_readiness(&spec, &work)?
    } else { None };

    // 1. The birth: both grains in one sponsor-signed intent. Once its outcome is
    // confirmed nothing here runs again, and genesis is not read.
    let birth = work.join("birth");
    if spec.needs_genesis(&phase)? {
        let genesis: Value = serde_json::from_slice(&fs::read(&spec.genesis).map_err(|e| format!("genesis: {e}"))?)
            .map_err(|e| format!("genesis: {e}"))?;
        let intent_path = work.join("birth-intent.json");
        let source = serde_json::to_vec(&spec.birth_intent(&genesis)).map_err(|e| e.to_string())?;
        if intent_path.exists() {
            if fs::read(&intent_path).map_err(|e| e.to_string())? != source {
                return Err("retained grain birth source differs from current spec/genesis".into());
            }
        } else {
            write_private_new(&intent_path, &source)?;
        }
        let birth_socket = match &phase { Phase::Birth { socket } => socket.clone(), Phase::Whole => spec.host_socket.clone() };
        submit_birth(&spec, &birth_socket, &intent_path, &genesis, &work)?;
    }

    if matches!(phase, Phase::Birth { .. }) {
        return Ok(json!({"type":"mini-grain-birth-v1","task":spec.task,"root":spec.root,
            "birthOutcome":birth.join("outcome.json"),
            "next":"give ROOT to the resident account, then run `grain-runtime create SPEC` as the resident"}));
    }

    // 2. The owner delegates the worker its parent witness.
    let owner_ws = work.join("owner-workspace");
    init_workspace(&spec, &spec.owner, &owner_ws)?;
    if !owner_ws.join("refs/parent.json").exists() {
        run(Command::new(&spec.mini).args(["workspace", "--action", "import", "--dir"]).arg(&owner_ws)
            .args(["--name", "parent", "--kind", "object", "--target"]).arg(&spec.task)
            .arg("--observe-capability").arg(&spec.capabilities.parent_observe)
            .arg("--control-capability").arg(&spec.capabilities.parent_control), "import parent")?;
    }
    let witness = delegate_witness(&spec, &work, &owner_ws, "witness", &spec.worker_key.subject)?;
    let provider_witness = match &spec.provider {
        Some(p) => Some(delegate_witness(&spec, &work, &owner_ws, "provider-witness", &p.key.subject)?),
        None => None,
    };

    let dispatch_witness = match &spec.dispatch {
        Some(d) => Some(delegate_witness(&spec, &work, &owner_ws, "dispatch-witness", &d.key.subject)?),
        None => None,
    };

    // 3. The controller's private state and the tool subject's workspace.
    let state = spec.root.join("state");
    if !state.exists() {
        fs::DirBuilder::new().mode(0o700).create(&state).map_err(|e| format!("state: {e}"))?;
    }
    init_workspace(&spec, &spec.worker_key, &state.join("resource-workspace"))?;
    // A room's tools keep their own home inside stateDir (the controller
    // refuses one elsewhere); create makes it, private.
    if let Some(home) = spec.room.as_ref().and_then(|r| r["home"].as_str()).map(PathBuf::from) {
        if home.parent() != Some(state.as_path()) {
            return Err("room.home must be a direct child of ROOT/state".into());
        }
        if !home.exists() {
            fs::DirBuilder::new().mode(0o700).create(&home).map_err(|e| format!("room home: {e}"))?;
        }
    }

    // 4. The controller config, decoded through the controller's own type.
    let config = spec.controller(&witness, provider_witness.as_deref(), dispatch_witness.as_deref(), consent_readiness);
    let typed: Config = serde_json::from_value(config.clone()).map_err(|e| format!("controller config refused by its own type: {e}"))?;
    // The same checks `serve` runs at open, so a bad config refuses here.
    crate::validate(&typed).map_err(|e| format!("controller config refused by the controller's validation: {e}"))?;
    let config_path = spec.root.join("controller.json");
    let bytes = serde_json::to_vec_pretty(&typed).map_err(|e| e.to_string())?;
    match fs::read(&config_path) {
        Ok(existing) if existing == bytes => {}
        Ok(_) => return Err(format!("{} exists with different contents; refusing", config_path.display())),
        Err(e) if e.kind() == io::ErrorKind::NotFound => write_private_new(&config_path, &bytes)?,
        Err(e) => return Err(format!("{}: {e}", config_path.display())),
    }
    Ok(json!({"type":"mini-grain-created-v1","task":spec.task,"toolTask":spec.tool_task,
        "owner":spec.owner.subject,"worker":spec.worker_key.subject,"witnessCapability":witness,
        "config":config_path,"configSha256":sha256_bytes(&bytes)?,
        "providerWitnessCapability":provider_witness,"dispatchWitnessCapability":dispatch_witness,"birthOutcome":birth.join("outcome.json"),
        "next":format!("install-controller --config {} ... (user shape) or --system --service-user ACCOUNT (root registration)", config_path.display())}))
}

pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let result = match args {
        [spec] => create(Path::new(spec))?,
        [spec, flag, socket] if flag == "--birth-socket" =>
            create_phase(Path::new(spec), Phase::Birth { socket: PathBuf::from(socket) })?,
        _ => return Err("usage: grain-runtime create /absolute/spec.json [--birth-socket OPERATOR-SOCKET]".into()),
    };
    println!("{result}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec_json() -> Value {
        json!({"type":SPEC_TYPE,"mini":"/m","host":"/h","hostConfig":"/c","hostSocket":"/s","genesis":"/g",
            "namespaceRoot":"/n","root":"/r","nonce":"22000",
            "sponsor":{"key":"/k","subject":"7","accountCapability":"41","grants":[{"kind":"account","target":"7","capability":"41"}]},
            "template":{"issuer":"5","ownerBudget":"100000","lifetime":"10000"},
            "owner":{"key":"/o","subject":"8","noPrerotation":true},
            "workerKey":{"key":"/w","subject":"9","noPrerotation":true},
            "task":"8751","toolTask":"8752",
            "capabilities":{"parentObserve":"8761","parentControl":"8762","toolObserve":"8771","toolControl":"8772"},
            "budgets":{"parent":"100","tool":"50","witnessMaxCost":"50000"},
            "worker":{"launcher":"/l/bwrap","runtimeRoot":"/rt","workspace":"/ws","network":"none",
                "wallTimeSeconds":600,"reserve":"3","charge":"1"},
            "toolCharges":{"reserve":"2","charge":"1"}})
    }

    struct BirthFixture(PathBuf);
    impl BirthFixture {
        fn new() -> Self {
            static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
            let path = std::env::temp_dir().join(format!("mini-create-birth-{}-{}", std::process::id(),
                NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
        fn spec(&self) -> Spec {
            let mut value = spec_json();
            value["mini"] = json!(self.0.join("mini"));
            value["sponsor"]["grants"].as_array_mut().unwrap().push(
                json!({"kind":"object","target":"2","capability":"42"}));
            serde_json::from_value(value).unwrap()
        }
        fn install_mini(&self) {
            // A transport double: verify orchestration/retention, not Host admission.
            fs::write(self.0.join("mini"), r#"#!/bin/sh
set -eu
root=${0%/*}
verb=$1
printf '%s\n' "$*" >> "$root/calls"
shift
dir=''
while [ "$#" -gt 0 ]; do
  case "$1" in --dir|--attempt) dir=$2;; esac
  shift 2
done
mkdir -p "$dir"
case "$verb" in
 query) printf signed-current-factory > "$dir/signed-observation.bin";;
 current-resource-intent) printf current-canonical-birth > "$dir/intent.bin";;
 submit) printf exact-signed-call > "$dir/call.bin"; exit 1;;
 retry) printf '{"type":"confirmed"}' > "$dir/outcome.json";;
 *) exit 2;;
esac
"#).unwrap();
            fs::set_permissions(self.0.join("mini"), fs::Permissions::from_mode(0o700)).unwrap();
        }
    }
    impl Drop for BirthFixture {
        fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); }
    }

    #[test]
    fn create_birth_uses_current_signed_factory_and_binary_then_exact_lookup() {
        let fixture = BirthFixture::new(); fixture.install_mini();
        let spec = fixture.spec();
        let source = fixture.0.join("source.json");
        fs::write(&source, b"{}").unwrap();
        let socket = Path::new("/operator-live.sock");
        submit_birth(&spec, socket, &source, &json!({"factoryId":"2"}), &fixture.0).unwrap();
        let calls = fs::read_to_string(fixture.0.join("calls")).unwrap();
        let rows: Vec<_> = calls.lines().collect();
        assert_eq!(rows.len(), 4);
        assert!(rows[0].starts_with("query "));
        assert!(rows[0].contains("--view resource "), "the query must name a view `mini query` accepts: {}", rows[0]);
        assert!(rows[1].starts_with("current-resource-intent "));
        assert!(rows[1].contains("factory-query/signed-observation.bin"));
        assert!(rows[2].contains("author/intent.bin --intent-kind binary"));
        assert!(rows[3].starts_with("retry ") && rows[3].contains("--mode lookup"));
        assert!(rows.iter().all(|row| row.contains("--socket /operator-live.sock")));
        let query: Value = serde_json::from_slice(&fs::read(fixture.0.join("birth-author-0/factory-query.json")).unwrap()).unwrap();
        assert_eq!(query["purpose"]["target"], "2");
        assert_eq!(query["grants"], json!([{"kind":"object","target":"2","capability":"42"}]));
        // A lost confirmation on a rerun must not query, author, or submit again.
        fs::remove_file(fixture.0.join("birth/outcome.json")).unwrap();
        submit_birth(&spec, socket, &source, &json!({"factoryId":"2"}), &fixture.0).unwrap();
        let again = fs::read_to_string(fixture.0.join("calls")).unwrap();
        assert_eq!(again.lines().count(), 5);
        assert!(again.lines().last().unwrap().starts_with("retry "));
        assert!(!fixture.0.join("birth-author-1").exists());
    }

    #[test]
    fn the_resident_half_reads_no_genesis_once_the_birth_is_confirmed() {
        let fixture = BirthFixture::new();
        let mut value = spec_json();
        value["root"] = json!(fixture.0);
        let spec: Spec = serde_json::from_value(value).unwrap();
        let operator = Phase::Birth { socket: PathBuf::from("/operator.sock") };
        assert!(spec.needs_genesis(&Phase::Whole).unwrap(), "no birth yet: the birth needs genesis");
        fs::create_dir_all(fixture.0.join("create/birth")).unwrap();
        fs::write(fixture.0.join("create/birth/outcome.json"), br#"{"type":"undecided"}"#).unwrap();
        assert!(spec.needs_genesis(&Phase::Whole).unwrap(), "an undecided birth is still looked up");
        fs::write(fixture.0.join("create/birth/outcome.json"), br#"{"type":"confirmed"}"#).unwrap();
        assert!(!spec.needs_genesis(&Phase::Whole).unwrap());
        assert!(spec.needs_genesis(&operator).unwrap());
    }

    #[test]
    fn create_birth_reads_again_when_the_host_refuses_an_authoring() {
        let fixture = BirthFixture::new(); fixture.install_mini();
        // The first authoring is refused (the World moved after the read), as the Host
        // refuses an observation of an image it no longer holds.
        let mini = fs::read_to_string(fixture.0.join("mini")).unwrap().replace(
            " current-resource-intent) printf current-canonical-birth > \"$dir/intent.bin\";;",
            " current-resource-intent) if [ ! -e \"$root/refused-once\" ]; then : > \"$root/refused-once\"; exit 1; fi; printf current-canonical-birth > \"$dir/intent.bin\";;");
        assert!(mini.contains("refused-once"));
        fs::write(fixture.0.join("mini"), mini).unwrap();
        let spec = fixture.spec(); let socket = Path::new("/s");
        let source = fixture.0.join("source.json"); fs::write(&source, b"{}").unwrap();
        let authored = author_birth(&spec, socket, &source, &json!({"factoryId":"2"}), &fixture.0).unwrap();
        assert_eq!(authored, fixture.0.join("birth-author-1/author/intent.bin"));
        let calls = fs::read_to_string(fixture.0.join("calls")).unwrap();
        assert_eq!(calls.lines().filter(|row| row.starts_with("query ")).count(), 2);
        assert!(!fixture.0.join("birth-author-0/author/intent.bin").exists());
    }

    #[test]
    fn create_birth_unsubmitted_authoring_keeps_generations_and_requires_unique_factory_grant() {
        let fixture = BirthFixture::new(); fixture.install_mini();
        let mut spec = fixture.spec(); let socket = Path::new("/s");
        let source = fixture.0.join("source.json"); fs::write(&source, b"{}").unwrap();
        let genesis = json!({"factoryId":"2"});
        let first = author_birth(&spec, socket, &source, &genesis, &fixture.0).unwrap();
        let second = author_birth(&spec, socket, &source, &genesis, &fixture.0).unwrap();
        assert_ne!(first, second); assert!(first.exists() && second.exists());
        spec.sponsor.grants.push(spec.sponsor.grants[1].clone());
        assert!(author_birth(&spec, socket, &source, &genesis, &fixture.0).unwrap_err().contains("exactly one"));
        spec.sponsor.grants.retain(|g| g.kind != "object");
        assert!(author_birth(&spec, socket, &source, &genesis, &fixture.0).unwrap_err().contains("exactly one"));
        assert!(!fixture.0.join("birth-author-2").exists());
        // A partial signed-attempt directory is retained and does not reauthor.
        fs::create_dir(fixture.0.join("birth")).unwrap();
        assert!(submit_birth(&spec, socket, &source, &genesis, &fixture.0).unwrap_err().contains("no signed call"));
        assert!(!fixture.0.join("birth-author-2").exists());
    }

    #[test]
    fn create_full_consent_skips_plain_grains_and_preserves_published_config() {
        let fixture = BirthFixture::new();
        let mut spec = fixture.spec();
        spec.root = fixture.0.clone();
        // No executable exists: plain creation must not probe or replay consent.
        assert_eq!(provision_consent_readiness(&spec, &fixture.0).unwrap(), None);
        spec.dispatch = serde_json::from_value(with_dispatch()["dispatch"].clone()).unwrap();
        for setting in [None, Some(false), Some(true)] {
            let config = spec.controller("8790", None, Some("8792"), setting);
            let bytes = serde_json::to_vec_pretty(&config).unwrap();
            fs::write(spec.root.join("controller.json"), &bytes).unwrap();
            assert_eq!(provision_consent_readiness(&spec, &fixture.0).unwrap(), setting);
            assert_eq!(fs::read(spec.root.join("controller.json")).unwrap(), bytes);
        }
        assert!(!fixture.0.join("consent-full-readiness.json").exists());
    }

    #[test]
    fn create_dispatch_enables_full_consent_only_after_exact_native_ack() {
        let fixture = BirthFixture::new();
        let mut spec: Spec = serde_json::from_value(with_dispatch()).unwrap();
        spec.root = fixture.0.clone();
        spec.mini = fixture.0.join("mini");
        spec.host = fixture.0.join("host");
        spec.host_config = fixture.0.join("host-config.json");
        fs::write(&spec.host, b"pinned Host").unwrap();
        fs::write(&spec.host_config, b"pinned settings").unwrap();
        // A transport double, not native admission: it rejects all signed verbs.
        fs::write(&spec.mini, r#"#!/bin/sh
set -eu
[ "$1" = consent-full-ready ] || exit 90
root=${0%/*}
printf '%s\n' "$*" >> "$root/readiness-calls"
cat "$root/readiness-reply"
"#).unwrap();
        fs::set_permissions(&spec.mini, fs::Permissions::from_mode(0o700)).unwrap();
        for reply in ["unsupported", "", r#"{"type":"mini-consent-full-readiness-v1","ready":false}"#,
            r#"{"type":"mini-consent-full-readiness-v1","ready":true,"extra":1}"#] {
            fs::write(fixture.0.join("readiness-reply"), reply).unwrap();
            assert!(provision_consent_readiness(&spec, &fixture.0).is_err());
            assert!(!fixture.0.join("consent-full-readiness.json").exists());
            assert!(!fixture.0.join("controller.json").exists());
        }
        fs::write(fixture.0.join("readiness-reply"),
            br#"{"type":"mini-consent-full-readiness-v1","ready":true}"#).unwrap();
        let selected = provision_consent_readiness(&spec, &fixture.0).unwrap();
        assert_eq!(selected, Some(true));
        let config = spec.controller("8790", None, Some("8792"), selected);
        assert_eq!(config["consentFullReadiness"], true);
        let evidence = fixture.0.join("consent-full-readiness.json");
        let original = fs::read(&evidence).unwrap();
        let proof: Value = serde_json::from_slice(&original).unwrap();
        assert_eq!(proof["inputs"]["miniSha256"], sha256_file(&spec.mini).unwrap());
        assert_eq!(proof["receipt"]["ready"], true);
        assert_eq!(provision_consent_readiness(&spec, &fixture.0).unwrap(), Some(true));
        assert_eq!(fs::read(&evidence).unwrap(), original);
        fs::write(&spec.host_config, b"different settings").unwrap();
        assert!(provision_consent_readiness(&spec, &fixture.0).unwrap_err().contains("receipt differs"));
        assert_eq!(fs::read(&evidence).unwrap(), original);
    }

    #[test]
    fn create_spec_refuses_every_missing_field_and_unknown_field() {
        let full = spec_json();
        serde_json::from_value::<Spec>(full.clone()).unwrap();
        for field in full.as_object().unwrap().keys() {
            let mut partial = full.clone();
            partial.as_object_mut().unwrap().remove(field);
            assert!(serde_json::from_value::<Spec>(partial).is_err(), "missing {field} accepted");
        }
        let mut extra = full.clone();
        extra["typo"] = json!(1);
        assert!(serde_json::from_value::<Spec>(extra).is_err());
        let mut nested = full;
        nested["worker"].as_object_mut().unwrap().remove("network");
        assert!(serde_json::from_value::<Spec>(nested).is_err());
    }

    #[test]
    fn create_writes_a_config_the_controller_type_accepts() {
        let spec: Spec = serde_json::from_value(spec_json()).unwrap();
        let config = spec.controller("8790", None, None, None);
        let typed: Config = serde_json::from_value(config.clone()).unwrap();
        assert_eq!(typed.task, "8751");
        assert_eq!(config["toolTask"]["parentCapability"], "8790");
        assert_eq!(config["commands"][0]["args"][5], "none");
        assert_eq!(config["controlSocket"], "/r/state/control.sock");
        let intent = spec.birth_intent(&json!({"g":1}));
        assert_eq!(intent["birth"]["resources"][1]["owner"], "9");
        assert_eq!(intent["birth"]["resources"][0]["workerSubjects"], json!(["9"]));
        let mut with = spec_json();
        with["provider"] = json!({"key":{"key":"/p","subject":"10","noPrerotation":true},"task":"8753",
            "observeCapability":"8781","controlCapability":"8782","budget":"50",
            "gateway":{"providers":"/etc/mini/providers.json","credentialBroker":"/etc/mini/keys-client.json",
                "gatewayBind":"127.0.0.1:18761","model":"m","reserve":"30000","maxInputTokens":1000,
                "maxOutputTokens":100,"maxRequestBytes":1048576,"maxResponseBytes":8388608,"timeoutSeconds":600}});
        let spec: Spec = serde_json::from_value(with.clone()).unwrap();
        spec.check_values().unwrap();
        let intent = spec.birth_intent(&json!({}));
        assert_eq!(intent["birth"]["resources"][0]["workerSubjects"], json!(["9", "10"]));
        assert_eq!(intent["birth"]["resources"][2]["owner"], "10");
        let config = spec.controller("8790", Some("8791"), None, None);
        assert_eq!(config["providerTask"]["parentCapability"], "8791");
        assert_eq!(config["providerTask"]["subject"], "10");
        serde_json::from_value::<Config>(config).unwrap();
        with["dispatch"] = with_dispatch()["dispatch"].clone();
        let both: Spec = serde_json::from_value(with.clone()).unwrap();
        both.check_values().unwrap();
        let config: Config = serde_json::from_value(both.controller("8790", Some("8791"), Some("8792"), Some(true))).unwrap();
        let workers = ordered_worker_subjects(
            config.tool_task.as_ref().map(|v| v.subject.as_str()),
            config.provider_task.as_ref().map(|v| v.subject.as_str()),
            config.dispatch_task.as_ref().map(|v| v.subject.as_str()));
        assert_eq!(workers, ["9", "10", "11"]);
        assert_eq!(both.birth_intent(&json!({}))["birth"]["resources"][0]["workerSubjects"], json!(workers));
        with["provider"]["gateway"]["task"] = json!("1");
        assert!(serde_json::from_value::<Spec>(with).unwrap().check_values().unwrap_err().contains("must not set task"));
    }

    fn with_dispatch() -> Value {
        let mut spec = spec_json();
        spec["dispatch"] = json!({"key":{"key":"/d","subject":"11","noPrerotation":true},
            "task":"8754","observeCapability":"8783","controlCapability":"8784","budget":"50",
            "transport":{"reserve":"2","charge":"1","socketPath":"/operator/reverse.sock",
                "hostUid":1001,"operatorSocket":"/controller/operator.sock","operatorPeerUid":0,
                "reserveSigner":{"role":"4","index":"0","publicKey":"00".repeat(32),
                    "keyId":"1111","keyEpoch":"2"}}});
        spec
    }

    #[test]
    fn create_dispatch_binds_birth_witness_and_controller_to_same_purse() {
        let spec: Spec = serde_json::from_value(with_dispatch()).unwrap();
        spec.check_values().unwrap();
        let birth = spec.birth_intent(&json!({}));
        assert_eq!(birth["birth"]["resources"][0]["workerSubjects"], json!(["9", "11"]));
        let resource = &birth["birth"]["resources"][2];
        let typed: Config = serde_json::from_value(spec.controller("8790", None, Some("8792"), Some(true))).unwrap();
        let dispatch = typed.dispatch_task.unwrap();
        assert_eq!(dispatch.task, resource["target"]);
        assert_eq!(dispatch.subject, resource["owner"]);
        assert_eq!(dispatch.capability, resource["ownerCapability"]);
        assert_eq!(dispatch.parent_capability, "8792");
        assert_eq!(dispatch.parent_observe_capability, "8792");
        assert_ne!(dispatch.task, typed.tool_task.unwrap().task);
        assert_eq!(dispatch.operator_peer_uid, Some(0));
    }

    #[test]
    fn create_dispatch_refuses_role_aliases_and_transport_overrides_before_birth() {
        for (field, value) in [("task", json!("8751")), ("task", json!("8752")),
            ("observeCapability", json!("8761")), ("controlCapability", json!("8783"))] {
            let mut bad = with_dispatch(); bad["dispatch"][field] = value;
            assert!(serde_json::from_value::<Spec>(bad).unwrap().check_values().is_err(), "accepted {field}");
        }
        for (field, value) in [("subject", json!("8")), ("subject", json!("9")), ("key", json!("/w"))] {
            let mut bad = with_dispatch(); bad["dispatch"]["key"][field] = value;
            assert!(serde_json::from_value::<Spec>(bad).unwrap().check_values().is_err(), "accepted {field}");
        }
        for (field, value) in [("task", json!("999")), ("unknown", json!("x")),
            ("charge", json!("3")), ("reserve", json!("0")), ("hostUid", json!(0)),
            ("operatorSocket", json!("/s"))] {
            let mut bad = with_dispatch(); bad["dispatch"]["transport"][field] = value;
            assert!(serde_json::from_value::<Spec>(bad).unwrap().check_values().is_err(), "accepted {field}");
        }
        for field in ["socketPath", "hostUid", "reserveSigner", "operatorSocket"] {
            let mut bad = with_dispatch(); bad["dispatch"]["transport"].as_object_mut().unwrap().remove(field);
            assert!(serde_json::from_value::<Spec>(bad).unwrap().check_values().is_err(), "missing {field}");
        }
    }

    #[test]
    fn create_check_refuses_bad_values_before_touching_the_filesystem() {
        let mut bad = spec_json();
        bad["task"] = json!("08751");
        let spec: Spec = serde_json::from_value(bad).unwrap();
        assert!(spec.check_values().unwrap_err().contains("task must be canonical"));
        serde_json::from_value::<Spec>(spec_json()).unwrap().check_values().unwrap();
        let mut wrong = spec_json();
        wrong["type"] = json!("other");
        assert!(serde_json::from_value::<Spec>(wrong).unwrap().check_values().unwrap_err().contains("spec type"));
        let mut same = spec_json();
        same["workerKey"]["subject"] = json!("8");
        assert!(serde_json::from_value::<Spec>(same).unwrap().check_values().unwrap_err().contains("distinct"));
        let mut caps = spec_json();
        caps["capabilities"]["toolControl"] = json!("8761");
        assert!(serde_json::from_value::<Spec>(caps).unwrap().check_values().unwrap_err().contains("distinct"));
        let mut net = spec_json();
        net["worker"]["network"] = json!("bridge");
        assert!(serde_json::from_value::<Spec>(net).unwrap().check_values().is_err());
    }
}
