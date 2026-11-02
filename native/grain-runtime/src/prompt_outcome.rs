//! The one typed per-prompt outcome record (gr §4.3). The controller writes
//! it at the moment a Hermes prompt ends, once, next to the prompt's other
//! retained artifacts in `stateDir`. It is the only input to resident
//! failed-prompt reconciliation, to a resident request's terminal status and
//! to automatic effects acknowledgement: nothing downstream infers an outcome
//! from presentation labels, note prefixes or process liveness.
//!
//! Three states, each decided by the controller at the prompt boundary:
//! * `admitted`: the turn ended `end_turn` and the parent hold settled; the
//!   receipt fields name what was settled.
//! * `refused`: the turn is decided and closed without a deliverable result
//!   (a typed turn failure at a settled boundary, a setup failure settled at
//!   zero, a preadmission refusal, or a controller refusal that left no
//!   retained custody). `reason` is the decoded reason.
//! * `undecided`: custody is still retained. `retry` names the exact admin
//!   commands, in order, that resolve it and the operation they act on. An
//!   undecided record stays immutable. Only an explicit, hash-bound audited
//!   resolution can close it as refused without claiming a deliverable result.
use crate::*;

pub(crate) const KIND: &str = "mini-prompt-outcome-v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Record {
    #[serde(rename = "type")]
    pub(crate) kind: String,
    pub(crate) prompt_operation_id: u64,
    pub(crate) resident_prompt_id: Option<String>,
    pub(crate) prompt_sha256: Option<String>,
    pub(crate) session_id: Option<String>,
    pub(crate) outcome: Outcome,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "state", rename_all = "kebab-case", deny_unknown_fields)]
pub(crate) enum Outcome {
    #[serde(rename_all = "camelCase")]
    Admitted {
        stop_reason: String,
        settled_charge: String,
        provider_response_sha256: Option<String>,
        provider_metered_charge: Option<String>,
    },
    #[serde(rename_all = "camelCase")]
    Refused { stage: RefusalStage, reason: String },
    #[serde(rename_all = "camelCase")]
    Undecided { retry: Retry, detail: String },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum RefusalStage {
    /// Refused before the prompt was admitted; no model request was made.
    Preadmission,
    /// The worker or session could not start; the hold settled at zero.
    Setup,
    /// The prompt was admitted and its typed turn failure settled.
    TurnFailure,
    /// The controller refused after allocating the prompt and retained no
    /// custody: no hold, attempt, worker or external-effect note remains.
    Controller,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Retry {
    /// Exact `grain-runtime admin SOCKET CMD` commands, in order.
    pub(crate) admin: Vec<String>,
    /// The retained native attempt the first command looks up, when one is.
    pub(crate) operation: Option<u64>,
}

impl Record {
    pub(crate) fn validate(&self) -> Result<()> {
        let digest = |v: &Option<String>| v.as_ref().is_none_or(|s| resident_origin::valid_digest(s));
        let ok = self.kind == KIND
            && self.prompt_operation_id > 0
            && digest(&self.resident_prompt_id)
            && digest(&self.prompt_sha256)
            && self.resident_prompt_id.is_some() == self.prompt_sha256.is_some()
            && self.session_id.as_ref().is_none_or(|s| !s.is_empty() && s.len() <= 128)
            && match &self.outcome {
                Outcome::Admitted { stop_reason, settled_charge, .. } => {
                    stop_reason == "end_turn" && decimal_text(settled_charge)
                }
                Outcome::Refused { reason, .. } => !reason.is_empty() && reason.len() <= 4096,
                Outcome::Undecided { retry, detail } => {
                    !retry.admin.is_empty()
                        && retry.admin.iter().all(|c| admin_command(c))
                        && detail.len() <= 4096
                }
            };
        if ok { Ok(()) } else { Err("prompt outcome record is malformed".into()) }
    }
}

fn decimal_text(s: &str) -> bool {
    !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) && (s == "0" || !s.starts_with('0'))
}

/// The admin verbs an undecided prompt may name. Each resolves retained
/// custody by exact lookup or operator audit; none resubmits the prompt.
fn admin_command(c: &str) -> bool {
    matches!(c, "recover" | "reconcile parent audited" | "reconcile tool audited"
        | "reconcile provider audited" | "reconcile worker audited" | "reconcile effects")
}

pub(crate) fn path(state_dir: &Path, prompt: u64) -> PathBuf {
    state_dir.join(format!("prompt-outcome-{prompt:016}.json"))
}

/// Write once. A second write must carry identical bytes; a differing record
/// for the same prompt is refused (the first decision stands).
pub(crate) fn write(state_dir: &Path, record: &Record) -> Result<()> {
    record.validate()?;
    let bytes = serde_json::to_vec_pretty(record).map_err(|e| e.to_string())?;
    let target = path(state_dir, record.prompt_operation_id);
    match fs::symlink_metadata(&target) {
        Ok(_) => {
            if bounded_regular_file(&target, 65_536)? == bytes {
                return Ok(());
            }
            Err(format!("prompt {} already has a different outcome record", record.prompt_operation_id))
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            journal_io::write(&target, &bytes).map_err(|e| format!("prompt outcome record: {e}"))
        }
        Err(e) => Err(format!("prompt outcome record: {e}")),
    }
}

fn read_original(state_dir: &Path, prompt: u64) -> Result<Option<Record>> {
    let target = path(state_dir, prompt);
    match fs::symlink_metadata(&target) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(format!("prompt outcome record: {e}")),
        Ok(meta) => {
            if !meta.is_file() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
                return Err("prompt outcome record must be an owned private regular file".into());
            }
            let record: Record = serde_json::from_slice(&bounded_regular_file(&target, 65_536)?)
                .map_err(|e| format!("prompt outcome record: {e}"))?;
            record.validate()?;
            if record.prompt_operation_id != prompt {
                return Err("prompt outcome record names another prompt".into());
            }
            Ok(Some(record))
        }
    }
}

/// An audit closes uncertainty without rewriting the original decision or
/// asserting that the worker performed no effects. This is a terminal refusal
/// to deliver a result, not a synthetic successful turn or NoDispatch proof.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AuditedResolution {
    #[serde(rename = "type")]
    kind: String,
    original_sha256: String,
    controller_identity: Value,
    audit: Vec<Value>,
    reserve_source: String,
    reserve_source_sha256: String,
    reserve_outcome: String,
    reserve_outcome_sha256: String,
    record: Record,
}

fn resolution_path(state: &Path, prompt: u64) -> PathBuf {
    state.join(format!("prompt-resolution-{prompt:016}.json"))
}

fn decision(row: &Value) -> Option<u64> {
    let s = row["decisionId"].as_str()?;
    let n = s.parse::<u64>().ok()?;
    (n.to_string() == s).then_some(n)
}

/// The narrow supported closure is a stranded worker followed by native
/// parent settlement and source-derived or explicit effects closure, in that order.
/// Mere idle state, a note string, or an unrelated old audit cannot close it.
fn audit_chain(rows: &[Value], record: &Record) -> Result<Vec<Value>> {
    let Outcome::Undecided { retry, .. } = &record.outcome else {
        return Err("only an undecided prompt can be audited".into());
    };
    if retry.operation.is_some()
        || retry.admin.is_empty()
        || retry.admin.iter().any(|v| !matches!(v.as_str(),
            "reconcile worker audited" | "reconcile provider audited" | "reconcile parent audited" | "reconcile effects")) {
        return Err("prompt audit requires the retained worker/parent recovery boundary".into());
    }
    let op = record.prompt_operation_id;
    let worker = rows.iter().find(|r| decision(r).is_some_and(|d| d > op)
        && r["operationId"] == op.to_string()
        && ((r["action"] == "recover-gated-worker" && r["stage"] == "physical-stop-verified" && r["machineProven"] == true)
            || (r["action"] == "clear-stranded-child-after-physical-audit"
                && r["stage"] == "physical-audit-recorded" && r["operatorAudited"] == true)));
    if retry.admin.iter().any(|v| v == "reconcile worker audited") && worker.is_none() {
        return Err("prompt has no exact worker stop audit".into());
    }
    let after_worker = worker.and_then(decision).unwrap_or(op);
    let mut chain = Vec::new();
    if let Some(w) = worker {
        chain.push(w.clone());
    }
    if retry.admin.iter().any(|v| v == "reconcile provider audited") {
        let is_provider_req = |r: &Value| decision(r).is_some_and(|d| d > after_worker)
            && r["authority"] == "provider"
            && ((r["action"] == "settle-provider-source-metered-charge"
                && matches!(r["stage"].as_str(), Some("operator-audited-requested" | "delivered-response-recovery-requested")))
                || (r["action"] == "abort-definitively-unreserved-provider-request"
                    && r["stage"] == "signed-origin-confirmed"));
        let is_provider_settled = |req: &Value, r: &Value| decision(r) == decision(req)
            && r["authority"] == "provider"
            && matches!(r["stage"].as_str(), Some("signed-settlement-confirmed" | "operator-audited-terminal-without-held-receipt"));
        let provider_req = rows.iter().find(|r| is_provider_req(r)
            && (r["action"] != "settle-provider-source-metered-charge"
                || rows.iter().any(|s| is_provider_settled(r, s))))
            .or_else(|| rows.iter().find(|r| is_provider_req(r)))
            .ok_or("prompt has no subsequent provider audit request")?;
        chain.push(provider_req.clone());
        if provider_req["action"] == "settle-provider-source-metered-charge" {
            let provider_settled = rows.iter().find(|r| is_provider_settled(provider_req, r))
                .ok_or("prompt provider settlement is not confirmed")?;
            chain.push(provider_settled.clone());
        }
    }
    let is_parent_req = |r: &Value| decision(r).is_some_and(|d| d > after_worker)
        && r["authority"] == "parent" && r["action"] == "settle-held-allowance"
        && r["stage"] == "requested" && r["reserveAttempt"].as_str().is_some();
    let is_parent_settled = |req: &Value, r: &Value| decision(r) == decision(req)
        && r["authority"] == "parent"
        && matches!(r["stage"].as_str(), Some("signed-settlement-confirmed" | "confirmed-no-active-reservation"));
    let parent = rows.iter().find(|r| is_parent_req(r) && rows.iter().any(|s| is_parent_settled(r, s)))
        .or_else(|| rows.iter().find(|r| is_parent_req(r)))
        .ok_or("prompt has no subsequent exact parent settlement request")?;
    let settled = rows.iter().find(|r| is_parent_settled(parent, r))
        .ok_or("prompt parent settlement is not confirmed")?;
    let effects = rows.iter().find(|r| decision(r).is_some_and(|d| d > decision(parent).unwrap())
        && r["stage"] == "acknowledged" && r["externalEffectsAcknowledged"] == true
        && ((r["action"] == "acknowledge-external-effects" && r["automatic"] == false)
            || (r["action"] == "derive-no-unaccounted-external-effects" && r["automatic"] == true
                && r["basis"] == "derived: scoped --network none worker whose only external channel is the Mini broker; every Mini attempt resolved; no provider or dispatch attempt outstanding"))
        && r["details"].as_array().is_some_and(|details| details.iter().any(|v|
            v.as_str() == Some(format!("worker operation {op} stopped after controller restart; external effects need acknowledgement").as_str())
            || v.as_str() == Some("parent reserved operation may have external effects; explicit operator acknowledgement required")
            || v.as_str() == Some("parent confirmed reservation was externally settled; explicit effects acknowledgement required")
            || v.as_str().is_some_and(|s| s.starts_with(&format!("Hermes prompt {op}: "))
                || s == "provider reservation fenced; external send/response requires exact audit"
                || (s.starts_with("provider request ") && s.ends_with(" external effects require explicit acknowledgement"))))))
        .ok_or("prompt lacks subsequent bound external-effects closure")?;
    chain.push(parent.clone());
    chain.push(settled.clone());
    chain.push(effects.clone());
    Ok(chain)
}

/// Identity survives legitimate controller policy/enrollment updates. The
/// complete audit and reserve artifacts remain immutable in the resolution;
/// reading historical refusal does not depend on unbounded mutable log rows.
fn controller_identity(binding: &Value) -> Result<Value> {
    let mut value = serde_json::Map::new();
    for name in ["stateDir", "task", "subject", "capability", "queryCapability", "custodyKey", "hostConfig"] {
        let field = binding["config"][name].as_str().ok_or("controller identity field absent")?;
        value.insert(name.into(), json!(field));
    }
    Ok(Value::Object(value))
}

fn reserve_ordinal(identity: &Value, audit: &[Value], op: u64) -> Result<u64> {
    let parent = audit.iter().find(|r| r["authority"] == "parent" && r["action"] == "settle-held-allowance" && r["stage"] == "requested")
        .ok_or("audited parent settlement request absent")?;
    let attempt = parent["reserveAttempt"].as_str().ok_or("audited parent reserve attempt absent")?;
    let directory = Path::new(identity["stateDir"].as_str().ok_or("state directory absent")?);
    let p = Path::new(attempt);
    let name = p.file_name().and_then(|v| v.to_str()).ok_or("parent reserve leaf invalid")?;
    let n = name.strip_prefix("attempt-").and_then(|v| v.parse::<u64>().ok())
        .ok_or("parent reserve operation invalid")?;
    if p.parent() != Some(directory) || n == 0 || n >= op || name != format!("attempt-{n:016}") {
        return Err("parent audit does not name a preceding exact local reserve".into());
    }
    let expected_unit = format!("mini-grain-t{}-o{op}", identity["task"].as_str().ok_or("task absent")?);
    if let Some(worker) = audit.iter().find(|r| r["action"] == "recover-gated-worker" || r["action"] == "clear-stranded-child-after-physical-audit") {
        if worker["unit"].as_str().or_else(|| worker["recordedUnit"].as_str()) != Some(&expected_unit) {
            return Err("worker audit does not bind this controller task and prompt".into());
        }
    }
    Ok(n)
}

fn validate_reserve(identity: &Value, audit: &[Value], record: &Record, source: &str, outcome: &str) -> Result<u64> {
    let ordinal = reserve_ordinal(identity, audit, record.prompt_operation_id)?;
    let source: Value = serde_json::from_str(source).map_err(|e| format!("retained reserve source: {e}"))?;
    let outcome: Value = serde_json::from_str(outcome).map_err(|e| format!("retained reserve outcome: {e}"))?;
    let grain = &source["grain"];
    if grain["task"] != identity["task"] || grain["subject"] != identity["subject"]
        || grain["capability"] != identity["capability"] || grain["observeCapability"] != identity["queryCapability"]
        || grain["operation"]["type"] != "reserve" || grain["context"]["payload"] != "hermes-acp prompt"
        || outcome["type"] != "confirmed" || outcome["confirmation"] != "installed" {
        return Err("parent audit source is not this prompt's confirmed Hermes reserve".into());
    }
    Ok(ordinal)
}

pub(crate) fn read(state_dir: &Path, prompt: u64) -> Result<Option<Record>> {
    let Some(original) = read_original(state_dir, prompt)? else { return Ok(None) };
    let target = resolution_path(state_dir, prompt);
    match fs::symlink_metadata(&target) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Some(original)),
        Err(e) => return Err(e.to_string()),
        Ok(meta) if !meta.is_file() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 =>
            return Err("prompt resolution must be an owned private regular file".into()),
        Ok(_) => {},
    }
    let resolution: AuditedResolution = serde_json::from_slice(&bounded_regular_file(&target, 131_072)?)
        .map_err(|e| format!("prompt audited resolution: {e}"))?;
    let journal: Journal = serde_json::from_slice(&bounded_regular_file(&state_dir.join("journal.json"), 32 * 1024 * 1024)?)
        .map_err(|e| format!("prompt resolution journal: {e}"))?;
    let mut expected = original.clone();
    expected.outcome = Outcome::Refused { stage: RefusalStage::Controller,
        reason: "native recovery and operator audit closed the worker, parent settlement and external-effects obligations; prompt closed without a deliverable result; no claim of absent effects".into() };
    if resolution.kind != "mini-prompt-audited-resolution-v1"
        || resolution.original_sha256 != sha256_file(&path(state_dir, prompt))?
        || resolution.controller_identity != controller_identity(&journal.binding)?
        || resolution.record != expected || resolution.audit != audit_chain(&resolution.audit, &original)?
        || resolution.reserve_source_sha256 != sha256_bytes(resolution.reserve_source.as_bytes())?
        || resolution.reserve_outcome_sha256 != sha256_bytes(resolution.reserve_outcome.as_bytes())? {
        return Err("prompt resolution differs from original outcome, controller binding or native audit chain".into());
    }
    validate_reserve(&resolution.controller_identity, &resolution.audit, &original,
        &resolution.reserve_source, &resolution.reserve_outcome)?;
    Ok(Some(resolution.record))
}

fn prompt_quiescent(journal: &Journal) -> bool {
    quiescence::retained(journal, quiescence::ResidentEvidence::NotConfigured)
        .iter()
        .all(|field| matches!(*field, "connection_fenced" | "hermes_pending_prompt"))
        && journal.provider_retry_gate.is_none()
}

impl Runtime {
    fn clear_audited_pending_prompt(&mut self) -> Result<()> {
        if let Some(session) = self.journal.hermes_session.as_mut() {
            if session.pending_prompt {
                if let Ok(Some(fp)) = hermes_state_fingerprint(&session.workspace.join(".hermes")) {
                    session.state_fingerprint = Some(fp);
                    session.retention_issue = None;
                }
                session.pending_prompt = false;
                self.save()?;
            }
        }
        Ok(())
    }

    pub(crate) fn reconcile_prompt_audited(&mut self, id: &str) -> Result<Value> {
        let op = id.parse::<u64>().map_err(|_| "prompt operation must be canonical positive u64")?;
        if op == 0 || op.to_string() != id { return Err("prompt operation must be canonical positive u64".into()); }
        let original = read_original(&self.config.state_dir, op)?.ok_or("prompt outcome absent")?;
        if self.child.is_some() || self.prompt_active || self.foreground_operation.is_some()
            || self.prompt_decision.is_some() || !prompt_quiescent(&self.journal) {
            return Err("prompt audit requires every invocation and retained custody to be reconciled".into());
        }
        let origin = self.journal.resident_prompt_origin.as_ref().ok_or("current resident prompt origin absent")?;
        if origin.prompt_operation_id != op || original.resident_prompt_id.as_deref() != Some(&origin.resident_prompt_id)
            || original.prompt_sha256.as_deref() != Some(&origin.prompt_sha256)
            || original.session_id != origin.session_id {
            return Err("prompt audit differs from exact current resident origin".into());
        }
        let target = resolution_path(&self.config.state_dir, op);
        if target.try_exists().map_err(|e| e.to_string())? {
            let resolved = read(&self.config.state_dir, op)?.ok_or("resolved prompt absent")?;
            self.clear_audited_pending_prompt()?;
            return resolution_result(&self.config.state_dir, &target, &resolved);
        }
        let audit = audit_chain(&self.journal.reconciliation_log, &original)?;
        let identity = controller_identity(&self.journal.binding)?;
        let ordinal = reserve_ordinal(&identity, &audit, op)?;
        let source_path = self.config.state_dir.join(format!("source-{ordinal:016}.json"));
        let outcome_path = self.config.state_dir.join(format!("attempt-{ordinal:016}/outcome.json"));
        let source = String::from_utf8(bounded_regular_file(&source_path, 65_536)?).map_err(|e|e.to_string())?;
        let outcome = String::from_utf8(bounded_regular_file(&outcome_path, 65_536)?).map_err(|e|e.to_string())?;
        validate_reserve(&identity, &audit, &original, &source, &outcome)?;
        if op - ordinal > 4096 { return Err("parent reserve is outside bounded prompt preparation".into()); }
        // Native prompt allocation immediately follows its parent lease. A
        // different parent reserve in between makes this old source unrelated.
        for id in ordinal + 1 .. op {
            let p = self.config.state_dir.join(format!("source-{id:016}.json"));
            if p.try_exists().map_err(|e|e.to_string())? {
                let v: Value = serde_json::from_slice(&bounded_regular_file(&p, 65_536)?).map_err(|e|e.to_string())?;
                if v["grain"]["task"] == identity["task"] && v["grain"]["operation"]["type"] == "reserve" {
                    return Err("another parent reserve intervenes before this prompt".into());
                }
            }
        }
        let mut record = original.clone();
        record.outcome = Outcome::Refused { stage: RefusalStage::Controller,
            reason: "native recovery and operator audit closed the worker, parent settlement and external-effects obligations; prompt closed without a deliverable result; no claim of absent effects".into() };
        let resolution = AuditedResolution { kind: "mini-prompt-audited-resolution-v1".into(),
            original_sha256: sha256_file(&path(&self.config.state_dir, op))?,
            controller_identity: identity, audit,
            reserve_source_sha256: sha256_bytes(source.as_bytes())?, reserve_source: source,
            reserve_outcome_sha256: sha256_bytes(outcome.as_bytes())?, reserve_outcome: outcome, record };
        let bytes = serde_json::to_vec_pretty(&resolution).map_err(|e| e.to_string())?;
        let target = resolution_path(&self.config.state_dir, op);
        match fs::symlink_metadata(&target) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => write_new(&target, &bytes)?,
            Err(e) => return Err(e.to_string()),
            Ok(_) if bounded_regular_file(&target, 131_072)? == bytes => {},
            Ok(_) => return Err("prompt already has a different audited resolution".into()),
        }
        let resolved = read(&self.config.state_dir, op)?.ok_or("resolved prompt absent")?;
        self.clear_audited_pending_prompt()?;
        resolution_result(&self.config.state_dir, &target, &resolved)
    }
}

fn resolution_result(state: &Path, target: &Path, resolved: &Record) -> Result<Value> {
    Ok(json!({"type":"mini-prompt-audited-resolution-result-v1", "promptOperationId":resolved.prompt_operation_id.to_string(),
        "residentPromptId":resolved.resident_prompt_id,"promptSha256":resolved.prompt_sha256,
        "state":"refused","resultReady":false,"originalSha256":sha256_file(&path(state, resolved.prompt_operation_id))?,
        "resolutionSha256":sha256_file(target)?,"resolutionPath":target}))
}

/// Administrative success reports the completed audit, not a successful
/// model turn. Keep this typed boundary separate from the refusal outcome.
pub(crate) fn successful_admin_reply(id: &str, response: &str) -> bool {
    #[derive(Deserialize)]
    #[serde(rename_all="camelCase", deny_unknown_fields)]
    struct Reply {
        #[serde(rename="type")] kind: String,
        prompt_operation_id: String,
        resident_prompt_id: String,
        prompt_sha256: String,
        state: String,
        result_ready: bool,
        original_sha256: String,
        resolution_sha256: String,
        resolution_path: PathBuf,
    }
    let Ok(op)=id.parse::<u64>() else { return false };
    if op == 0 || op.to_string() != id || response.len() > 65_536 { return false; }
    let Ok(reply)=serde_json::from_str::<Reply>(response) else { return false };
    reply.kind == "mini-prompt-audited-resolution-result-v1" && reply.prompt_operation_id == id
        && reply.state == "refused" && !reply.result_ready
        && [&reply.resident_prompt_id,&reply.prompt_sha256,&reply.original_sha256,&reply.resolution_sha256]
            .into_iter().all(|v| resident_origin::valid_digest(v))
        && reply.resolution_path.is_absolute()
        && reply.resolution_path.file_name().and_then(|v|v.to_str()) == Some(format!("prompt-resolution-{op:016}.json").as_str())
}

/// A consumer receipt must name both the original decision and the optional
/// validated resolution. The immutable original still says Undecided.
pub(crate) fn evidence(state: &Path, prompt: u64) -> Result<Value> {
    let record = read(state, prompt)?.ok_or("prompt evidence absent")?;
    let original = path(state, prompt);
    let resolution = resolution_path(state, prompt);
    let resolved = if resolution.try_exists().map_err(|e|e.to_string())? {
        Some(json!({"path":resolution,"sha256":sha256_file(&resolution)?}))
    } else { None };
    Ok(json!({"basis":"typed-prompt-outcome", "promptOutcome":original,
        "sha256":sha256_file(&original)?,"resolution":resolved,"outcome":record.outcome}))
}

/// Read the record bound to an exact resident origin. Absent is an error for
/// callers that need a decision: absence is never a refusal.
pub(crate) fn read_bound(state_dir: &Path, prompt: u64, resident_prompt_id: &str, prompt_sha256: &str) -> Result<Record> {
    let record = read(state_dir, prompt)?
        .ok_or_else(|| format!("prompt {prompt} has no outcome record; it is undecided until the controller writes one"))?;
    if record.resident_prompt_id.as_deref() != Some(resident_prompt_id)
        || record.prompt_sha256.as_deref() != Some(prompt_sha256) {
        return Err("prompt outcome record binds another resident prompt".into());
    }
    Ok(record)
}

/// The exact retry for retained custody, in the order an operator runs it.
/// `None` means the journal retains nothing for this prompt.
pub(crate) fn retry_for(journal: &Journal) -> Option<Retry> {
    let mut admin = Vec::new();
    let mut operation = None;
    if let Some(pending) = &journal.pending {
        operation = Some(pending.operation_id);
        admin.push("recover".to_owned());
    }
    if journal.child.is_some() {
        admin.push("reconcile worker audited".to_owned());
    }
    if journal.provider_pending.is_some() || journal.provider_hold.is_some() || journal.provider_attempt.is_some() {
        admin.push("reconcile provider audited".to_owned());
    }
    if journal.parent_hold.is_some() || journal.settlement_due.is_some() {
        admin.push("reconcile parent audited".to_owned());
    }
    if journal.tool_hold.is_some() || journal.tool_pending.is_some() {
        admin.push("reconcile tool audited".to_owned());
    }
    if journal.workspace_attempt.is_some() || journal.room_attempt.is_some() {
        if !admin.iter().any(|c| c == "recover") { admin.insert(0, "recover".to_owned()); }
    }
    if !journal.unresolved_external.is_empty() {
        admin.push("reconcile effects".to_owned());
    }
    (!admin.is_empty()).then_some(Retry { admin, operation })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    fn record(outcome: Outcome) -> Record {
        Record { kind: KIND.into(), prompt_operation_id: 42, resident_prompt_id: Some("a".repeat(64)),
            prompt_sha256: Some("b".repeat(64)), session_id: Some("s".into()), outcome }
    }

    #[test]
    fn undecided_record_names_its_retry_and_is_never_refused() {
        let dir = std::env::temp_dir().join(format!("prompt-outcome-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
        let undecided = record(Outcome::Undecided {
            retry: Retry { admin: vec!["reconcile parent audited".into(), "reconcile effects".into()], operation: None },
            detail: "ACP stream closed".into() });
        write(&dir, &undecided).unwrap();
        let back = read_bound(&dir, 42, &"a".repeat(64), &"b".repeat(64)).unwrap();
        assert_eq!(back, undecided);
        assert!(matches!(back.outcome, Outcome::Undecided { .. }));
        let text = fs::read_to_string(path(&dir, 42)).unwrap();
        assert!(text.contains("\"state\": \"undecided\"") && text.contains("reconcile parent audited"));
        // The first decision stands: a later refused record for the same prompt is refused.
        let refused = record(Outcome::Refused { stage: RefusalStage::TurnFailure, reason: "format_error".into() });
        assert!(write(&dir, &refused).is_err());
        write(&dir, &undecided).unwrap();
        // Undecided without a retry, or with a resubmitting verb, does not validate.
        let mut empty = undecided.clone();
        empty.outcome = Outcome::Undecided { retry: Retry { admin: vec![], operation: None }, detail: String::new() };
        assert!(empty.validate().is_err());
        empty.outcome = Outcome::Undecided { retry: Retry { admin: vec!["hermes again".into()], operation: None }, detail: String::new() };
        assert!(empty.validate().is_err());
        // Absence is not a decision.
        assert!(read_bound(&dir, 43, &"a".repeat(64), &"b".repeat(64)).is_err());
        // Another resident prompt's record does not bind.
        assert!(read_bound(&dir, 42, &"c".repeat(64), &"b".repeat(64)).is_err());
        fs::remove_dir_all(dir).unwrap();
    }

    pub(crate) fn audited_fixture() -> (Runtime, PathBuf, Record) {
        let (mut rt, root) = publication_refusal_tests::fixture(false, false, false);
        rt.journal.connection = Connection::Detached;
        rt.journal.child = None;
        rt.journal.prompt_witness = None;
        rt.journal.hermes_session = None;
        rt.prompt_active = false;
        rt.journal.next_operation_id = 89;
        let original = Record { prompt_operation_id: 67, session_id: None,
            outcome: Outcome::Undecided { retry: Retry { admin: vec!["reconcile worker audited".into(),
                "reconcile parent audited".into()], operation: None }, detail: "custody retained at the prompt boundary".into() },
            ..record(Outcome::Refused { stage: RefusalStage::Controller, reason: "unused".into() }) };
        rt.journal.resident_prompt_origin = Some(resident_origin::ResidentPromptOrigin {
            prompt_operation_id: 67, resident_prompt_id: original.resident_prompt_id.clone().unwrap(),
            prompt_sha256: original.prompt_sha256.clone().unwrap(), session_id: None });
        rt.journal.reconciliation_log = vec![
            json!({"decisionId":"68","action":"recover-gated-worker","operationId":"67",
                "machineProven":true,"stage":"physical-stop-verified","unit":"mini-grain-t7101-o67"}),
            json!({"decisionId":"79","authority":"parent","action":"settle-held-allowance",
                "stage":"requested","reserveAttempt":rt.config.state_dir.join("attempt-0000000000000065"),
                "originProof":"own-managed-law","originAudited":false,"charge":"1"}),
            json!({"decisionId":"79","authority":"parent","stage":"signed-settlement-confirmed","charge":"1"}),
            json!({"decisionId":"88","action":"derive-no-unaccounted-external-effects","stage":"acknowledged",
                "automatic":true,"externalEffectsAcknowledged":true,
                "basis":"derived: scoped --network none worker whose only external channel is the Mini broker; every Mini attempt resolved; no provider or dispatch attempt outstanding",
                "details":["worker operation 67 stopped after controller restart; external effects need acknowledgement"]})];
        write(&rt.config.state_dir, &original).unwrap();
        let source = json!({"grain":{"task":rt.config.task,"subject":rt.config.subject,
            "capability":rt.config.capability,"observeCapability":rt.config.query_capability,
            "operation":{"type":"reserve","amount":"3"},"context":{"payload":"hermes-acp prompt"}}});
        write_new(&rt.config.state_dir.join("source-0000000000000065.json"), &serde_json::to_vec(&source).unwrap()).unwrap();
        let attempt = rt.config.state_dir.join("attempt-0000000000000065");fs::create_dir(&attempt).unwrap();
        write_new(&attempt.join("outcome.json"), b"{\"type\":\"confirmed\",\"confirmation\":\"installed\"}").unwrap();
        rt.save().unwrap();
        (rt, root, original)
    }

    #[test]
    fn audited_resolution_preserves_original_and_is_exactly_replayable() {
        let (mut rt, root, original) = audited_fixture();
        let before = fs::read(path(&rt.config.state_dir, 67)).unwrap();
        let journal_before = fs::read(rt.config.state_dir.join("journal.json")).unwrap();
        let result = rt.reconcile_prompt_audited("67").unwrap();
        assert_eq!(result["state"], "refused"); assert_eq!(result["resultReady"], false);
        assert_eq!(rt.reconcile_prompt_audited("67").unwrap(), result);
        assert_eq!(fs::read(path(&rt.config.state_dir, 67)).unwrap(), before);
        assert_eq!(fs::read(rt.config.state_dir.join("journal.json")).unwrap(), journal_before);
        assert_eq!(read_original(&rt.config.state_dir, 67).unwrap().unwrap(), original);
        let resolved = read_bound(&rt.config.state_dir, 67, &"a".repeat(64), &"b".repeat(64)).unwrap();
        assert!(matches!(resolved.outcome, Outcome::Refused { stage: RefusalStage::Controller, .. }));
        assert!(read_bound(&rt.config.state_dir, 67, &"c".repeat(64), &"b".repeat(64)).is_err());
        rt.journal.reconciliation_log.clear(); rt.journal.binding["config"]["startupTimeoutSeconds"] = json!(1200); rt.save().unwrap();
        assert!(read(&rt.config.state_dir, 67).is_ok());
        rt.journal.binding["config"]["task"] = json!("foreign"); rt.save().unwrap();
        assert!(read(&rt.config.state_dir, 67).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn audited_resolution_requires_exact_origin_quiescence_and_complete_ordered_audits() {
        let (mut rt, root, _) = audited_fixture();
        for id in ["0", "067", "-1", "68", "18446744073709551616"] {
            assert!(rt.reconcile_prompt_audited(id).is_err());
        }
        rt.prompt_active = true; assert!(rt.reconcile_prompt_audited("67").is_err()); rt.prompt_active = false;
        rt.journal.unresolved_external.push("still uncertain".into());
        assert!(rt.reconcile_prompt_audited("67").is_err()); rt.journal.unresolved_external.clear();
        rt.journal.resident_prompt_origin.as_mut().unwrap().prompt_sha256 = "c".repeat(64);
        assert!(rt.reconcile_prompt_audited("67").is_err());
        rt.journal.resident_prompt_origin.as_mut().unwrap().prompt_sha256 = "b".repeat(64);
        let all = rt.journal.reconciliation_log.clone();
        for index in 0..all.len() {
            rt.journal.reconciliation_log = all.clone(); rt.journal.reconciliation_log.remove(index);
            assert!(rt.reconcile_prompt_audited("67").is_err(), "missing audit {index}");
        }
        rt.journal.reconciliation_log = all.clone(); rt.journal.reconciliation_log[0]["operationId"] = json!("66");
        assert!(rt.reconcile_prompt_audited("67").is_err());
        rt.journal.reconciliation_log = all.clone(); rt.journal.reconciliation_log[3]["decisionId"] = json!("78");
        assert!(rt.reconcile_prompt_audited("67").is_err());
        rt.journal.reconciliation_log = all.clone(); rt.journal.reconciliation_log[3]["basis"] = json!("caller says done");
        assert!(rt.reconcile_prompt_audited("67").is_err());
        rt.journal.reconciliation_log = all.clone(); rt.journal.reconciliation_log[0]["unit"] = json!("mini-grain-tforeign-o67");
        assert!(rt.reconcile_prompt_audited("67").is_err());
        rt.journal.reconciliation_log = all.clone();
        rt.journal.reconciliation_log[1]["reserveAttempt"] = json!(rt.config.state_dir.join("attempt-0000000000000070"));
        assert!(rt.reconcile_prompt_audited("67").is_err());
        rt.journal.reconciliation_log = all;
        let intervening = rt.config.state_dir.join("source-0000000000000066.json");
        write_new(&intervening, &serde_json::to_vec(&json!({"grain":{"task":rt.config.task,"operation":{"type":"reserve"}}})).unwrap()).unwrap();
        assert!(rt.reconcile_prompt_audited("67").is_err());
        assert!(!resolution_path(&rt.config.state_dir, 67).exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn audited_resolution_rejects_changed_original_or_resolution() {
        let (mut rt, root, _) = audited_fixture();
        rt.reconcile_prompt_audited("67").unwrap();
        let p = resolution_path(&rt.config.state_dir, 67); let bytes = fs::read(&p).unwrap();
        let mut value: Value = serde_json::from_slice(&bytes).unwrap();
        value["record"]["outcome"] = json!({"state":"admitted","stopReason":"end_turn","settledCharge":"0",
            "providerResponseSha256":null,"providerMeteredCharge":null});
        fs::write(&p, serde_json::to_vec(&value).unwrap()).unwrap();
        assert!(read(&rt.config.state_dir, 67).is_err());
        fs::write(&p, bytes).unwrap();
        let original = path(&rt.config.state_dir, 67);
        let mut bytes = fs::read(&original).unwrap(); bytes.push(b' '); fs::write(original, bytes).unwrap();
        assert!(read(&rt.config.state_dir, 67).is_err());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    #[ignore = "requires an explicitly retained native capture; never opens its Store"]
    fn audited_resolution_retained_native_capture() {
        let p = std::env::var_os("MINI_PROMPT_AUDIT_CAPTURE").expect("retained capture path required");
        let capture: Value = serde_json::from_slice(&fs::read(p).unwrap()).unwrap();
        let journal: Journal = serde_json::from_value(capture["journal"].clone()).unwrap();
        let original: Record = serde_json::from_value(capture["outcome"].clone()).unwrap();
        assert!(prompt_quiescent(&journal));
        let origin=journal.resident_prompt_origin.as_ref().unwrap();
        assert_eq!(origin.prompt_operation_id, original.prompt_operation_id);
        assert_eq!(Some(&origin.resident_prompt_id), original.resident_prompt_id.as_ref());
        assert_eq!(Some(&origin.prompt_sha256), original.prompt_sha256.as_ref());
        let audit=audit_chain(&journal.reconciliation_log,&original).unwrap();
        let identity=controller_identity(&journal.binding).unwrap();
        let reserve=validate_reserve(&identity,&audit,&original,capture["source"].as_str().unwrap(),
            capture["reserveOutcome"].as_str().unwrap()).unwrap();
        assert_eq!(reserve, capture["reserveOperationId"].as_u64().unwrap());
    }

    fn admin_reply() -> Value {
        json!({"type":"mini-prompt-audited-resolution-result-v1","promptOperationId":"67",
            "residentPromptId":"a".repeat(64),"promptSha256":"b".repeat(64),"state":"refused",
            "resultReady":false,"originalSha256":"c".repeat(64),"resolutionSha256":"d".repeat(64),
            "resolutionPath":"/private/state/prompt-resolution-0000000000000067.json"})
    }

    #[test]
    fn audited_admin_reply_classifies_command_success_without_claiming_turn_success() {
        let good=admin_reply(); assert!(successful_admin_reply("67",&good.to_string()));
        for id in ["0","067","68"] { assert!(!successful_admin_reply(id,&good.to_string())); }
        for (field,bad) in [("state",json!("admitted")),("resultReady",json!(true)),
            ("originalSha256",json!("")),("resolutionPath",json!("relative.json")),("noDispatch",json!(true))] {
            let mut reply=good.clone();reply[field]=bad;
            assert!(!successful_admin_reply("67",&reply.to_string()),"{field}");
        }
        let duplicate=good.to_string().replacen('{',"{\"resultReady\":false,",1);
        assert!(!successful_admin_reply("67",&duplicate));
        assert!(!successful_admin_reply("67","error: audit incomplete"));
    }

    #[test]
    #[ignore = "requires a separately built runtime executable for actual CLI reception"]
    fn audited_admin_actual_cli_preserves_stdout_and_exit_status() {
        use std::os::unix::net::UnixListener;
        let binary=std::env::var_os("MINI_GRAIN_RUNTIME_CLI").expect("qualified runtime path required");
        let root=std::env::temp_dir().join(format!("gpa-cli-{}",std::process::id()));
        fs::create_dir(&root).unwrap();
        let good=admin_reply().to_string();
        for (index,reply,success) in [(0,good.clone(),true),
            (1,good.replace("\"67\"","\"68\""),false),(2,"error: audit incomplete".into(),false)] {
            let socket=root.join(format!("{index}.sock"));let listener=UnixListener::bind(&socket).unwrap();
            let expected=reply.clone();
            let server=thread::spawn(move || {
                let (mut stream,_)=listener.accept().unwrap();
                assert_eq!(control::admin_read_frame(&mut stream).unwrap(),"reconcile prompt audited 67");
                control::admin_write_frame(&mut stream,&reply).unwrap();
            });
            let output=Command::new(&binary).args(["admin",socket.to_str().unwrap(),"reconcile prompt audited 67"])
                .output().unwrap();server.join().unwrap();
            assert_eq!(output.status.success(),success,"{}",String::from_utf8_lossy(&output.stderr));
            if success { assert_eq!(String::from_utf8(output.stdout).unwrap(),format!("{expected}\n"));assert!(output.stderr.is_empty()); }
            else { assert!(output.stdout.is_empty());assert!(String::from_utf8_lossy(&output.stderr).contains(&expected)); }
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn admitted_requires_end_turn_and_a_decimal_charge() {
        let ok = record(Outcome::Admitted { stop_reason: "end_turn".into(), settled_charge: "1".into(),
            provider_response_sha256: None, provider_metered_charge: None });
        ok.validate().unwrap();
        let mut bad = ok.clone();
        bad.outcome = Outcome::Admitted { stop_reason: "cancelled".into(), settled_charge: "1".into(),
            provider_response_sha256: None, provider_metered_charge: None };
        assert!(bad.validate().is_err());
        bad.outcome = Outcome::Admitted { stop_reason: "end_turn".into(), settled_charge: "01".into(),
            provider_response_sha256: None, provider_metered_charge: None };
        assert!(bad.validate().is_err());
        record(Outcome::Refused { stage: RefusalStage::TurnFailure, reason: "format_error".into() }).validate().unwrap();
        assert!(record(Outcome::Refused { stage: RefusalStage::Setup, reason: String::new() }).validate().is_err());
    }
}
