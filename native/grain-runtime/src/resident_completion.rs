//! Receive one source-completed model turn across controller/driver crashes.
//! Turn accounting and delivery are separate transactions. This receiver never
//! invokes a model, submits a room write, or accepts an arbitrary counter edit.
//!
//! Deliberate remaining boundary: a same-origin failed/review-needed frame
//! emitted after end_turn (for example final-stage filesystem failure) is a
//! competing outcome and is refused, not silently reclassified. Generic
//! Runtime::save journal.tmp recovery is outside this typed receiver; partial
//! or foreign staging bytes remain explicit refusals.
use crate::quiescence::{ResidentGuard, Status};
use crate::*;

const LIMIT: usize = 1_048_576;

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct CompletedTurn {
    kind: String,
    origin: Value,
    binding_sha256: String,
    config_sha256: String,
    acp_result: Value,
    acp_result_sha256: String,
    provider_replays_sha256: String,
    session_before: HermesSession,
    session_after: HermesSession,
    registered_shared_application_count: usize,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Pending {
    pub(crate) turn: CompletedTurn,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Receiving {
    kind: String,
    turn_sha256: String,
    resident_state: PathBuf,
    resident_before: String,
    resident_after: String,
    before_sha256: String,
    after_sha256: String,
    completion_frame: Value,
    completed_ordinal: u64,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct EvidenceRef {
    path: PathBuf,
    sha256: String,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct QuiescenceEvidence {
    kind: String,
    turn_sha256: String,
    receiving_sha256: String,
    resident_sha256: String,
    /// Exact source Status, including every native observation and error field.
    status: Value,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    #[serde(rename = "type")]
    kind: String,
    resident_state: PathBuf,
    resident_sha256: String,
    turn_sha256: String,
}

fn hash(value: &impl Serialize) -> Result<String> {
    sha256_bytes(&serde_json::to_vec(value).map_err(|e| e.to_string())?)
}

fn retain(path: &Path, value: &impl Serialize) -> Result<()> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    retain_exact_private(path, &bytes, LIMIT)?;
    File::open(path.parent().ok_or("completion artifact parent absent")?)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())
}

fn read<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    serde_json::from_slice(&bounded_regular_file(path, LIMIT)?).map_err(|e| e.to_string())
}

impl CompletedTurn {
    fn operation(&self) -> Result<u64> {
        self.origin["promptOperationId"]
            .as_u64()
            .filter(|id| *id > 0)
            .ok_or_else(|| "completion source operation absent".into())
    }
    fn path(&self, state: &Path, suffix: &str) -> Result<PathBuf> {
        Ok(state.join(format!(
            "resident-completion-{:016}.{suffix}.json",
            self.operation()?
        )))
    }
    fn validate(&self) -> Result<()> {
        self.operation()?;
        let mut expected = self.session_before.clone();
        expected.pending_prompt = false;
        expected.state_fingerprint = self.session_after.state_fingerprint.clone();
        expected.retention_issue = None;
        if self.kind != "mini-resident-completed-turn-v1"
            || !resident_origin::valid_digest(
                self.origin["residentPromptId"].as_str().unwrap_or(""),
            )
            || !resident_origin::valid_digest(self.origin["promptSha256"].as_str().unwrap_or(""))
            || self.origin["sessionId"] != self.session_before.id
            || !self.session_before.pending_prompt
            || self
                .session_before
                .retention_issue
                .as_deref()
                .is_some_and(|s| s != "first prompt has not yet been retained")
            || hash(&expected)? != hash(&self.session_after)?
            || self
                .session_after
                .state_fingerprint
                .as_deref()
                .is_none_or(str::is_empty)
            || self.acp_result["stopReason"] != "end_turn"
            || self.acp_result["miniSourceFinalText"].as_str().is_none()
            || hash(&self.acp_result)? != self.acp_result_sha256
            || !resident_origin::valid_digest(&self.binding_sha256)
            || !resident_origin::valid_digest(&self.config_sha256)
            || !resident_origin::valid_digest(&self.provider_replays_sha256)
        {
            return Err("source completed-turn record refused".into());
        }
        Ok(())
    }
    fn session_matches(&self, current: &HermesSession) -> Result<bool> {
        let value = hash(current)?;
        Ok(value == hash(&self.session_before)? || value == hash(&self.session_after)?)
    }
    fn fingerprint_matches(&self) -> Result<()> {
        let home = self.session_after.workspace.join(".hermes");
        let meta = fs::symlink_metadata(&home).map_err(|e| e.to_string())?;
        if !meta.is_dir()
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.mode() & 0o077 != 0
            || hermes_state_fingerprint(&home)? != self.session_after.state_fingerprint
        {
            return Err("source-completed session bytes or custody changed after reap".into());
        }
        Ok(())
    }
}

pub(crate) fn validate_pending(journal: &Journal) -> Result<()> {
    let Some(pending) = &journal.resident_completion else {
        return Ok(());
    };
    pending.turn.validate()?;
    if pending.turn.origin
        != serde_json::to_value(&journal.resident_prompt_origin).map_err(|e| e.to_string())?
        || pending.turn.binding_sha256 != hash(&journal.binding)?
        || pending.turn.provider_replays_sha256 != hash(&journal.provider_replays)?
        || !pending.turn.session_matches(
            journal
                .hermes_session
                .as_ref()
                .ok_or("completed session absent")?,
        )?
    {
        return Err("completion pending record differs from current source journal".into());
    }
    Ok(())
}

fn transition(turn: &CompletedTurn, state: &Path, bytes: &[u8]) -> Result<Receiving> {
    turn.validate()?;
    resident_reconcile::decode_resident_state(bytes)?;
    let before: Value = serde_json::from_slice(bytes).map_err(|e| e.to_string())?;
    let pending = &before["pending"];
    if pending["residentPromptId"] != turn.origin["residentPromptId"]
        || pending["promptSha256"] != turn.origin["promptSha256"]
        || !resident_origin::valid_digest(pending["inputSha256"].as_str().unwrap_or(""))
        || pending["attachmentId"].as_u64().is_none_or(|n| n == 0)
        || pending["requestId"].as_u64().is_none_or(|n| n == 0)
        || before["returnPending"] == true
    {
        return Err("source completion does not bind the resident's exact pending turn".into());
    }
    let frame = json!({"v":1,"type":"prompt-complete","attachmentId":pending["attachmentId"],
        "requestId":pending["requestId"],"outcome":"completed","activity":"ready",
        "retainedSession":true,"reviewNeeded":false,
        "registeredSharedApplicationCount":turn.registered_shared_application_count,
        "residentOrigin":turn.origin,"residentPendingSha256":hash(pending)?});
    // A received frame must agree exactly with the source receipt. Missing
    // transport delivery is the only absent-frame case, not a failed outcome.
    if !before["lastCompletion"].is_null() && before["lastCompletion"] != frame {
        return Err(
            "resident has a competing completion; source receipt does not overwrite it".into(),
        );
    }
    let ordinal = before["completed"]
        .as_u64()
        .ok_or("resident completed counter invalid")?
        .checked_add(1)
        .ok_or("resident completed counter exhausted")?;
    let mut after = before.clone();
    after["completed"] = json!(ordinal);
    after["lastInput"] = pending["inputSha256"].clone();
    after["pending"] = Value::Null;
    after["lastCompletion"] = frame.clone();
    let after_bytes = serde_json::to_vec_pretty(&after).map_err(|e| e.to_string())?;
    Ok(Receiving {
        kind: "mini-resident-completion-receiving-v1".into(),
        turn_sha256: hash(turn)?,
        resident_state: state.into(),
        resident_before: std::str::from_utf8(bytes)
            .map_err(|e| e.to_string())?
            .into(),
        resident_after: String::from_utf8(after_bytes.clone()).map_err(|e| e.to_string())?,
        before_sha256: sha256_bytes(bytes)?,
        after_sha256: sha256_bytes(&after_bytes)?,
        completion_frame: frame,
        completed_ordinal: ordinal,
    })
}

impl Receiving {
    fn validate(&self, turn: &CompletedTurn, state: &Path) -> Result<()> {
        if self.kind != "mini-resident-completion-receiving-v1"
            || self.turn_sha256 != hash(turn)?
            || self.resident_state != state
            || self.before_sha256 != sha256_bytes(self.resident_before.as_bytes())?
            || self.after_sha256 != sha256_bytes(self.resident_after.as_bytes())?
        {
            return Err("completion receiving archive binding changed".into());
        }
        let expected = transition(turn, state, self.resident_before.as_bytes())?;
        if hash(self)? != hash(&expected)? {
            return Err("completion archive is not the source-defined counter transition".into());
        }
        Ok(())
    }
    fn accepts(&self, bytes: &[u8]) -> bool {
        bytes == self.resident_before.as_bytes() || bytes == self.resident_after.as_bytes()
    }
}

fn closed_boundary(status: &Status) -> Result<()> {
    if !status.can_restart_retaining_state
        || !status.active.is_empty()
        || !status.evidence_required.is_empty()
        || !status.exact_recovery.is_empty()
        || status.observations.is_empty()
        || !status
            .observations
            .iter()
            .all(|o| quiescence::signed_unreserved_boundary(&o["state"]))
        || status.retained.iter().any(|name| {
            !matches!(
                *name,
                "resident_completion"
                    | "resident_delivery"
                    | "resident_pending_prompt"
                    | "hermes_pending_prompt"
                    | "hermes_retention_issue"
            )
        })
        || status
            .session_integrity_errors
            .iter()
            .any(|e| e != "retained session fingerprint is missing or changed")
    {
        return Err(
            "completion receiving requires a source-bound closed native/process/session boundary"
                .into(),
        );
    }
    // The one allowed stale prior-fingerprint report is checked independently
    // against the captured final fingerprint before any publication.
    Ok(())
}

fn evidence_path(state: &Path, turn: &CompletedTurn, digest: &str) -> Result<PathBuf> {
    if !resident_origin::valid_digest(digest) {
        return Err("completion quiescence evidence digest invalid".into());
    }
    turn.path(state, &format!("quiescence-{digest}"))
}

/// Content addressing preserves every distinct fresh attempt. The full Status
/// is archived before state publication; a failed/partial archive cannot become
/// the receipt's evidence. An already-received acknowledgment verifies its
/// original archive instead of relabeling an older snapshot as fresh.
fn archive_quiescence(
    state: &Path,
    turn: &CompletedTurn,
    receiving: &Receiving,
    resident: &[u8],
    status: &Status,
) -> Result<EvidenceRef> {
    closed_boundary(status)?;
    receiving.validate(turn, &receiving.resident_state)?;
    if !receiving.accepts(resident)
        || status.binding_sha256 != turn.binding_sha256
        || status.config_sha256.as_deref() != Some(turn.config_sha256.as_str())
        || status.resident_state.as_deref() != Some(receiving.resident_state.as_path())
        || !status.snapshot_only
    {
        return Err("completion quiescence snapshot does not bind this receiving attempt".into());
    }
    let evidence = QuiescenceEvidence {
        kind: "mini-resident-completion-quiescence-v1".into(),
        turn_sha256: hash(turn)?,
        receiving_sha256: hash(receiving)?,
        resident_sha256: sha256_bytes(resident)?,
        status: serde_json::to_value(status).map_err(|e| e.to_string())?,
    };
    let bytes = serde_json::to_vec_pretty(&evidence).map_err(|e| e.to_string())?;
    let sha256 = sha256_bytes(&bytes)?;
    let path = evidence_path(state, turn, &sha256)?;
    retain(&path, &evidence)?;
    Ok(EvidenceRef { path, sha256 })
}

fn validate_quiescence_archive(
    state: &Path,
    turn: &CompletedTurn,
    receiving: &Receiving,
    reference: &EvidenceRef,
) -> Result<()> {
    if reference.path != evidence_path(state, turn, &reference.sha256)? {
        return Err("completion quiescence evidence path leaves its source namespace".into());
    }
    let bytes = bounded_regular_file(&reference.path, LIMIT)?;
    if sha256_bytes(&bytes)? != reference.sha256 {
        return Err("completion quiescence evidence bytes changed".into());
    }
    let evidence: QuiescenceEvidence = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if evidence.kind != "mini-resident-completion-quiescence-v1"
        || evidence.turn_sha256 != hash(turn)?
        || evidence.receiving_sha256 != hash(receiving)?
        || ![&receiving.before_sha256, &receiving.after_sha256].contains(&&evidence.resident_sha256)
        || evidence.status["bindingSha256"] != turn.binding_sha256
        || evidence.status["configSha256"] != turn.config_sha256
        || evidence.status["residentState"] != json!(receiving.resident_state)
        || evidence.status["snapshotOnly"] != true
    {
        return Err("completion quiescence evidence identity differs from its receipt".into());
    }
    Ok(())
}

impl Runtime {
    /// Caller has validated genuine end_turn, drained provider and reaped the
    /// worker, settled the parent, but has NOT cleared session.pending_prompt.
    pub(crate) fn stage_resident_completion(&mut self, result: &Value) -> Result<()> {
        let origin = self
            .journal
            .resident_prompt_origin
            .as_ref()
            .ok_or("completed resident origin absent")?;
        if self.journal.resident_completion.is_some() {
            return Err("previous completion is not received".into());
        }
        let forbidden =
            quiescence::retained(&self.journal, quiescence::ResidentEvidence::NotConfigured)
                .into_iter()
                .filter(|m| !matches!(*m, "hermes_pending_prompt" | "hermes_retention_issue"))
                .collect::<Vec<_>>();
        if !forbidden.is_empty() || self.child.is_some() || self.prompt_active {
            return Err(format!(
                "completed-turn staging requires reaped settled source boundary: {forbidden:?}"
            ));
        }
        let before = self
            .journal
            .hermes_session
            .clone()
            .ok_or("completed source session absent")?;
        let mut after = before.clone();
        after.pending_prompt = false;
        after.state_fingerprint = hermes_state_fingerprint(&after.workspace.join(".hermes"))?;
        after.retention_issue = None;
        let turn = CompletedTurn {
            kind: "mini-resident-completed-turn-v1".into(),
            origin: serde_json::to_value(origin).map_err(|e| e.to_string())?,
            binding_sha256: hash(&self.journal.binding)?,
            config_sha256: hash(&self.config)?,
            acp_result: result.clone(),
            acp_result_sha256: hash(result)?,
            provider_replays_sha256: hash(&self.journal.provider_replays)?,
            session_before: before,
            session_after: after,
            registered_shared_application_count: self
                .config
                .tool_task
                .as_ref()
                .map_or(0, |t| t.registered_shared_applications.len()),
        };
        turn.validate()?;
        self.journal.resident_completion = Some(Pending { turn: turn.clone() });
        self.save()?; // Old pending_prompt remains until this typed marker is durable.
        retain(&turn.path(&self.config.state_dir, "source")?, &turn)
    }

    fn completion_turn(&self) -> Result<CompletedTurn> {
        validate_pending(&self.journal)?;
        if let Some(pending) = &self.journal.resident_completion {
            let turn = pending.turn.clone();
            if turn.config_sha256 != hash(&self.config)? {
                return Err("completion configuration changed".into());
            }
            return Ok(turn);
        }
        // Read-only idempotent acknowledgment after the marker was cleared.
        let origin = self
            .journal
            .resident_prompt_origin
            .as_ref()
            .ok_or("no source completion pending")?;
        let source = self.config.state_dir.join(format!(
            "resident-completion-{:016}.source.json",
            origin.prompt_operation_id
        ));
        let turn: CompletedTurn = read(&source)?;
        turn.validate()?;
        if turn.origin != serde_json::to_value(origin).map_err(|e| e.to_string())?
            || !turn
                .path(&self.config.state_dir, "received")?
                .try_exists()
                .map_err(|e| e.to_string())?
        {
            return Err("completion marker absent without its exact received receipt".into());
        }
        Ok(turn)
    }

    pub(crate) fn plan_resident_completion(&mut self, state: &Path) -> Result<Value> {
        let guard = ResidentGuard::acquire(&self.config, Some(state))?;
        let turn = self.completion_turn()?;
        let path = turn.path(&self.config.state_dir, "receiving")?;
        let receiving = if path.try_exists().map_err(|e| e.to_string())? {
            read::<Receiving>(&path)?
        } else {
            transition(&turn, state, guard.bytes()?)?
        };
        receiving.validate(&turn, state)?;
        if !receiving.accepts(guard.bytes()?) {
            return Err("resident completion is outside its exact old/new receiving states".into());
        }
        Ok(
            json!({"type":"mini-resident-completion-plan-v1","turnSha256":hash(&turn)?,
            "residentState":state,"residentSha256":sha256_bytes(guard.bytes()?)?,
            "beforeSha256":receiving.before_sha256,"afterSha256":receiving.after_sha256,
            "completedOrdinal":receiving.completed_ordinal,"completionFrame":receiving.completion_frame,"modelRequests":0}),
        )
    }

    pub(crate) fn receive_resident_completion(&mut self, path: &Path) -> Result<Value> {
        let request: Request = read(path)?;
        if request.kind != "mini-resident-completion-request-v1" {
            return Err("completion request type refused".into());
        }
        let guard = ResidentGuard::acquire(&self.config, Some(&request.resident_state))?;
        let turn = self.completion_turn()?;
        if request.turn_sha256 != hash(&turn)? {
            return Err("completion source changed after review".into());
        }
        let receiving_path = turn.path(&self.config.state_dir, "receiving")?;
        let receiving = if receiving_path.try_exists().map_err(|e| e.to_string())? {
            read::<Receiving>(&receiving_path)?
        } else {
            transition(&turn, &request.resident_state, guard.bytes()?)?
        };
        receiving.validate(&turn, &request.resident_state)?;
        if !receiving.accepts(guard.bytes()?)
            || ![&receiving.before_sha256, &receiving.after_sha256]
                .contains(&&request.resident_sha256)
        {
            return Err("completion receiving refuses a third resident state or request".into());
        }
        let received_path = turn.path(&self.config.state_dir, "received")?;
        if received_path.try_exists().map_err(|e| e.to_string())? {
            let old: Value = read(&received_path)?;
            let evidence: EvidenceRef = serde_json::from_value(old["quiescenceEvidence"].clone())
                .map_err(|e| format!("completion receipt evidence: {e}"))?;
            validate_quiescence_archive(&self.config.state_dir, &turn, &receiving, &evidence)?;
            let receipt = completion_receipt(&turn, &receiving, &evidence)?;
            if old != receipt || guard.bytes()? != receiving.resident_after.as_bytes() {
                return Err(
                    "completion received receipt differs from published exact state".into(),
                );
            }
            if self.journal.resident_completion.is_some() {
                self.journal.resident_completion = None;
                self.publish_completion_journal(turn.operation()?)?;
            }
            return Ok(receipt);
        }
        turn.fingerprint_matches()?;
        let status = self.inspect_quiescence_locked(&guard)?;
        closed_boundary(&status)?;
        turn.fingerprint_matches()?;
        guard.assert_unchanged()?;
        let evidence = archive_quiescence(
            &self.config.state_dir,
            &turn,
            &receiving,
            guard.bytes()?,
            &status,
        )?;
        let receipt = completion_receipt(&turn, &receiving, &evidence)?;
        retain(&turn.path(&self.config.state_dir, "source")?, &turn)?;
        retain(&receiving_path, &receiving)?;
        // The controller may have crashed between staging CompletedTurn and
        // staging the final delivery. Reconstruct only from its source ACP
        // result and retained settled response, never from display output.
        self.stage_resident_final(&turn.acp_result)?;
        // Both publications are typed old/new transitions. Source markers are
        // retained until the receipt is durable; every cut can re-enter here.
        self.publish_completed_session(&turn)?;
        publish_resident(&receiving)?;
        retain(&received_path, &receipt)?;
        self.journal.resident_completion = None;
        self.publish_completion_journal(turn.operation()?)?;
        Ok(receipt)
    }

    fn publish_completed_session(&mut self, turn: &CompletedTurn) -> Result<()> {
        if !turn.session_matches(
            self.journal
                .hermes_session
                .as_ref()
                .ok_or("completion session disappeared")?,
        )? {
            return Err("completion session is outside its old/new source vectors".into());
        }
        self.journal.hermes_session = Some(turn.session_after.clone());
        self.publish_completion_journal(turn.operation()?)
    }

    fn publish_completion_journal(&self, operation: u64) -> Result<()> {
        config_migration::ensure_process_current(&self.config.state_dir)?;
        session_failure::ensure_publication_known(&self.config.state_dir)?;
        let bytes = serde_json::to_vec_pretty(&self.journal).map_err(|e| e.to_string())?;
        config_migration::publish_bytes(
            &self.config.state_dir.join("journal.json"),
            &bytes,
            &format!("resident-completion-{operation}-{}", sha256_bytes(&bytes)?),
        )
    }
}

pub(crate) fn require_source_receipt(config: &Config, frame: &Value) -> Result<()> {
    let journal: Journal = read(&config.state_dir.join("journal.json"))?;
    validate_pending(&journal)?;
    let turn = &journal
        .resident_completion
        .as_ref()
        .ok_or("controller completed frame has no source completion receipt")?
        .turn;
    if frame["residentOrigin"] != turn.origin
        || frame["outcome"] != "completed"
        || frame["reviewNeeded"] != false
    {
        return Err("driver completion frame differs from source completed-turn receipt".into());
    }
    Ok(())
}

fn completion_receipt(
    turn: &CompletedTurn,
    receiving: &Receiving,
    evidence: &EvidenceRef,
) -> Result<Value> {
    Ok(
        json!({"type":"mini-resident-completion-received-v1","turnSha256":hash(turn)?,
        "origin":turn.origin,"residentState":receiving.resident_state,
        "beforeSha256":receiving.before_sha256,"afterSha256":receiving.after_sha256,
        "completedOrdinal":receiving.completed_ordinal,"completionFrame":receiving.completion_frame,
        "quiescenceEvidence":evidence,
        "modelRequests":0,"roomWrites":0}),
    )
}

fn publish_resident(receiving: &Receiving) -> Result<()> {
    let path = receiving.resident_state.join("resident.json");
    let current = bounded_regular_file(&path, LIMIT)?;
    if !receiving.accepts(&current) {
        return Err("completion resident changed before publication".into());
    }
    if current == receiving.resident_after.as_bytes() {
        return Ok(());
    }
    config_migration::publish_bytes(
        &path,
        receiving.resident_after.as_bytes(),
        &receiving.turn_sha256[..16],
    )
}

/// Called with the resident flock held before rejecting pending, before a new
/// prompt and before maxPrompts/unchanged-input exits. The source controller
/// marker fences prompt admission while the driver transfers this flock.
pub(crate) fn drain(config: &Config, state: &Path, lock: &File) -> Result<()> {
    let journal: Journal = read(&config.state_dir.join("journal.json"))?;
    if journal.resident_completion.is_none() {
        return Ok(());
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) } != 0 {
        return Err("completion lock transfer failed".into());
    }
    let result = (|| -> Result<()> {
        let socket = config.state_dir.join("admin.sock");
        let response = control::admin_call(
            &socket,
            &format!("resident completion-plan {}", state.display()),
        )?;
        let plan: Value = serde_json::from_str(&response).map_err(|_| response.clone())?;
        if plan["type"] != "mini-resident-completion-plan-v1" {
            return Err("completion plan response refused".into());
        }
        let request = json!({"type":"mini-resident-completion-request-v1","residentState":state,
            "residentSha256":plan["residentSha256"],"turnSha256":plan["turnSha256"]});
        let path = state.join(format!("completion-request-{}.json", hash(&request)?));
        retain(&path, &request)?;
        let response = control::admin_call(
            &socket,
            &format!("resident receive-completion {}", path.display()),
        )?;
        let value: Value = serde_json::from_str(&response).map_err(|_| response.clone())?;
        if value["type"] != "mini-resident-completion-received-v1" {
            return Err("completion receiving response refused".into());
        }
        Ok(())
    })();
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err("resident lock changed while completion was receiving".into());
    }
    config_migration::ensure_resident_current(config)?;
    result
}

pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let command =
        match args {
            [mode, _, state] if mode == "plan" => format!(
                "resident completion-plan {}",
                state
                    .to_str()
                    .ok_or("completion state path must be UTF-8")?
            ),
            [mode, _, request] if mode == "receive" => format!(
                "resident receive-completion {}",
                request
                    .to_str()
                    .ok_or("completion request path must be UTF-8")?
            ),
            _ => return Err(
                "usage: grain-runtime resident-completion plan ADMIN STATE | receive ADMIN REQUEST"
                    .into(),
            ),
        };
    let response = control::admin_call(Path::new(&args[1]), &command)?;
    let value: Value = serde_json::from_str(&response).map_err(|_| response.clone())?;
    if ![
        "mini-resident-completion-plan-v1",
        "mini-resident-completion-received-v1",
    ]
    .contains(&value["type"].as_str().unwrap_or(""))
    {
        return Err("completion response type refused".into());
    }
    println!("{value}");
    Ok(())
}

#[cfg(test)]
pub(crate) fn fixture_write_receipt(
    config: &Config,
    journal: &mut Journal,
    id: &str,
    digest: &str,
) -> Result<()> {
    let origin = resident_origin::ResidentPromptOrigin {
        resident_prompt_id: id.into(),
        prompt_sha256: digest.into(),
        prompt_operation_id: 94,
        session_id: Some("source-session".into()),
    };
    let before = HermesSession {
        id: "source-session".into(),
        workspace: config.cwd.clone(),
        load_verified: true,
        state_fingerprint: Some("fixture-old".into()),
        retention_issue: None,
        pending_prompt: true,
    };
    let mut after = before.clone();
    after.pending_prompt = false;
    after.state_fingerprint = Some("fixture-final".into());
    let acp = json!({"stopReason":"end_turn","miniSourceFinalText":"fixture final"});
    let turn = CompletedTurn {
        kind: "mini-resident-completed-turn-v1".into(),
        origin: serde_json::to_value(&origin).map_err(|e| e.to_string())?,
        binding_sha256: hash(&journal.binding)?,
        config_sha256: hash(config)?,
        acp_result_sha256: hash(&acp)?,
        acp_result: acp,
        provider_replays_sha256: hash(&journal.provider_replays)?,
        session_before: before.clone(),
        session_after: after,
        registered_shared_application_count: 0,
    };
    journal.resident_prompt_origin = Some(origin);
    journal.resident_completion = Some(Pending { turn });
    journal.hermes_session = Some(before);
    journal.next_operation_id = journal.next_operation_id.max(95);
    atomic_json(&config.state_dir.join("journal.json"), journal)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(tag: &str) -> (PathBuf, CompletedTurn, Value) {
        let (root, rt) = crate::tests::restart_resolution_fixture(tag);
        let before = HermesSession {
            id: "session".into(),
            workspace: root.join("workspace"),
            load_verified: true,
            state_fingerprint: Some("old-fingerprint".into()),
            retention_issue: None,
            pending_prompt: true,
        };
        let mut after = before.clone();
        after.pending_prompt = false;
        after.state_fingerprint = Some("final-fingerprint".into());
        let acp = json!({"stopReason":"end_turn","miniSourceFinalText":"the answer"});
        let turn = CompletedTurn {
            kind: "mini-resident-completed-turn-v1".into(),
            origin: json!({"residentPromptId":"a".repeat(64),
            "promptSha256":"b".repeat(64),"promptOperationId":42,"sessionId":"session"}),
            binding_sha256: hash(&rt.journal.binding).unwrap(),
            config_sha256: hash(&rt.config).unwrap(),
            acp_result_sha256: hash(&acp).unwrap(),
            acp_result: acp,
            provider_replays_sha256: "c".repeat(64),
            session_before: before,
            session_after: after,
            registered_shared_application_count: 0,
        };
        let resident = json!({"completed":7,"pending":{"residentPromptId":"a".repeat(64),"promptSha256":"b".repeat(64),
            "inputSha256":"d".repeat(64),"attachmentId":2,"requestId":3},"lastInput":"older","lastCompletion":null,
            "returnPending":false,"returned":null});
        (root, turn, resident)
    }
    #[test]
    fn source_receipt_supports_lost_or_matching_frame_without_counting_twice() {
        let (root, turn, resident) = fixture("completion-frame");
        let bytes = serde_json::to_vec_pretty(&resident).unwrap();
        let first = transition(&turn, &root, &bytes).unwrap();
        assert_eq!(first.completed_ordinal, 8);
        let mut received = resident.clone();
        received["lastCompletion"] = first.completion_frame.clone();
        let normal = transition(&turn, &root, &serde_json::to_vec(&received).unwrap()).unwrap();
        assert_eq!(first.resident_after, normal.resident_after);
        assert!(first.accepts(first.resident_after.as_bytes()));
        assert!(
            transition(&turn, &root, first.resident_after.as_bytes()).is_err(),
            "already received is only accepted through immutable receiving archive"
        );
        let mut other = resident;
        other["pending"]["residentPromptId"] = json!("e".repeat(64));
        assert!(transition(&turn, &root, &serde_json::to_vec(&other).unwrap()).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn publication_reentry_accepts_exact_staging_and_after_bytes_only() {
        let (root, turn, resident) = fixture("completion-publication");
        let bytes = serde_json::to_vec_pretty(&resident).unwrap();
        let receiving = transition(&turn, &root, &bytes).unwrap();
        receiving.validate(&turn, &root).unwrap();
        fs::write(root.join("resident.json"), &bytes).unwrap();
        let temp = root.join(format!(
            ".resident.json.migration-{}.tmp",
            &receiving.turn_sha256[..16]
        ));
        write_new(&temp, receiving.resident_after.as_bytes()).unwrap(); // crash after staging fsync
        publish_resident(&receiving).unwrap();
        let after = fs::read(root.join("resident.json")).unwrap();
        publish_resident(&receiving).unwrap(); // crash after rename, before received receipt
        assert_eq!(fs::read(root.join("resident.json")).unwrap(), after);
        assert_eq!(
            serde_json::from_slice::<Value>(&after).unwrap()["completed"],
            8
        );
        let mut foreign: Value = serde_json::from_slice(&after).unwrap();
        foreign["completed"] = json!(9);
        fs::write(
            root.join("resident.json"),
            serde_json::to_vec(&foreign).unwrap(),
        )
        .unwrap();
        assert!(publish_resident(&receiving).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn partial_staging_and_forged_counter_archive_are_retained_and_refused() {
        let (root, turn, resident) = fixture("completion-foreign");
        let bytes = serde_json::to_vec_pretty(&resident).unwrap();
        let mut receiving = transition(&turn, &root, &bytes).unwrap();
        fs::write(root.join("resident.json"), &bytes).unwrap();
        let temp = root.join(format!(
            ".resident.json.migration-{}.tmp",
            &receiving.turn_sha256[..16]
        ));
        write_new(&temp, b"partial").unwrap();
        assert!(publish_resident(&receiving).is_err());
        assert_eq!(fs::read(&temp).unwrap(), b"partial");
        assert_eq!(fs::read(root.join("resident.json")).unwrap(), bytes);
        receiving.completed_ordinal = 99;
        assert!(receiving.validate(&turn, &root).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn session_receiver_accepts_only_captured_before_and_after() {
        let (root, turn, _) = fixture("completion-session");
        assert!(turn.session_matches(&turn.session_before).unwrap());
        assert!(turn.session_matches(&turn.session_after).unwrap());
        let mut altered = turn.session_after.clone();
        altered.state_fingerprint = Some("different bytes".into());
        assert!(!turn.session_matches(&altered).unwrap());
        altered = turn.session_after.clone();
        altered.id = "other-session".into();
        assert!(!turn.session_matches(&altered).unwrap());
        let mut wrong = turn;
        wrong.acp_result["stopReason"] = json!("max_iterations");
        assert!(wrong.validate().is_err());
        fs::remove_dir_all(root).unwrap();
    }

    fn receiving_status(turn: &CompletedTurn, state: &Path) -> Status {
        Status {
            disposition: quiescence::Disposition::RestartWithRetainedUncertainty,
            can_restart_retaining_state: true,
            closed_checkpoint: false,
            full_resume_ready: false,
            retained: vec![
                "resident_completion",
                "hermes_pending_prompt",
                "resident_pending_prompt",
            ],
            active: vec![],
            evidence_required: vec![],
            observations: vec![json!({"slot":"parent","task":"7",
                "state":{"grain":{"status":"2","reserved":"0"},"nativeRead":{"height":"87","root":"fixture-root"}}})],
            journal_sha256: "e".repeat(64),
            next_operation_id: 80,
            binding_sha256: turn.binding_sha256.clone(),
            config_sha256: Some(turn.config_sha256.clone()),
            controller_pid: std::process::id(),
            worker_unit: None,
            exact_recovery: vec![],
            resident_state: Some(state.into()),
            resume_evidence_required: vec![],
            session_integrity_errors: vec![],
            // Even a fresh locked inspection is a snapshot, not lasting permission.
            snapshot_only: true,
        }
    }

    #[test]
    fn each_fresh_receiving_attempt_keeps_exact_status_and_receipt_evidence() {
        let (root, turn, resident) = fixture("completion-evidence");
        let bytes = serde_json::to_vec_pretty(&resident).unwrap();
        let receiving = transition(&turn, &root, &bytes).unwrap();
        let mut status = receiving_status(&turn, &root);
        let first = archive_quiescence(&root, &turn, &receiving, &bytes, &status).unwrap();
        let original = fs::read(&first.path).unwrap();
        let archived: QuiescenceEvidence = read(&first.path).unwrap();
        assert_eq!(archived.status, serde_json::to_value(&status).unwrap());
        assert_eq!(archived.resident_sha256, sha256_bytes(&bytes).unwrap());
        validate_quiescence_archive(&root, &turn, &receiving, &first).unwrap();
        let receipt = completion_receipt(&turn, &receiving, &first).unwrap();
        assert_eq!(
            receipt["quiescenceEvidence"],
            serde_json::to_value(&first).unwrap()
        );

        // A retry after the first snapshot has been archived gets its own
        // exact fresh evidence; it never rewrites the earlier native views.
        status.next_operation_id += 1;
        status.journal_sha256 = "f".repeat(64);
        let second = archive_quiescence(&root, &turn, &receiving, &bytes, &status).unwrap();
        assert_ne!(first, second);
        assert_eq!(fs::read(&first.path).unwrap(), original);
        validate_quiescence_archive(&root, &turn, &receiving, &first).unwrap();
        validate_quiescence_archive(&root, &turn, &receiving, &second).unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn completion_receipt_refuses_tampered_foreign_or_unclosed_evidence() {
        let (root, turn, resident) = fixture("completion-evidence-refusal");
        let bytes = serde_json::to_vec_pretty(&resident).unwrap();
        let receiving = transition(&turn, &root, &bytes).unwrap();
        let status = receiving_status(&turn, &root);
        let evidence = archive_quiescence(&root, &turn, &receiving, &bytes, &status).unwrap();
        let mut foreign = evidence.clone();
        foreign.path = root.join("unrelated-evidence.json");
        assert!(validate_quiescence_archive(&root, &turn, &receiving, &foreign).is_err());
        let mut other_turn = turn.clone();
        other_turn.origin["residentPromptId"] = json!("e".repeat(64));
        assert!(validate_quiescence_archive(&root, &other_turn, &receiving, &evidence).is_err());

        let mut unclosed = receiving_status(&turn, &root);
        unclosed.observations[0]["state"]["grain"]["reserved"] = json!("1");
        assert!(archive_quiescence(&root, &turn, &receiving, &bytes, &unclosed).is_err());
        let mut wrong_config = receiving_status(&turn, &root);
        wrong_config.config_sha256 = Some("f".repeat(64));
        assert!(archive_quiescence(&root, &turn, &receiving, &bytes, &wrong_config).is_err());

        fs::write(&evidence.path, b"partial or changed evidence").unwrap();
        assert!(validate_quiescence_archive(&root, &turn, &receiving, &evidence).is_err());
        assert!(archive_quiescence(&root, &turn, &receiving, &bytes, &status).is_err());
        assert_eq!(
            fs::read(&evidence.path).unwrap(),
            b"partial or changed evidence"
        );
        fs::remove_dir_all(root).unwrap();
    }
}
