//! Upgrade inspection is a snapshot, never permission to erase or replay custody.
//! Unlike terminal presentation, this examines every durable work family. The
//! pure projection performs no I/O. `inspect_quiescence` adds fresh signed reads
//! and physical stop observations while holding the resident lock; it never
//! settles, clears, acknowledges, pays, starts a worker, or sends to a provider.
use crate::*;
use std::collections::BTreeSet;

#[derive(Debug, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Disposition {
    Active,
    EvidenceRequired,
    RestartWithRetainedUncertainty,
    ClosedCheckpoint,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Status {
    pub disposition: Disposition,
    pub can_restart_retaining_state: bool,
    pub closed_checkpoint: bool,
    pub full_resume_ready: bool,
    pub retained: Vec<&'static str>,
    pub active: Vec<&'static str>,
    pub evidence_required: Vec<String>,
    pub observations: Vec<Value>,
    pub journal_sha256: String,
    pub next_operation_id: u64,
    pub binding_sha256: String,
    pub config_sha256: Option<String>,
    pub controller_pid: u32,
    pub worker_unit: Option<String>,
    pub exact_recovery: Vec<Recovery>,
    pub resident_state: Option<PathBuf>,
    pub resident_requests_sha256: Option<String>,
    pub resume_evidence_required: Vec<String>,
    pub session_integrity_errors: Vec<String>,
    pub snapshot_only: bool,
}

#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(crate) struct Recovery {
    family: &'static str,
    operation_id: u64,
    path: Option<PathBuf>,
    possible_effect: bool,
}

fn exact_recovery(j: &Journal) -> Vec<Recovery> {
    let mut out = Vec::new();
    for (family, pending) in [
        ("parent", &j.pending),
        ("tool", &j.tool_pending),
        ("provider", &j.provider_pending),
        ("dispatch", &j.dispatch_pending),
    ] {
        if let Some(p) = pending {
            out.push(Recovery {
                family,
                operation_id: p.operation_id,
                path: Some(p.attempt.clone()),
                possible_effect: true,
            });
        }
    }
    if let Some(a) = &j.provider_attempt {
        out.push(Recovery {
            family: "provider-request",
            operation_id: a.id,
            path: Some(a.request_path.clone()),
            possible_effect: a.send_started,
        });
    }
    if let Some(a) = &j.dispatch_attempt {
        out.push(Recovery {
            family: "dispatch-request",
            operation_id: a.id,
            path: Some(a.request_path.clone()),
            possible_effect: a.send_started,
        });
    }
    if let Some(a) = &j.application_api_attempt {
        out.push(Recovery {
            family: "application-api",
            operation_id: a.operation_id,
            path: Some(a.request_path.clone()),
            possible_effect: !matches!(
                a.phase,
                ApplicationApiPhase::Prepared
                    | ApplicationApiPhase::BindingVerified
                    | ApplicationApiPhase::NoDispatch
            ),
        });
    }
    if let Some(a) = &j.foreground_attempt {
        out.push(Recovery {
            family: "foreground",
            operation_id: a.operation_id,
            path: Some(a.request_path.clone()),
            possible_effect: !matches!(
                a.phase,
                ForegroundPhase::Prepared | ForegroundPhase::Reserved
            ),
        });
    }
    if let Some(a) = &j.workspace_attempt {
        out.push(Recovery {
            family: "workspace",
            operation_id: a.operation_id,
            path: Some(a.attempt.clone()),
            possible_effect: !a.no_submit,
        });
    }
    if let Some(a) = &j.room_attempt {
        out.push(Recovery {
            family: "room",
            operation_id: a.operation_id,
            path: None,
            possible_effect: a.payment_started || a.write_started,
        });
    }
    if let Some(a) = &j.birth_pending {
        out.push(Recovery {
            family: "birth",
            operation_id: a.operation_id,
            path: None,
            possible_effect: true,
        });
    }
    out
}

/// Not deserializable: a caller cannot assert process or native evidence in JSON.
struct Evidence {
    journal_sha256: String,
    observations: Vec<Value>,
    errors: Vec<String>,
    stopped: bool,
    resident: ResidentEvidence,
    session_error: Option<String>,
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum ResidentEvidence {
    Unknown,
    NotConfigured,
    Stopped {
        prompt_pending: bool,
        return_pending: bool,
        queued_requests: bool,
        started_request: bool,
        maintenance_pending: bool,
    },
}

fn journal_digest(j: &Journal) -> Result<String> {
    sha256_bytes(&serde_json::to_vec(j).map_err(|e| e.to_string())?)
}

/// Same unreserved semantic boundary accepted by source-owned foreground
/// recovery. Status 2 is soft-running, not a reserved allowance; physical
/// worker/submitter stop proof remains separately mandatory.
pub(crate) fn signed_unreserved_boundary(state: &Value) -> bool {
    matches!(
        state.pointer("/grain/status").and_then(Value::as_str),
        Some("0" | "1" | "2" | "6")
    ) && state.pointer("/grain/reserved").and_then(Value::as_str) == Some("0")
}

pub(crate) fn retained(j: &Journal, resident: ResidentEvidence) -> Vec<&'static str> {
    let mut out = Vec::new();
    macro_rules! marker { ($($field:ident),+ $(,)?) => { $(
        if j.$field.is_some() { out.push(stringify!($field)); }
    )+ }; }
    marker!(
        pending,
        tool_pending,
        provider_pending,
        dispatch_pending,
        child,
        settlement_due,
        parent_hold,
        tool_hold,
        provider_hold,
        dispatch_hold,
        provider_attempt,
        dispatch_attempt,
        application_api_attempt,
        foreground_attempt,
        birth_operation,
        birth_pending,
        workspace_attempt,
        room_attempt,
        workspace_birth,
        resident_delivery,
        resident_completion,
        prompt_witness
    );
    if j.hard_reconnect_pending {
        out.push("hard_reconnect_pending");
    }
    if j.connection == Connection::Fenced {
        out.push("connection_fenced");
    }
    if !j.unresolved_external.is_empty() {
        out.push("unresolved_external");
    }
    if let Some(session) = &j.hermes_session {
        if session.pending_prompt {
            out.push("hermes_pending_prompt");
        }
        if session.retention_issue.is_some() {
            out.push("hermes_retention_issue");
        }
    }
    // Historical definite receipts, replay cache, request counts, draft
    // proposals and birth registry entries are retained evidence, not work.
    // Latest unresolved history is still work even if its active slot is absent.
    let mut seen = BTreeSet::new();
    if j.workspace_resolutions
        .iter()
        .rev()
        .any(|r| seen.insert(r.operation_id) && r.resolution == "uncertain")
    {
        out.push("workspace_uncertain_resolution");
    }
    let mut seen = BTreeSet::new();
    if j.foreground_history
        .iter()
        .rev()
        .any(|r| seen.insert(r.operation_id) && r.phase == ForegroundPhase::Uncertain)
    {
        out.push("foreground_uncertain_history");
    }
    let mut seen = BTreeSet::new();
    if j.application_api_history
        .iter()
        .rev()
        .any(|r| seen.insert(r.operation_id) && r.phase == ApplicationApiPhase::Uncertain)
    {
        out.push("application_api_uncertain_history");
    }
    match resident {
        ResidentEvidence::Stopped {
            prompt_pending,
            return_pending,
            queued_requests,
            started_request,
            maintenance_pending,
        } => {
            if prompt_pending {
                out.push("resident_pending_prompt");
            }
            if return_pending {
                out.push("resident_return_pending");
            }
            if queued_requests {out.push("resident_queued_requests");}
            if started_request {out.push("resident_started_request");}
            if maintenance_pending {out.push("resident_maintenance_pending");}
        }
        ResidentEvidence::Unknown | ResidentEvidence::NotConfigured => {}
    }
    out
}

fn project(j: &Journal, active: Vec<&'static str>, evidence: Option<&Evidence>) -> Result<Status> {
    let digest = journal_digest(j)?;
    let resident = evidence.map_or(ResidentEvidence::Unknown, |e| e.resident);
    let retained = retained(j, resident);
    let mut required = Vec::new();
    let stopped = if let Some(e) = evidence {
        required.extend(e.errors.clone());
        if e.journal_sha256 != digest {
            required.push("journal changed after evidence collection".into());
        }
        if !e.stopped {
            required.push("current submitter/worker stop evidence absent".into());
        }
        e.stopped && e.journal_sha256 == digest
    } else {
        required.push("fresh process-stop and signed purse observations required".into());
        false
    };
    if matches!(resident, ResidentEvidence::Unknown) {
        required.push("resident configuration, lock and durable state must be inspected".into());
    }
    let can_restart =
        active.is_empty() && stopped && !matches!(resident, ResidentEvidence::Unknown);
    let observations = evidence.map_or_else(Vec::new, |e| e.observations.clone());
    let native_closed = !observations.is_empty()
        && observations
            .iter()
            .all(|o| signed_unreserved_boundary(&o["state"]));
    if evidence.is_some() && !native_closed {
        required.push("all configured purses need fresh signed unreserved boundaries".into());
    }
    let closed = can_restart && retained.is_empty() && required.is_empty() && native_closed;
    let mut resume_required = Vec::new();
    if let Some(error) = evidence.and_then(|e| e.session_error.clone()) {
        resume_required.push(error);
    }
    let session_integrity_errors = resume_required.clone();
    if j.hermes_session.as_ref().is_some_and(|s| !s.load_verified) {
        resume_required
            .push("retained session requires fresh session/load before another prompt".into());
    }
    let resume = closed
        && resume_required.is_empty()
        && j.hermes_session.as_ref().map_or(true, |s| {
            s.load_verified
                && s.state_fingerprint.is_some()
                && s.retention_issue.is_none()
                && !s.pending_prompt
        });
    let disposition = if !active.is_empty() {
        Disposition::Active
    } else if closed {
        Disposition::ClosedCheckpoint
    } else if can_restart && !retained.is_empty() {
        Disposition::RestartWithRetainedUncertainty
    } else {
        Disposition::EvidenceRequired
    };
    Ok(Status {
        disposition,
        can_restart_retaining_state: can_restart,
        closed_checkpoint: closed,
        full_resume_ready: resume,
        retained,
        active,
        evidence_required: required,
        observations,
        journal_sha256: digest,
        next_operation_id: j.next_operation_id,
        binding_sha256: sha256_bytes(&serde_json::to_vec(&j.binding).map_err(|e| e.to_string())?)?,
        config_sha256: None,
        controller_pid: std::process::id(),
        worker_unit: j.child.as_ref().and_then(|c| c.unit.clone()),
        exact_recovery: exact_recovery(j),
        resident_state: None,
        resident_requests_sha256: None,
        resume_evidence_required: resume_required,
        session_integrity_errors,
        snapshot_only: true,
    })
}

/// Mirrors the resident's versioned journal, refusing unknown schema instead
/// of treating an unfamiliar pending marker as absent. No field is modified.
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
#[allow(dead_code)] // Full strict schema is retained even for fields not projected.
struct ResidentJournal {
    completed: u64,
    pending: Option<Value>,
    last_input: Option<String>,
    last_completion: Option<Value>,
    #[serde(default)]
    return_pending: bool,
    #[serde(default)]
    returned: Option<Value>,
}

pub(crate) struct ResidentGuard {
    _lock: Option<File>,
    evidence: ResidentEvidence,
    path: Option<PathBuf>,
    bytes: Option<Vec<u8>>,
    request_bytes: Option<Vec<u8>>,
    config_sha256: String,
}

/// Operator socket client; neither attaches a worker nor changes connection mode.
pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let usage="usage: grain-runtime quiescence status ADMIN_SOCKET | quiescence inspect ADMIN_SOCKET RESIDENT_STATE_DIR|none";
    let command = match args {
        [mode, _] if mode == "status" => "quiescence status".to_owned(),
        [mode, _, resident] if mode == "inspect" => format!(
            "quiescence inspect {}",
            resident
                .to_str()
                .ok_or("resident state path must be UTF-8")?
        ),
        _ => return Err(usage.into()),
    };
    let response = control::admin_call(Path::new(&args[1]), &command)?;
    let value: Value = serde_json::from_str(&response).map_err(|_| response.clone())?;
    if value["type"] != "mini-grain-quiescence-v1" {
        return Err("unexpected quiescence response".into());
    }
    println!("{value}");
    Ok(())
}

impl ResidentGuard {
    pub(crate) fn acquire(config: &Config, path: Option<&Path>) -> Result<Self> {
        let config_sha256 = sha256_bytes(&serde_json::to_vec(config).map_err(|e| e.to_string())?)?;
        let Some(path) = path else {
            if config
                .tool_task
                .as_ref()
                .and_then(|t| t.room.as_ref())
                .is_some()
            {
                return Err(
                    "room-enabled controller requires explicit resident state directory".into(),
                );
            }
            return Ok(Self {
                _lock: None,
                evidence: ResidentEvidence::NotConfigured,
                path: None,
                bytes: None,
                request_bytes: None,
                config_sha256,
            });
        };
        if path.parent() != Some(config.state_dir.as_path()) {
            return Err("resident state must be a direct child of controller stateDir".into());
        }
        let meta = fs::symlink_metadata(path).map_err(|e| format!("resident state: {e}"))?;
        if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
            return Err("resident state must be an owned private real directory".into());
        }
        // Inspection neither creates a state nor upgrades missing custody to fresh.
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path.join("resident.lock"))
            .map_err(|e| format!("resident lock: {e}"))?;
        let meta = lock.metadata().map_err(|e| e.to_string())?;
        if !meta.is_file() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
            return Err("resident lock must be an owned private regular file".into());
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
            return Err("resident driver is active or its lock is unavailable".into());
        }
        let bytes = bounded_regular_file(&path.join("resident.json"), 65_536)?;
        let state: ResidentJournal =
            serde_json::from_slice(&bytes).map_err(|e| format!("resident state schema: {e}"))?;
        let requests=crate::resident_requests::custody_snapshot(path)?;
        Ok(Self {
            _lock: Some(lock),
            evidence: ResidentEvidence::Stopped {
                prompt_pending: state.pending.is_some(),
                return_pending: state.return_pending,
                queued_requests: requests.queued,
                started_request: requests.started,
                maintenance_pending: requests.maintenance_pending,
            },
            path: Some(path.to_owned()),
            bytes: Some(bytes),
            request_bytes: requests.bytes,
            config_sha256,
        })
    }

    pub(crate) fn path(&self) -> Result<&Path> {
        self.path
            .as_deref()
            .ok_or_else(|| "resident state is not configured".into())
    }

    pub(crate) fn bytes(&self) -> Result<&[u8]> {
        self.bytes
            .as_deref()
            .ok_or_else(|| "resident state is not configured".into())
    }

    pub(crate) fn request_bytes(&self)->Option<&[u8]> {self.request_bytes.as_deref()}

    pub(crate) fn assert_unchanged(&self) -> Result<()> {
        if let Some(path) = &self.path {
            if bounded_regular_file(&path.join("resident.json"), 65_536)?.as_slice()
                != self.bytes()?
            {
                return Err("resident journal changed while its source-owned lock was held".into());
            }
            if crate::resident_requests::custody_snapshot(path)?.bytes!=self.request_bytes {
                return Err("resident request custody changed while its source-owned lock was held".into());
            }
        }
        Ok(())
    }

    fn assert_config(&self, config: &Config) -> Result<()> {
        if sha256_bytes(&serde_json::to_vec(config).map_err(|e| e.to_string())?)?
            != self.config_sha256
        {
            return Err("resident guard belongs to another controller configuration".into());
        }
        self.assert_unchanged()
    }
}

impl Runtime {
    fn quiescence_active(&self) -> Vec<&'static str> {
        let mut out = Vec::new();
        if self.child.is_some() {
            out.push("owned_worker");
        }
        if self.prompt_active {
            out.push("prompt_active");
        }
        if self.foreground_operation.is_some() {
            out.push("foreground_operation");
        }
        if self.startup_recovery_active {
            out.push("startup_recovery");
        }
        if !self.custody_gate.is_idle() {
            out.push("resource_client");
        }
        if self.provider_lease.is_some() {
            out.push("provider_lease");
        }
        match self.provider_control.lock() {
            Ok(gate) => {
                if gate.as_ref().is_some_and(|g| !g.is_idle()) {
                    out.push("provider_gateway");
                }
            }
            Err(_) => out.push("provider_gateway_lock_unavailable"),
        }
        out
    }

    pub(crate) fn quiescence_stop_proof(&self) -> Result<()> {
        if !self.quiescence_active().is_empty() {
            return Err("controller has active work".into());
        }
        self.quiescence_physical_stop_proof()
    }

    pub(crate) fn quiescence_recovery_stop_proof(&self) -> Result<()> {
        if !self.startup_recovery_active || self.quiescence_active().iter().any(|marker|*marker!="startup_recovery") {
            return Err("provider startup recovery has another active operation".into());
        }
        self.quiescence_physical_stop_proof()
    }

    fn quiescence_physical_stop_proof(&self) -> Result<()> {
        // Fresh, not the cached startup boolean. Includes custody clients in
        // the controller cgroup; a missing journal child alone proves nothing.
        prove_prior_run_stopped(&self.config.task)?;
        if self.current_pgid.load(Ordering::SeqCst) != 0 {
            return Err("controller retains an owned process group".into());
        }
        let unit = self
            .current_unit
            .lock()
            .map_err(|_| "worker unit lock poisoned")?;
        if unit.is_some() {
            return Err("controller retains a current worker unit".into());
        }
        if let Some(record) = &self.journal.child {
            let unit = record
                .unit
                .as_deref()
                .ok_or("retained unscoped child requires physical audit")?;
            if record.launch_gate_protocol.as_deref() != Some("mini-grain-launch-gate-v1") {
                return Err("retained child has no exact launch-gate protocol".into());
            }
            prove_worker_unit_stopped(&self.config.task, record, unit)?;
        }
        Ok(())
    }

    /// Pure status for UI/admission. It deliberately cannot certify a closed
    /// checkpoint without the fresh evidence collected by the inspect path.
    pub(crate) fn quiescence_status(&self) -> Result<Status> {
        self.quiescence_project(None)
    }

    fn quiescence_project(&self, evidence: Option<&Evidence>) -> Result<Status> {
        let mut status = project(&self.journal, self.quiescence_active(), evidence)?;
        // Digest of the parsed config actually held by this process, not a
        // possibly edited file on disk. Binding digest is retained separately.
        status.config_sha256 = Some(sha256_bytes(
            &serde_json::to_vec(&self.config).map_err(|e| e.to_string())?,
        )?);
        if status.worker_unit.is_none() {
            status.worker_unit = self
                .current_unit
                .lock()
                .map_err(|_| "worker unit lock poisoned")?
                .as_ref()
                .map(|(unit, _)| unit.clone());
        }
        Ok(status)
    }

    /// Explicit active-controller inspect path. Native query_as is the existing
    /// signed client path, not a new lifecycle. Its exact query artifacts remain
    /// in stateDir. Observe every configured purse, even with no local marker.
    /// The event loop must serialize this command; supervisor must stop ingress
    /// before using its snapshot to replace a process or take a checkpoint.
    pub(crate) fn inspect_quiescence(&mut self, resident_path: Option<&Path>) -> Result<Status> {
        let resident = match ResidentGuard::acquire(&self.config, resident_path) {
            Ok(resident) => resident,
            Err(error) => {
                return self.quiescence_missing_evidence(
                    error,
                    ResidentEvidence::Unknown,
                    resident_path,
                )
            }
        };
        self.inspect_quiescence_locked(&resident)
    }

    /// The caller may retain this guard through a narrowly typed resident
    /// reconciliation. Never drop/reacquire between inspection and mutation.
    pub(crate) fn inspect_quiescence_locked(&mut self, resident: &ResidentGuard) -> Result<Status> {
        self.inspect_quiescence_locked_via(resident, None)
    }

    /// Same complete inspection and original binding; a root-attested token
    /// changes only signed-query routing and annotates every observation.
    pub(crate) fn inspect_quiescence_locked_via(&mut self, resident: &ResidentGuard,
        transport: Option<&crate::quiescence_transport::AuthorizedTransport>) -> Result<Status> {
        resident.assert_config(&self.config)?;
        let resident_path = resident.path.as_deref();
        if let Err(error) = self.quiescence_stop_proof() {
            return self.quiescence_missing_evidence(error, resident.evidence, resident_path);
        }
        let mut authorities = vec![("parent", self.parent())];
        if self.config.tool_task.is_some() {
            authorities.push(("tool", self.tool()?));
        }
        if self.config.provider_task.is_some() {
            authorities.push(("provider", self.provider()?));
        }
        if self.config.dispatch_task.is_some() {
            authorities.push(("dispatch", self.dispatch()?));
        }
        let mut observations = Vec::new();
        let mut errors = Vec::new();
        for (slot, authority) in authorities {
            match self.query_as_via(&authority, transport) {
                Ok(state) => {
                    let mut observation = json!({"slot":slot,"task":authority.task,"state":state});
                    if let Some(via) = transport { observation["transportEvidence"] = via.evidence(); }
                    observations.push(observation)
                }
                Err(error) => errors.push(format!("{slot} signed boundary: {error}")),
            }
        }
        let session_error = self.journal.hermes_session.as_ref().and_then(|session| {
            let home = session.workspace.join(".hermes");
            let check = (|| -> Result<()> {
                let meta = fs::symlink_metadata(&home).map_err(|e| format!("Hermes home: {e}"))?;
                if !meta.is_dir()
                    || meta.uid() != unsafe { libc::geteuid() }
                    || meta.mode() & 0o077 != 0
                {
                    return Err("Hermes home is not an owned private real directory".into());
                }
                if session.state_fingerprint.is_none()
                    || hermes_state_fingerprint(&home)? != session.state_fingerprint
                {
                    return Err("retained session fingerprint is missing or changed".into());
                }
                Ok(())
            })();
            check.err()
        });
        let stopped = match self.quiescence_stop_proof() {
            Ok(()) => true,
            Err(error) => {
                errors.push(error);
                false
            }
        };
        let evidence = Evidence {
            journal_sha256: journal_digest(&self.journal)?,
            observations,
            errors,
            stopped,
            resident: resident.evidence,
            session_error,
        };
        resident.assert_unchanged()?;
        let mut status = self.quiescence_project(Some(&evidence))?;
        status.resident_state = resident_path.map(Path::to_path_buf);
        status.resident_requests_sha256 = resident.request_bytes().map(sha256_bytes).transpose()?;
        Ok(status)
    }

    fn quiescence_missing_evidence(
        &self,
        error: String,
        resident: ResidentEvidence,
        resident_path: Option<&Path>,
    ) -> Result<Status> {
        let evidence = Evidence {
            journal_sha256: journal_digest(&self.journal)?,
            observations: Vec::new(),
            errors: vec![error],
            stopped: false,
            resident,
            session_error: None,
        };
        let mut status = self.quiescence_project(Some(&evidence))?;
        status.resident_state = resident_path.map(Path::to_path_buf);
        Ok(status)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fresh() -> Journal {
        Journal::fresh(json!({}))
    }
    #[test]
    fn soft_running_zero_hold_needs_physical_proof_but_is_semantically_closed() {
        let j = fresh();
        let mut e = evidence(&j);
        e.observations[0]["state"]["grain"]["status"] = json!("2");
        assert!(project(&j, vec![], Some(&e)).unwrap().closed_checkpoint);
        assert!(
            !project(&j, vec!["owned_worker"], Some(&e))
                .unwrap()
                .closed_checkpoint
        );
        e.observations[0]["state"]["grain"]["reserved"] = json!("3");
        assert!(!project(&j, vec![], Some(&e)).unwrap().closed_checkpoint);
    }
    #[test]
    fn fresh_session_load_is_resume_advisory_not_a_false_integrity_error() {
        let mut j = fresh();
        j.hermes_session = Some(HermesSession {
            id: "retained".into(),
            workspace: "/owned/workspace".into(),
            load_verified: false,
            state_fingerprint: Some("a".repeat(64)),
            retention_issue: None,
            pending_prompt: false,
        });
        let s = project(&j, vec![], Some(&evidence(&j))).unwrap();
        assert!(s.closed_checkpoint);
        assert!(!s.full_resume_ready);
        assert!(s.session_integrity_errors.is_empty());
        assert!(!s.resume_evidence_required.is_empty());
    }
    fn evidence(j: &Journal) -> Evidence {
        Evidence {
            journal_sha256: journal_digest(j).unwrap(),
            errors: vec![],
            stopped: true,
            session_error: None,
            resident: ResidentEvidence::Stopped {
                prompt_pending: false,
                return_pending: false,
                queued_requests:false,started_request:false,maintenance_pending:false,
            },
            observations: vec![
                json!({"slot":"parent","state":{"grain":{"status":"0","reserved":"0"}}}),
            ],
        }
    }
    #[test]
    fn absent_markers_do_not_prove_closed() {
        let j = fresh();
        let s = project(&j, vec![], None).unwrap();
        assert_eq!(s.disposition, Disposition::EvidenceRequired);
        assert!(!s.closed_checkpoint);
    }
    #[test]
    fn all_pending_authorities_block_closure_but_allow_retained_restart() {
        for slot in [
            AuthoritySlot::Parent,
            AuthoritySlot::Tool,
            AuthoritySlot::Provider,
            AuthoritySlot::Dispatch,
        ] {
            let mut j = fresh();
            *j.pending_for_mut(slot) = Some(Pending {
                operation_id: 1,
                operation: "reserve".into(),
                attempt: "exact/attempt".into(),
                uncertain: true,
                publication: None,
            });
            let s = project(&j, vec![], Some(&evidence(&j))).unwrap();
            assert_eq!(s.disposition, Disposition::RestartWithRetainedUncertainty);
            assert!(!s.full_resume_ready);
            assert!(j.pending_for(slot).as_ref().unwrap().uncertain);
        }
    }
    #[test]
    fn resident_pending_or_return_is_not_erased_by_controller_readiness() {
        let j = fresh();
        for (p, r) in [(true, false), (false, true)] {
            let mut e = evidence(&j);
            e.resident = ResidentEvidence::Stopped {
                prompt_pending: p,
                return_pending: r,
                queued_requests:false,started_request:false,maintenance_pending:false,
            };
            let s = project(&j, vec![], Some(&e)).unwrap();
            assert!(s.can_restart_retaining_state);
            assert!(!s.closed_checkpoint);
        }
    }
    #[test]
    fn request_queue_custody_blocks_reassignment_without_a_resident_pending_marker() {
        let j=fresh();
        for (queued,started,maintenance) in [(true,false,false),(false,true,false),(false,false,true)] {
            let mut e=evidence(&j);
            e.resident=ResidentEvidence::Stopped {prompt_pending:false,return_pending:false,
                queued_requests:queued,started_request:started,maintenance_pending:maintenance};
            let status=project(&j,vec![],Some(&e)).unwrap();
            assert!(status.can_restart_retaining_state);
            assert!(!status.closed_checkpoint,"request custody cannot disappear on account rebinding");
            assert_eq!(status.retained.len(),1);
        }
    }
    #[test]
    fn native_hold_without_local_marker_blocks_closed_checkpoint() {
        let j = fresh();
        let mut e = evidence(&j);
        e.observations
            .push(json!({"slot":"provider","state":{"grain":{"status":"3","reserved":"7000"}}}));
        let s = project(&j, vec![], Some(&e)).unwrap();
        assert!(!s.closed_checkpoint);
        assert!(s.can_restart_retaining_state);
        assert!(!s.evidence_required.is_empty());
    }
    #[test]
    fn stale_proof_and_running_submitter_never_admit_restart() {
        let mut j = fresh();
        let e = evidence(&j);
        j.next_operation_id += 1;
        assert!(
            !project(&j, vec![], Some(&e))
                .unwrap()
                .can_restart_retaining_state
        );
        let e = evidence(&j);
        assert!(
            !project(&j, vec!["resource_client"], Some(&e))
                .unwrap()
                .can_restart_retaining_state
        );
    }
    #[test]
    fn closed_requires_complete_observations_and_keeps_historical_counts() {
        let mut j = fresh();
        j.provider_prompt_requests = 1;
        let e = evidence(&j);
        let s = project(&j, vec![], Some(&e)).unwrap();
        assert!(s.closed_checkpoint);
        assert!(s.full_resume_ready);
        let mut e = e;
        e.errors.push("tool signed boundary unavailable".into());
        assert!(!project(&j, vec![], Some(&e)).unwrap().closed_checkpoint);
        assert_eq!(j.provider_prompt_requests, 1);
    }
    #[test]
    fn provider_attempt_presence_is_never_terminal_readiness() {
        for sent in [false, true] {
            let mut j = fresh();
            j.connection = Connection::Soft;
            j.provider_attempt=Some(serde_json::from_value(json!({
                "id":1,"promptOperationId":1,"parentGeneration":"1","model":"test",
                "requestPath":"exact/request","requestBytes":2,"requestSha256":"ab",
                "sendStarted":sent,"route":{"provider":"fixture","endpoint":"http://127.0.0.1","credential":"none"}
            })).unwrap());
            let before = serde_json::to_value(&j).unwrap();
            let s = project(&j, vec![], Some(&evidence(&j))).unwrap();
            assert!(s.retained.contains(&"provider_attempt"));
            assert_eq!(s.disposition, Disposition::RestartWithRetainedUncertainty);
            assert!(!s.closed_checkpoint);
            assert_eq!(s.exact_recovery[0].operation_id, 1);
            assert_eq!(s.exact_recovery[0].possible_effect, sent);
            assert_eq!(serde_json::to_value(&j).unwrap(), before);
        }
    }
    #[test]
    fn every_hold_blocks_closure_even_if_reservation_not_confirmed() {
        for slot in [
            AuthoritySlot::Parent,
            AuthoritySlot::Tool,
            AuthoritySlot::Provider,
            AuthoritySlot::Dispatch,
        ] {
            let mut j = fresh();
            *j.hold_for_mut(slot) = Some(
                serde_json::from_value(json!({
                    "reserve":"7","charge":"1","beforeGeneration":"1","beforeTargetRoot":"2",
                    "reserveConfirmed":false,"reserveRefused":false
                }))
                .unwrap(),
            );
            assert!(
                !project(&j, vec![], Some(&evidence(&j)))
                    .unwrap()
                    .closed_checkpoint
            );
        }
    }
    #[test]
    fn unresolved_room_payment_blocks_even_before_write() {
        let mut j = fresh();
        j.room_attempt = Some(room_task::Attempt {
            resident_origin: None,
            expected_reply: None,
            operation_id: 1,
            tool: "mini_room_say".into(),
            arguments: json!({}),
            payment: None,
            tool_lifecycle_started: true,
            payment_started: true,
            write_started: false,
            submitter_stopped: true,
            resolution: None,
        });
        let s = project(&j, vec![], Some(&evidence(&j))).unwrap();
        assert!(s.retained.contains(&"room_attempt"));
        assert!(!s.closed_checkpoint);
    }
    #[test]
    fn closed_checkpoint_is_not_full_resume_when_session_evidence_changed() {
        let j = fresh();
        let mut e = evidence(&j);
        e.session_error = Some("session fingerprint changed".into());
        let s = project(&j, vec![], Some(&e)).unwrap();
        assert!(s.closed_checkpoint);
        assert!(!s.full_resume_ready);
    }
    #[test]
    fn resident_schema_refuses_unknown_pending_state() {
        assert!(serde_json::from_value::<ResidentJournal>(
            json!({"completed":0,"newPendingSend":true})
        )
        .is_err());
    }
    #[test]
    fn resident_lock_covers_the_inspection_lifetime() {
        let (root, rt) = crate::tests::restart_resolution_fixture("quiescence-resident-lock");
        let dir = rt.config.state_dir.join("resident");
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
        OpenOptions::new()
            .create_new(true)
            .read(true)
            .write(true)
            .mode(0o600)
            .open(dir.join("resident.lock"))
            .unwrap();
        fs::write(
            dir.join("resident.json"),
            br#"{"completed":0,"pending":{"requestId":2}}"#,
        )
        .unwrap();
        fs::set_permissions(dir.join("resident.json"), fs::Permissions::from_mode(0o600)).unwrap();
        let guard = ResidentGuard::acquire(&rt.config, Some(&dir)).unwrap();
        assert!(matches!(
            guard.evidence,
            ResidentEvidence::Stopped {
                prompt_pending: true,
                ..
            }
        ));
        assert!(ResidentGuard::acquire(&rt.config, Some(&dir)).is_err());
        atomic_json(&dir.join("requests.json"),&json!({"binding":{},"pending":[],"selected":null,"lastAuthor":null,
            "maintenancePending":{"residentPromptId":"orphan","revision":"revision"}})).unwrap();
        assert!(guard.assert_unchanged().is_err(),"new request custody must invalidate an absent-file snapshot");
        drop(guard);
        let guard=ResidentGuard::acquire(&rt.config,Some(&dir)).unwrap();
        assert!(matches!(guard.evidence,ResidentEvidence::Stopped {maintenance_pending:true,..}));
        assert!(guard.request_bytes().is_some());
        let before=fs::read(dir.join("requests.json")).unwrap();
        atomic_json(&dir.join("requests.json"),&json!({"binding":{},"pending":[],"selected":null,"lastAuthor":null})).unwrap();
        assert!(guard.assert_unchanged().is_err());
        assert_ne!(fs::read(dir.join("requests.json")).unwrap(),before);
        drop(guard);
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
}
