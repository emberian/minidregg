//! Reconcile one source-confirmed failed resident prompt, without replaying it.
//! This is deliberately not a general resident-journal editor. The exact prior
//! bytes, source-bound completion and current signed/physical evidence must all
//! agree while the resident lock remains held. Lost replies remain unresolved.
use crate::quiescence::{ResidentGuard, Status};
use crate::*;

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct ResidentState {
    completed: u64,
    pending: Option<Value>,
    last_input: Option<String>,
    last_completion: Option<Value>,
    #[serde(default)]
    return_pending: bool,
    #[serde(default)]
    returned: Option<Value>,
}

pub(crate) fn decode_resident_state(bytes: &[u8]) -> Result<ResidentState> {
    serde_json::from_slice(bytes).map_err(|e| format!("resident state schema: {e}"))
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct PendingIdentity {
    input_sha256: String,
    prompt_sha256: String,
    attachment_id: u64,
    request_id: u64,
    #[serde(default)]
    resident_prompt_id: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Completion {
    v: u64,
    #[serde(rename = "type")]
    kind: String,
    attachment_id: u64,
    request_id: u64,
    outcome: String,
    activity: String,
    retained_session: bool,
    review_needed: bool,
    registered_shared_application_count: usize,
    resident_pending_sha256: String,
    #[serde(default)]
    resident_origin: Option<ResidentOrigin>,
}

#[derive(Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct ResidentOrigin { resident_prompt_id:String,prompt_sha256:String,prompt_operation_id:u64,session_id:Option<String> }

struct Plan {
    before: ResidentState,
    after: ResidentState,
    prior_sha256: String,
    pending_sha256: String,
    completion_sha256: String,
    after_bytes: Vec<u8>,
}

fn hash(value: &Value) -> Result<String> {
    sha256_bytes(&serde_json::to_vec(value).map_err(|e| e.to_string())?)
}

fn is_digest(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}

fn failed_identity(bytes: &[u8], expected: &str) -> Result<(ResidentState, String, String)> {
    if !is_digest(expected) || sha256_bytes(bytes)? != expected {
        return Err("resident prior-state digest changed; inspect the exact retained state".into());
    }
    let before: ResidentState =
        serde_json::from_slice(bytes).map_err(|e| format!("resident state schema: {e}"))?;
    let pending = before
        .pending
        .as_ref()
        .ok_or("resident has no failed pending prompt")?;
    let identity: PendingIdentity = serde_json::from_value(pending.clone())
        .map_err(|e| format!("resident pending identity: {e}"))?;
    if !is_digest(&identity.input_sha256)
        || !is_digest(&identity.prompt_sha256)
        || identity.attachment_id == 0
        || identity.request_id == 0
        || identity.resident_prompt_id.as_ref().is_some_and(|id| {
            id.is_empty()
                || id.len() > 128
                || !id
                    .bytes()
                    .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
        })
    {
        return Err("resident pending identity is malformed".into());
    }
    let completion_value = before
        .last_completion
        .as_ref()
        .ok_or("resident has no authoritative completion; lost reply remains unresolved")?;
    let completion: Completion = serde_json::from_value(completion_value.clone())
        .map_err(|e| format!("resident completion identity: {e}"))?;
    let pending_sha256 = hash(pending)?;
    if completion.v != 1
        || completion.kind != "prompt-complete"
        || completion.attachment_id != identity.attachment_id
        || completion.request_id != identity.request_id
        || completion.resident_pending_sha256 != pending_sha256
    {
        return Err("resident completion does not bind this exact pending prompt".into());
    }
    if let Some(origin) = &completion.resident_origin {
        if Some(&origin.resident_prompt_id) != identity.resident_prompt_id.as_ref()
            || origin.prompt_sha256 != identity.prompt_sha256 || origin.prompt_operation_id == 0
            || origin.session_id.as_ref().is_some_and(|id|id.is_empty() || id.len()>128) {
            return Err("resident completion source origin differs from exact pending prompt".into());
        }
    }
    if !matches!(completion.outcome.as_str(), "failed" | "review-needed")
        || (completion.outcome == "review-needed") != completion.review_needed
        || !matches!(
            completion.activity.as_str(),
            "ready" | "busy" | "review-needed"
        )
    {
        return Err(
            "only an authoritative failed or review-needed completion can be reconciled".into(),
        );
    }
    // Keep source-only presentation fields in the strict accepted frame schema.
    let _ = (
        completion.retained_session,
        completion.registered_shared_application_count,
    );
    let completion_sha256 = hash(completion_value)?;
    if before.return_pending { return Err("resident return remains pending".into()); }
    Ok((before, pending_sha256, completion_sha256))
}

/// Reuse the exact authoritative failed-completion identity check for the
/// separate session-marker recovery; this grants no state mutation by itself.
pub(crate) fn bound_failed_pending(bytes: &[u8], expected: &str) -> Result<Value> {
    let (before, _, _) = failed_identity(bytes, expected)?;
    before.pending.ok_or_else(|| "resident pending disappeared".into())
}

fn plan(bytes: &[u8], expected: &str, status: &Status) -> Result<Plan> {
    let (before, pending_sha256, completion_sha256) = failed_identity(bytes, expected)?;
    if before.return_pending
        || !status.can_restart_retaining_state
        || !status.active.is_empty()
        || !status.evidence_required.is_empty()
        || !status.session_integrity_errors.is_empty()
        || status.retained.as_slice() != ["resident_pending_prompt"]
        || !status.exact_recovery.is_empty()
        || status.config_sha256.is_none()
        || status.observations.is_empty()
        || !status
            .observations
            .iter()
            .all(|o| quiescence::signed_unreserved_boundary(&o["state"]))
    {
        return Err("failed resident reconciliation requires the sole retained resident prompt and fresh closed native/process evidence".into());
    }
    let mut after = before.clone();
    after.pending = None;
    let after_bytes = serde_json::to_vec_pretty(&after).map_err(|e| e.to_string())?;
    Ok(Plan {
        before,
        after,
        prior_sha256: expected.to_owned(),
        pending_sha256,
        completion_sha256,
        after_bytes,
    })
}

fn private_directory(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(meta)
            if meta.is_dir()
                && meta.uid() == unsafe { libc::geteuid() }
                && meta.mode() & 0o077 == 0 =>
        {
            Ok(())
        }
        Ok(_) => Err("reconciliation archive is not an owned private real directory".into()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            let mut builder = fs::DirBuilder::new();
            builder.mode(0o700);
            builder
                .create(path)
                .map_err(|e| format!("reconciliation archive: {e}"))?;
            File::open(path.parent().ok_or("archive parent absent")?)
                .and_then(|f| f.sync_all())
                .map_err(|e| e.to_string())
        }
        Err(e) => Err(format!("reconciliation archive: {e}")),
    }
}

fn commit(
    guard: &ResidentGuard,
    plan: &Plan,
    status: &Status,
    controller: &[u8],
    decision_id: u64,
) -> Result<Value> {
    guard.assert_unchanged()?;
    if sha256_bytes(controller)? != status.journal_sha256 {
        return Err("controller changed after quiescence observation".into());
    }
    let state = guard.path()?;
    let archive_root = state.join("failed-reconciliations");
    private_directory(&archive_root)?;
    let archive = archive_root.join(format!("{}-{decision_id}", plan.prior_sha256));
    let mut builder = fs::DirBuilder::new();
    builder.mode(0o700);
    builder
        .create(&archive)
        .map_err(|e| format!("reconciliation decision already exists or cannot be created: {e}"))?;
    // Every file is immutable/create-new; partial prior decisions remain for
    // inspection. A later retry uses a new durable controller operation ID.
    write_new(&archive.join("resident-before.json"), guard.bytes()?)?;
    write_new(&archive.join("controller-before.json"), controller)?;
    write_new(&archive.join("resident-after.json"), &plan.after_bytes)?;
    let observed = serde_json::to_vec_pretty(status).map_err(|e| e.to_string())?;
    write_new(&archive.join("quiescence.json"), &observed)?;
    let after_sha256 = sha256_bytes(&plan.after_bytes)?;
    let decision = json!({"type":"mini-resident-failed-reconciliation-decision-v1",
        "decisionId":decision_id.to_string(),"action":"reconcile-source-confirmed-failed-prompt",
        "priorStateSha256":plan.prior_sha256,"afterStateSha256":after_sha256,
        "pendingSha256":plan.pending_sha256,"completionSha256":plan.completion_sha256,
        "controllerJournalSha256":status.journal_sha256,"controllerConfigSha256":status.config_sha256,
        "controllerBindingSha256":status.binding_sha256,"quiescenceSha256":sha256_bytes(&observed)?,
        "pending":plan.before.pending,"completion":plan.before.last_completion,
        "completed":plan.before.completed,"lastInput":plan.before.last_input,
        "promptReplayed":false,"providerOrExternalStateChanged":false});
    write_new(
        &archive.join("decision.json"),
        &serde_json::to_vec_pretty(&decision).map_err(|e| e.to_string())?,
    )?;
    File::open(&archive)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    File::open(&archive_root)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    guard.assert_unchanged()?;
    // Only this typed field changes. Completion, failed prompt, controller
    // session and exact previous bytes already have durable retained copies.
    atomic_json(&state.join("resident.json"), &plan.after)?;
    let committed = json!({"type":"mini-resident-failed-reconciliation-v1","status":"reconciled",
        "decisionId":decision_id.to_string(),"priorStateSha256":plan.prior_sha256,
        "afterStateSha256":after_sha256,"archive":archive,"promptReplayed":false,
        "completed":plan.after.completed,"lastInput":plan.after.last_input});
    write_new(
        &archive.join("committed.json"),
        &serde_json::to_vec_pretty(&committed).map_err(|e| e.to_string())?,
    )?;
    File::open(&archive)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    Ok(committed)
}

impl Runtime {
    pub(crate) fn reconcile_failed_resident(
        &mut self,
        path: &Path,
        expected: &str,
    ) -> Result<Value> {
        let guard = ResidentGuard::acquire(&self.config, Some(path))?;
        // Refuse stale operator intent before even collecting signed reads.
        if !is_digest(expected) || sha256_bytes(guard.bytes()?)? != expected {
            return Err("resident prior-state digest changed".into());
        }
        let status = self.inspect_quiescence_locked(&guard)?;
        let plan = plan(guard.bytes()?, expected, &status)?;
        let controller = serde_json::to_vec(&self.journal).map_err(|e| e.to_string())?;
        // Allocate an audit identity only; no worker, provider or native effect.
        let decision_id = self.next_id()?;
        commit(&guard, &plan, &status, &controller, decision_id)
    }
}

pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let [mode, socket, resident, expected] = args else {
        return Err("usage: grain-runtime resident-reconcile failed ADMIN_SOCKET RESIDENT_STATE_DIR EXPECTED_STATE_SHA256".into());
    };
    if mode != "failed" {
        return Err("resident reconciliation supports only failed".into());
    }
    let command = format!(
        "resident reconcile-failed {} {}",
        resident.to_str().ok_or("resident path must be UTF-8")?,
        expected.to_str().ok_or("state digest must be UTF-8")?
    );
    let response = control::admin_call(Path::new(socket), &command)?;
    let value: Value = serde_json::from_str(&response).map_err(|_| response.clone())?;
    if value["type"] != "mini-resident-failed-reconciliation-v1" {
        return Err("unexpected resident reconciliation response".into());
    }
    println!("{value}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (PathBuf, Runtime, Value, Status) {
        let (root, rt) = crate::tests::restart_resolution_fixture("failed-resident");
        let pending = json!({"inputSha256":"a".repeat(64),"promptSha256":"b".repeat(64),
            "attachmentId":7,"requestId":2,"residentPromptId":"c".repeat(32)});
        let frame = json!({"v":1,"type":"prompt-complete","attachmentId":7,"requestId":2,
            "outcome":"review-needed","activity":"review-needed","retainedSession":true,
            "reviewNeeded":true,"registeredSharedApplicationCount":0,"residentPendingSha256":hash(&pending).unwrap()});
        let state = json!({"completed":3,"pending":pending,"lastInput":"old-input","lastCompletion":frame,
            "returnPending":false,"returned":null});
        let mut status = rt.quiescence_status().unwrap();
        status.active.clear();
        status.evidence_required.clear();
        status.resume_evidence_required.clear();
        status.can_restart_retaining_state = true;
        status.retained = vec!["resident_pending_prompt"];
        status.exact_recovery.clear();
        status.observations =
            vec![json!({"slot":"parent","state":{"grain":{"status":"0","reserved":"0"}}})];
        (root, rt, state, status)
    }
    fn planned(state: &Value, status: &Status) -> Result<Plan> {
        let bytes = serde_json::to_vec(state).unwrap();
        plan(&bytes, &sha256_bytes(&bytes).unwrap(), status)
    }
    #[test]
    fn failed_completion_requires_exact_pending_hash_not_reused_request_ids() {
        let (root, rt, mut state, status) = fixture();
        assert!(planned(&state, &status).is_ok());
        state["pending"]["residentPromptId"] = json!("d".repeat(32));
        assert!(planned(&state, &status).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn missing_reply_or_unhashed_legacy_frame_never_clears_pending() {
        let (root, rt, state, status) = fixture();
        let mut missing = state.clone();
        missing["lastCompletion"] = Value::Null;
        assert!(planned(&missing, &status).is_err());
        let mut legacy = state;
        legacy["lastCompletion"]
            .as_object_mut()
            .unwrap()
            .remove("residentPendingSha256");
        assert!(planned(&legacy, &status).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn successful_or_unknown_completion_is_not_a_failed_decision() {
        let (root, rt, state, status) = fixture();
        for outcome in ["completed", "model says failed"] {
            let mut altered = state.clone();
            altered["lastCompletion"]["outcome"] = json!(outcome);
            assert!(planned(&altered, &status).is_err());
        }
        let mut altered = state;
        altered["lastCompletion"]["newPendingSend"] = json!(true);
        assert!(planned(&altered, &status).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn every_other_quiescence_blocker_and_native_hold_refuses() {
        let (root, rt, state, mut status) = fixture();
        for marker in [
            "provider_attempt",
            "provider_hold",
            "unresolved_external",
            "resident_return_pending",
            "workspace_attempt",
        ] {
            status.retained.push(marker);
            assert!(planned(&state, &status).is_err());
            status.retained.pop();
        }
        status.observations[0]["state"]["grain"]["reserved"] = json!("7");
        assert!(planned(&state, &status).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn settled_soft_running_parent_accepts_failed_resident_reconciliation() {
        let (root, rt, state, mut status) = fixture();
        status.observations[0]["state"]["grain"]["status"] = json!("2");
        assert!(planned(&state, &status).is_ok());
        status.active.push("owned_worker");
        assert!(planned(&state, &status).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn pending_future_session_load_does_not_block_failed_only_reconciliation() {
        let (root, rt, state, mut status) = fixture();
        status
            .resume_evidence_required
            .push("retained session requires fresh session/load".into());
        assert!(planned(&state, &status).is_ok());
        status
            .session_integrity_errors
            .push("fingerprint changed".into());
        assert!(planned(&state, &status).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn audited_commit_preserves_prior_state_and_never_marks_success_or_replays() {
        let (root, rt, state, status) = fixture();
        let dir = rt.config.state_dir.join("resident");
        private_directory(&dir).unwrap();
        write_new(&dir.join("resident.lock"), b"").unwrap();
        let before = serde_json::to_vec(&state).unwrap();
        write_new(&dir.join("resident.json"), &before).unwrap();
        let guard = ResidentGuard::acquire(&rt.config, Some(&dir)).unwrap();
        let plan = plan(&before, &sha256_bytes(&before).unwrap(), &status).unwrap();
        let result = commit(
            &guard,
            &plan,
            &status,
            &serde_json::to_vec(&rt.journal).unwrap(),
            99,
        )
        .unwrap();
        assert!(
            ResidentGuard::acquire(&rt.config, Some(&dir)).is_err(),
            "lock survives the commit"
        );
        let after: Value =
            serde_json::from_slice(&fs::read(dir.join("resident.json")).unwrap()).unwrap();
        assert!(after["pending"].is_null());
        assert_eq!(after["completed"], state["completed"]);
        assert_eq!(after["lastInput"], state["lastInput"]);
        assert_eq!(after["lastCompletion"], state["lastCompletion"]);
        let archive = Path::new(result["archive"].as_str().unwrap());
        assert_eq!(
            fs::read(archive.join("resident-before.json")).unwrap(),
            before
        );
        assert!(archive.join("controller-before.json").exists());
        assert!(archive.join("decision.json").exists());
        assert_eq!(result["promptReplayed"], false);
        drop(guard);
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn archive_refusal_and_changed_state_leave_pending_untouched() {
        let (root, rt, state, status) = fixture();
        let dir = rt.config.state_dir.join("resident");
        private_directory(&dir).unwrap();
        write_new(&dir.join("resident.lock"), b"").unwrap();
        let bytes = serde_json::to_vec(&state).unwrap();
        write_new(&dir.join("resident.json"), &bytes).unwrap();
        let guard = ResidentGuard::acquire(&rt.config, Some(&dir)).unwrap();
        let plan = planned(&state, &status).unwrap();
        write_new(&dir.join("failed-reconciliations"), b"wrong file type").unwrap();
        assert!(commit(
            &guard,
            &plan,
            &status,
            &serde_json::to_vec(&rt.journal).unwrap(),
            99
        )
        .is_err());
        assert_eq!(fs::read(dir.join("resident.json")).unwrap(), bytes);
        fs::write(dir.join("resident.json"), b"changed").unwrap();
        assert!(guard.assert_unchanged().is_err());
        drop(guard);
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
}
