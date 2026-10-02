//! Retrospective closure of one source-confirmed failed ACP prompt. Native or
//! external uncertainty is never cleared; only its stranded session marker is
//! closed. The resident completion/count remains unchanged for its own receiver.
use crate::quiescence::{ResidentGuard, Status};
use crate::*;
const FORMAT: &str = "mini-hermes-session-failure-reconciliation-v1";
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    #[serde(rename = "type")]
    kind: String,
    resident_state: PathBuf,
    expected_resident_sha256: String,
    expected_binding_sha256: String,
    expected_session_sha256: String,
    expected_current_fingerprint: String,
    failure_evidence: PathBuf,
    failure_evidence_sha256: String,
    historical_runtime: PathBuf,
    legacy_forensic_admission: Option<LegacyAdmission>,
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct LegacyAdmission {
    #[serde(rename = "type")]
    kind: String,
    expected_journal_sha256: String,
    resident_pending_sha256: String,
    prompt_operation_id: u64,
    session_id: String,
    resident_prompt_id: String,
    assertion: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ObservedFailure {
    #[serde(rename = "type")]
    kind: String,
    prompt_operation_id: u64,
    session_id: String,
    controller_unit: String,
    controller_invocation_id: String,
    runtime_sha256: String,
    worker_record: Value,
    error_record: Value,
    error: Value,
    provider_request_sha256: String,
    resident_prompt_sha256: String,
}
fn digest(bytes: &[u8]) -> Result<String> {
    sha256_bytes(bytes)
}
fn hash<T: Serialize>(value: &T) -> Result<String> {
    let value = serde_json::to_value(value).map_err(|e| e.to_string())?;
    digest(&serde_json::to_vec(&value).map_err(|e| e.to_string())?)
}
fn private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let m = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !m.is_file()
        || m.uid() != unsafe { libc::geteuid() }
        || m.mode() & 0o077 != 0
        || m.nlink() != 1
    {
        return Err("failed-session evidence must be an owned private regular file".into());
    }
    bounded_regular_file(path, limit)
}
fn directory(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(m) if m.is_dir() && m.uid() == unsafe { libc::geteuid() } && m.mode() & 0o077 == 0 => {
            Ok(())
        }
        Ok(_) => Err("failed-session archive custody refused".into()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            let mut b = fs::DirBuilder::new();
            b.mode(0o700);
            b.create(path).map_err(|e| e.to_string())?;
            File::open(path.parent().ok_or("archive parent")?)
                .and_then(|f| f.sync_all())
                .map_err(|e| e.to_string())
        }
        Err(e) => Err(e.to_string()),
    }
}
fn checked_bytes(path: &Path, bytes: usize, expected: &str, limit: usize) -> Result<Vec<u8>> {
    let value = private(path, limit)?;
    if value.len() != bytes || digest(&value)? != expected {
        return Err("retained provider artifact bytes/hash changed".into());
    }
    Ok(value)
}
fn journal_records(invocation: &str) -> Result<Vec<Value>> {
    if invocation.len() != 32 || !invocation.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("controller invocation identity malformed".into());
    }
    let mut child = Command::new("/usr/bin/journalctl")
        .args([
            "--user",
            "--no-pager",
            "--quiet",
            "--output=json",
            &format!("_SYSTEMD_INVOCATION_ID={invocation}"),
        ])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .map_err(|e| e.to_string())?;
    let mut bytes = Vec::new();
    let read = child
        .stdout
        .take()
        .ok_or("trusted journal stdout absent")?
        .take(1_048_577)
        .read_to_end(&mut bytes);
    if read.is_err() || bytes.len() > 1_048_576 {
        let _ = child.kill();
        let _ = child.wait();
        return Err("complete trusted invocation journal unavailable or over bound".into());
    }
    if !child.wait().map_err(|e| e.to_string())?.success() {
        return Err("trusted failed invocation journal refused".into());
    }
    let text = String::from_utf8(bytes).map_err(|e| e.to_string())?;
    text.lines()
        .filter(|l| !l.is_empty())
        .map(|l| serde_json::from_str(l).map_err(|e| e.to_string()))
        .collect()
}
fn authenticate_failure(
    f: &ObservedFailure,
    task: &str,
    config_path: &Path,
    records: &[Value],
) -> Result<()> {
    if f.kind != "mini-hermes-observed-acp-failure-v1"
        || f.prompt_operation_id == 0
        || f.controller_unit != format!("mini-grain-controller@{task}.service")
        || hermes_outcome::typed_failure(&f.error).is_none()
    {
        return Err("failure envelope type/task/typed outcome refused".into());
    }
    let expected_worker = format!(
        "Running as unit: mini-grain-t{task}-o{}.service; invocation ID: ",
        f.prompt_operation_id
    );
    let expected_exec = format!(" serve {}", config_path.display());
    for record in [&f.worker_record, &f.error_record] {
        if record["_SYSTEMD_INVOCATION_ID"] != f.controller_invocation_id
            || record["_SYSTEMD_USER_UNIT"] != f.controller_unit
            || record["_UID"] != unsafe { libc::geteuid() }.to_string()
            || records.iter().filter(|actual| *actual == record).count() != 1
        {
            return Err(
                "retained failure record is not exact trusted invocation journal evidence".into(),
            );
        }
    }
    if f.worker_record["_EXE"] != "/usr/bin/systemd-run"
        || !f.worker_record["MESSAGE"]
            .as_str()
            .is_some_and(|s| s.starts_with(&expected_worker))
        || !f.error_record["_EXE"]
            .as_str()
            .is_some_and(|s| s.ends_with("/grain-runtime"))
        || !f.error_record["_CMDLINE"]
            .as_str()
            .is_some_and(|s| s.ends_with(&expected_exec))
    {
        return Err("trusted records do not name exact controller and prompt worker".into());
    }
    let worker_time = f.worker_record["__MONOTONIC_TIMESTAMP"]
        .as_str()
        .and_then(|v| v.parse::<u64>().ok())
        .ok_or("worker time absent")?;
    let error_time = f.error_record["__MONOTONIC_TIMESTAMP"]
        .as_str()
        .and_then(|v| v.parse::<u64>().ok())
        .ok_or("error time absent")?;
    if worker_time >= error_time || f.worker_record["_BOOT_ID"] != f.error_record["_BOOT_ID"] {
        return Err("failed worker/error ordering differs".into());
    }
    // A single scoped worker in the retained invocation removes a recycled
    // attachment/request-counter ambiguity. More complex histories need their
    // own durable per-prompt failure record, not this retrospective receiver.
    if records
        .iter()
        .filter(|v| {
            v["_EXE"] == "/usr/bin/systemd-run"
                && v["MESSAGE"]
                    .as_str()
                    .is_some_and(|s| s.starts_with("Running as unit: mini-grain-"))
        })
        .count()
        != 1
    {
        return Err("retrospective invocation contains multiple prompt workers".into());
    }
    let message = f.error_record["MESSAGE"]
        .as_str()
        .ok_or("typed failure message absent")?;
    let body = message
        .strip_prefix("grain-runtime: Hermes ACP outcome uncertain: Hermes ACP: ")
        .and_then(|s| s.strip_suffix("))); Mini/tool/provider fence=Ok(())"))
        .ok_or("legacy typed failure lacks exact confirmed local stop/fence record")?;
    let (raw, stop) = body
        .rsplit_once("; local stop=Ok(ExitStatus(unix_wait_status(")
        .ok_or("confirmed wait outcome absent")?;
    stop.parse::<u32>()
        .map_err(|_| "confirmed wait status malformed")?;
    let error: Value =
        serde_json::from_str(raw).map_err(|e| format!("typed failure payload: {e}"))?;
    if error != f.error {
        return Err("parsed typed failure differs from trusted source record".into());
    }
    Ok(())
}
fn request_prompt(request: &Value) -> Result<&str> {
    let last = request["messages"]
        .as_array()
        .ok_or("provider messages absent")?
        .iter()
        .rev()
        .find(|m| m["role"] == "user")
        .ok_or("provider request has no user prompt")?;
    last["content"]
        .as_str()
        .ok_or_else(|| "retrospective binding requires exact text user prompt".into())
}
fn boundary(status: &Status) -> Result<()> {
    if !status.can_restart_retaining_state
        || !status.active.is_empty()
        || !status.evidence_required.is_empty()
        || !status.exact_recovery.is_empty()
        || status.retained != ["hermes_pending_prompt", "resident_pending_prompt"]
        || status.observations.is_empty()
        || !status
            .observations
            .iter()
            .all(|o| quiescence::signed_unreserved_boundary(&o["state"]))
        || status
            .session_integrity_errors
            .iter()
            .any(|e| e != "retained session fingerprint is missing or changed")
    {
        return Err("failed-session closure requires only its two stranded prompt markers and fresh signed/process closure".into());
    }
    Ok(())
}
fn planned_session(j: &Journal, f: &ObservedFailure, r: &Request) -> Result<Journal> {
    let old = j.hermes_session.as_ref().ok_or("retained session absent")?;
    if old.id != f.session_id
        || !old.pending_prompt
        || old.retention_issue.is_some()
        || old.state_fingerprint.is_none()
        || hash(old)? != r.expected_session_sha256
    {
        return Err(
            "exact failed retained session changed or has other retention uncertainty".into(),
        );
    }
    let mut after = j.clone();
    let session = after.hermes_session.as_mut().unwrap();
    session.pending_prompt = false;
    session.state_fingerprint = Some(r.expected_current_fingerprint.clone());
    session.load_verified = false;
    Ok(after)
}
static PUBLICATION_UNCERTAIN: AtomicBool = AtomicBool::new(false);
pub(crate) fn ensure_publication_known(state: &Path) -> Result<()> {
    if PUBLICATION_UNCERTAIN.load(Ordering::SeqCst)
        || state
            .join("failed-session-publication-uncertain.json")
            .try_exists()
            .map_err(|e| e.to_string())?
    {
        return Err(
            "failed-session publication needs exact retained recovery before further mutation"
                .into(),
        );
    }
    Ok(())
}
fn mark_publication_uncertain(state: &Path, archive: &Path) {
    PUBLICATION_UNCERTAIN.store(true, Ordering::SeqCst);
    let bytes = serde_json::to_vec_pretty(
        &json!({"type":"mini-hermes-session-publication-uncertain-v1","archive":archive}),
    )
    .unwrap();
    let _ = write_new(
        &state.join("failed-session-publication-uncertain.json"),
        &bytes,
    );
    let _ = File::open(state).and_then(|file| file.sync_all());
}
fn require_origin(
    journal: &Journal,
    pending: &Value,
    resident_bytes: &[u8],
    failure: &ObservedFailure,
    request: &Request,
) -> Result<()> {
    let resident: Value = serde_json::from_slice(resident_bytes).map_err(|e| e.to_string())?;
    let origin = &resident["lastCompletion"]["residentOrigin"];
    if !origin.is_null() {
        if request.legacy_forensic_admission.is_some() {
            return Err(
                "source-bound completion must not borrow a legacy operator assertion".into(),
            );
        }
        if serde_json::to_value(journal).map_err(|e| e.to_string())?["residentPromptOrigin"]
            != *origin
            || origin["residentPromptId"] != pending["residentPromptId"]
            || origin["promptSha256"] != pending["promptSha256"]
            || origin["promptOperationId"] != failure.prompt_operation_id
            || origin["sessionId"] != failure.session_id
        {
            return Err("source completion origin does not bind exact resident, prompt operation and session".into());
        }
        return Ok(());
    }
    let legacy=request.legacy_forensic_admission.as_ref().ok_or("historical wire has no source prompt-origin receipt; explicit state-pinned legacy forensic admission required")?;
    if legacy.kind != "mini-hermes-legacy-forensic-admission-v1"
        || legacy.expected_journal_sha256 != hash(journal)?
        || legacy.resident_pending_sha256 != hash(pending)?
        || legacy.prompt_operation_id != failure.prompt_operation_id
        || legacy.session_id != failure.session_id
        || Some(legacy.resident_prompt_id.as_str()) != pending["residentPromptId"].as_str()
        || legacy.assertion.len() < 100
        || legacy.assertion.len() > 4096
    {
        return Err(
            "legacy forensic assertion is not bound to this exact current journal/resident/session"
                .into(),
        );
    }
    Ok(())
}
impl Runtime {
    pub(crate) fn reconcile_session_failure(&mut self, path: &Path) -> Result<Value> {
        ensure_publication_known(&self.config.state_dir)?;
        let request_bytes = private(path, 65536)?;
        let r: Request = serde_json::from_slice(&request_bytes).map_err(|e| e.to_string())?;
        if r.kind != FORMAT || hash(&self.journal.binding)? != r.expected_binding_sha256 {
            return Err("failed-session request binding/type changed".into());
        }
        let failure_bytes = private(&r.failure_evidence, 65536)?;
        if digest(&failure_bytes)? != r.failure_evidence_sha256 {
            return Err("failure evidence hash changed".into());
        }
        let f: ObservedFailure =
            serde_json::from_slice(&failure_bytes).map_err(|e| e.to_string())?;
        let binary = bounded_regular_file(&r.historical_runtime, 256 * 1024 * 1024)?;
        if digest(&binary)? != f.runtime_sha256 {
            return Err("retained historical runtime image differs".into());
        }
        let guard = ResidentGuard::acquire(&self.config, Some(&r.resident_state))?;
        let pending =
            resident_reconcile::bound_failed_pending(guard.bytes()?, &r.expected_resident_sha256)?;
        if pending["promptSha256"] != f.resident_prompt_sha256 {
            return Err("failed envelope names another resident prompt".into());
        }
        planned_session(&self.journal, &f, &r)?;
        require_origin(&self.journal, &pending, guard.bytes()?, &f, &r)?;
        let records = journal_records(&f.controller_invocation_id)?;
        authenticate_failure(&f, &self.config.task, &self.config_path, &records)?;
        let matches: Vec<_> = self
            .journal
            .provider_replays
            .iter()
            .filter(|p| {
                p.prompt_operation_id == f.prompt_operation_id
                    && p.request_sha256 == f.provider_request_sha256
            })
            .collect();
        if matches.len() != 1 {
            return Err("failed prompt has no unique retained provider request".into());
        }
        let replay = matches[0];
        let request = checked_bytes(
            &replay.request_path,
            replay.request_bytes,
            &replay.request_sha256,
            1_048_576,
        )?;
        let response = checked_bytes(
            &replay.response_path,
            replay.response_bytes,
            &replay.response_sha256,
            8_388_608,
        )?;
        if replay.status != 200 || replay.metered_charge.is_none() {
            return Err("retrospective failure requires its earlier request be definitely metered and settled".into());
        }
        let meter = private(
            replay
                .meter_report_path
                .as_deref()
                .ok_or("meter report absent")?,
            1_048_576,
        )?;
        if Some(digest(&meter)?.as_str()) != replay.meter_report_sha256.as_deref() {
            return Err("meter report digest changed".into());
        }
        let value: Value = serde_json::from_slice(&request).map_err(|e| e.to_string())?;
        if digest(request_prompt(&value)?.as_bytes())? != f.resident_prompt_sha256 {
            return Err("settled provider request does not bind resident pending text".into());
        }
        let home = self
            .journal
            .hermes_session
            .as_ref()
            .unwrap()
            .workspace
            .join(".hermes");
        self.quiescence_stop_proof()?;
        if hermes_state_fingerprint(&home)?.as_deref()
            != Some(r.expected_current_fingerprint.as_str())
        {
            return Err("current session fingerprint changed".into());
        }
        let id = self.next_id()?;
        let status = self.inspect_quiescence_locked(&guard)?;
        boundary(&status)?;
        guard.assert_unchanged()?;
        let after = planned_session(&self.journal, &f, &r)?;
        let root = self.config.state_dir.join("failed-session-reconciliations");
        directory(&root)?;
        let archive = root.join(format!(
            "prompt-{:016}-decision-{id:016}",
            f.prompt_operation_id
        ));
        directory(&archive)?;
        let old_bytes = serde_json::to_vec_pretty(&self.journal).map_err(|e| e.to_string())?;
        let after_bytes = serde_json::to_vec_pretty(&after).map_err(|e| e.to_string())?;
        for (name, bytes) in [
            ("request.json", request_bytes),
            ("failure.json", failure_bytes),
            ("resident-before.json", guard.bytes()?.to_vec()),
            ("controller-before.json", old_bytes),
            ("controller-after.json", after_bytes.clone()),
            ("provider-request.json", request),
            ("provider-response.bin", response),
            ("meter.json", meter),
            (
                "quiescence.json",
                serde_json::to_vec_pretty(&status).map_err(|e| e.to_string())?,
            ),
            (
                "trusted-invocation.json",
                serde_json::to_vec_pretty(&records).map_err(|e| e.to_string())?,
            ),
        ] {
            write_new(&archive.join(name), &bytes)?;
        }
        let copied_home = archive.join("session-state");
        directory(&copied_home)?;
        for name in ["state.db", "state.db-wal"] {
            let p = home.join(name);
            if p.try_exists().map_err(|e| e.to_string())? {
                write_new(&copied_home.join(name), &private(&p, 536_870_912)?)?;
            }
        }
        File::open(&copied_home)
            .and_then(|file| file.sync_all())
            .map_err(|e| e.to_string())?;
        if hermes_state_fingerprint(&home)?.as_deref()
            != Some(r.expected_current_fingerprint.as_str())
            || hermes_state_fingerprint(&copied_home)?.as_deref()
                != Some(r.expected_current_fingerprint.as_str())
        {
            return Err("session fingerprint changed during immutable archive".into());
        }
        self.quiescence_stop_proof()?;
        guard.assert_unchanged()?;
        let decision = json!({"type":FORMAT,"operationId":id,"promptOperationId":f.prompt_operation_id,"sessionId":f.session_id,
            "failureEvidenceSha256":r.failure_evidence_sha256,"residentSha256":r.expected_resident_sha256,
            "identityBasis":if r.legacy_forensic_admission.is_some(){"operator-forensic-assertion"}else{"source-prompt-origin"},
            "legacyForensicAdmission":r.legacy_forensic_admission,
            "controllerBeforeSha256":hash(&self.journal)?,"controllerAfterSha256":hash(&after)?,"currentFingerprint":r.expected_current_fingerprint,
            "supersedingOutcome":"failed","sessionLoadRequired":true,"residentPendingPreserved":true,"completedCountUnchanged":true,"promptReplayed":false,"archive":archive});
        write_new(
            &archive.join("decision.json"),
            &serde_json::to_vec_pretty(&decision).map_err(|e| e.to_string())?,
        )?;
        File::open(&archive)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
        // This single journal publication changes only three session fields.
        // A failed write keeps the in-memory state unchanged and the full plan.
        let publication = atomic_json(&self.config.state_dir.join("journal.json"), &after);
        if let Err(error) = publication {
            match private(
                &self.config.state_dir.join("journal.json"),
                32 * 1024 * 1024,
            ) {
                Ok(current) if current == after_bytes => {
                    self.journal = after;
                    return Err(format!("failed-session closure published; durability acknowledgement failed; inspect {}: {error}",archive.display()));
                }
                Ok(current)
                    if serde_json::from_slice::<Journal>(&current)
                        .ok()
                        .as_ref()
                        .is_some_and(|j| {
                            hash(j)
                                .ok()
                                .zip(hash(&self.journal).ok())
                                .is_some_and(|(a, b)| a == b)
                        }) =>
                {
                    return Err(error)
                }
                _ => {
                    mark_publication_uncertain(&self.config.state_dir, &archive);
                    return Err(format!("failed-session journal publication state is unknown; further mutation frozen: {error}"));
                }
            }
        }
        self.journal = after;
        write_new(
            &archive.join("committed.json"),
            &serde_json::to_vec_pretty(&decision).map_err(|e| e.to_string())?,
        )?;
        Ok(decision)
    }
}
pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let [socket, request] = args else {
        return Err("usage: grain-runtime session-failure ADMIN_SOCKET PRIVATE_REQUEST".into());
    };
    let response = control::admin_call(
        Path::new(socket),
        &format!(
            "session reconcile-failure {}",
            Path::new(request).to_str().ok_or("request path UTF-8")?
        ),
    )?;
    let result: Value = serde_json::from_str(&response).map_err(|_| response)?;
    if result["type"] != FORMAT {
        return Err("unexpected failed-session response".into());
    }
    println!("{result}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn failure() -> ObservedFailure {
        let error = json!({"code":-32003,"data":{"type":"mini-hermes-turn-failure-v1","reason":"format_error","detail":"HTTP400 bounded request","retryable":false}});
        let invocation = "a".repeat(32);
        let unit = "mini-grain-controller@8781.service";
        let mut worker = json!({"_SYSTEMD_INVOCATION_ID":invocation,"_SYSTEMD_USER_UNIT":unit,"_UID":unsafe{libc::geteuid()}.to_string(),"_EXE":"/usr/bin/systemd-run","__MONOTONIC_TIMESTAMP":"10","_BOOT_ID":"boot","MESSAGE":"Running as unit: mini-grain-t8781-o94.service; invocation ID: worker"});
        worker["__CURSOR"] = json!("worker-cursor");
        let mut failed = worker.clone();
        failed["_EXE"] = json!("/owned/grain-runtime");
        failed["__MONOTONIC_TIMESTAMP"] = json!("20");
        failed["__CURSOR"] = json!("error-cursor");
        failed["_CMDLINE"] = json!("/owned/grain-runtime serve /owned/controller.json");
        failed["MESSAGE"]=json!(format!("grain-runtime: Hermes ACP outcome uncertain: Hermes ACP: {error}; local stop=Ok(ExitStatus(unix_wait_status(36608))); Mini/tool/provider fence=Ok(())"));
        ObservedFailure {
            kind: "mini-hermes-observed-acp-failure-v1".into(),
            prompt_operation_id: 94,
            session_id: "session94".into(),
            controller_unit: unit.into(),
            controller_invocation_id: invocation,
            runtime_sha256: "a".repeat(64),
            worker_record: worker,
            error_record: failed,
            error,
            provider_request_sha256: "b".repeat(64),
            resident_prompt_sha256: "c".repeat(64),
        }
    }
    #[test]
    fn retained_error_must_match_trusted_invocation_and_exact_worker() {
        let mut f = failure();
        let records = vec![f.worker_record.clone(), f.error_record.clone()];
        authenticate_failure(&f, "8781", Path::new("/owned/controller.json"), &records).unwrap();
        f.prompt_operation_id = 95;
        assert!(
            authenticate_failure(&f, "8781", Path::new("/owned/controller.json"), &records)
                .is_err()
        );
        let mut f = failure();
        f.error["data"]["detail"] = json!("edited note");
        assert!(
            authenticate_failure(&f, "8781", Path::new("/owned/controller.json"), &records)
                .is_err()
        );
    }
    #[test]
    fn stopped_fence_and_unique_prompt_are_required_not_inferred() {
        let mut f = failure();
        f.error_record["MESSAGE"] = json!("grain-runtime: unstructured error");
        let records = vec![f.worker_record.clone(), f.error_record.clone()];
        assert!(
            authenticate_failure(&f, "8781", Path::new("/owned/controller.json"), &records)
                .is_err()
        );
        let f = failure();
        let mut other = f.worker_record.clone();
        other["MESSAGE"] =
            json!("Running as unit: mini-grain-t8781-o99.service; invocation ID: another");
        let records = vec![f.worker_record.clone(), f.error_record.clone(), other];
        assert!(
            authenticate_failure(&f, "8781", Path::new("/owned/controller.json"), &records)
                .is_err()
        );
    }
    #[test]
    fn last_user_text_is_exact_not_any_matching_historical_prompt() {
        let request = json!({"messages":[{"role":"user","content":"old"},{"role":"assistant","content":"answer"},{"role":"user","content":"current"},{"role":"tool","content":"result"}]});
        assert_eq!(request_prompt(&request).unwrap(), "current");
        assert!(request_prompt(
            &json!({"messages":[{"role":"user","content":[{"text":"ambiguous"}]}]})
        )
        .is_err());
    }
    #[test]
    fn closure_changes_only_source_proven_session_fields_and_requires_load() {
        let (root, rt) = crate::tests::restart_resolution_fixture("session-failure-plan");
        let mut j = rt.journal.clone();
        j.hermes_session = Some(HermesSession {
            id: "session94".into(),
            workspace: root.join("worker"),
            load_verified: true,
            state_fingerprint: Some("old".into()),
            retention_issue: None,
            pending_prompt: true,
        });
        let r = Request {
            kind: FORMAT.into(),
            resident_state: root.join("resident"),
            expected_resident_sha256: "a".repeat(64),
            expected_binding_sha256: hash(&j.binding).unwrap(),
            expected_session_sha256: hash(j.hermes_session.as_ref().unwrap()).unwrap(),
            expected_current_fingerprint: "current".into(),
            failure_evidence: root.join("failure"),
            failure_evidence_sha256: "b".repeat(64),
            historical_runtime: root.join("runtime"),
            legacy_forensic_admission: None,
        };
        let after = planned_session(&j, &failure(), &r).unwrap();
        let mut expected = serde_json::to_value(&j).unwrap();
        expected["hermesSession"]["pendingPrompt"] = json!(false);
        expected["hermesSession"]["loadVerified"] = json!(false);
        expected["hermesSession"]["stateFingerprint"] = json!("current");
        assert_eq!(serde_json::to_value(&after).unwrap(), expected);
        j.hermes_session.as_mut().unwrap().retention_issue = Some("other uncertainty".into());
        assert!(planned_session(&j, &failure(), &r).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn fresh_boundary_never_clears_other_native_or_external_uncertainty() {
        let (root, rt) = crate::tests::restart_resolution_fixture("session-failure-boundary");
        let mut s = rt.quiescence_status().unwrap();
        s.can_restart_retaining_state = true;
        s.active.clear();
        s.evidence_required.clear();
        s.exact_recovery.clear();
        s.retained = vec!["hermes_pending_prompt", "resident_pending_prompt"];
        s.session_integrity_errors =
            vec!["retained session fingerprint is missing or changed".into()];
        s.observations = vec![json!({"state":{"grain":{"status":"2","reserved":"0"}}})];
        boundary(&s).unwrap();
        s.retained.push("provider_attempt");
        assert!(boundary(&s).is_err());
        s.retained.pop();
        s.observations[0]["state"]["grain"]["reserved"] = json!("1");
        assert!(boundary(&s).is_err());
        drop(rt);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn legacy_identity_is_explicit_and_state_pinned_never_inferred_from_same_text() {
        let j = Journal::fresh(json!({"config":"exact"}));
        let f = failure();
        let pending =
            json!({"residentPromptId":"d".repeat(64),"promptSha256":f.resident_prompt_sha256});
        let resident = serde_json::to_vec(&json!({"lastCompletion":{},"pending":pending})).unwrap();
        let mut r = Request {
            kind: FORMAT.into(),
            resident_state: "/private/resident".into(),
            expected_resident_sha256: "a".repeat(64),
            expected_binding_sha256: hash(&j.binding).unwrap(),
            expected_session_sha256: "b".repeat(64),
            expected_current_fingerprint: "current".into(),
            failure_evidence: "/private/failure".into(),
            failure_evidence_sha256: "c".repeat(64),
            historical_runtime: "/private/runtime".into(),
            legacy_forensic_admission: None,
        };
        assert!(require_origin(&j, &pending, &resident, &f, &r).is_err());
        r.legacy_forensic_admission=Some(LegacyAdmission{kind:"mini-hermes-legacy-forensic-admission-v1".into(),expected_journal_sha256:hash(&j).unwrap(),resident_pending_sha256:hash(&pending).unwrap(),prompt_operation_id:94,session_id:f.session_id.clone(),resident_prompt_id:"d".repeat(64),assertion:"The historical wire lacked a prompt ID. This is an explicit operator forensic assertion about these exact retained bytes, not a source-generated causal receipt.".into()});
        require_origin(&j, &pending, &resident, &f, &r).unwrap();
        let mut repeated = pending.clone();
        repeated["residentPromptId"] = json!("e".repeat(64));
        assert!(require_origin(&j, &repeated, &resident, &f, &r).is_err());
        let mut changed = j.clone();
        changed.next_operation_id += 1;
        assert!(require_origin(&changed, &pending, &resident, &f, &r).is_err());
    }
}
