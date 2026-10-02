//! Immutable supersession of historical, unsupported completion claims. The
//! original resident counter, input and frame are never rewritten. Consumers
//! derive a qualified count from source-validated, ordinal-bound corrections.
use crate::quiescence::ResidentGuard;
use crate::*;
const FORMAT: &str = "mini-hermes-completion-supersession-v1";
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Pin {
    path: PathBuf,
    sha256: String,
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ForensicPairing {
    #[serde(rename = "type")]
    kind: String,
    historical_operation_id: u64,
    session_id: String,
    completed_ordinal: u64,
    completion_sha256: String,
    assertion: String,
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    #[serde(rename = "type")]
    kind: String,
    resident_state: PathBuf,
    expected_resident_sha256: String,
    expected_binding_sha256: String,
    historical_resident: Pin,
    historical_controller: Pin,
    forensic_pairing: ForensicPairing,
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Selection {
    protocol: String,
    resident_state: PathBuf,
    completed_ordinal: u64,
    completion_sha256: String,
    decision: Pin,
}
fn digest(bytes: &[u8]) -> Result<String> {
    sha256_bytes(bytes)
}
fn canonical(value: &impl Serialize) -> Result<String> {
    let v = serde_json::to_value(value).map_err(|e| e.to_string())?;
    digest(&serde_json::to_vec(&v).map_err(|e| e.to_string())?)
}
fn private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let m = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !m.is_file()
        || m.uid() != unsafe { libc::geteuid() }
        || m.mode() & 0o077 != 0
        || m.nlink() != 1
    {
        return Err("completion correction custody refused".into());
    }
    bounded_regular_file(path, limit)
}
fn pinned(pin: &Pin) -> Result<Vec<u8>> {
    let b = private(&pin.path, 32 * 1024 * 1024)?;
    if digest(&b)? != pin.sha256 {
        return Err("historical completion evidence hash changed".into());
    }
    Ok(b)
}
fn directory(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(m) if m.is_dir() && m.uid() == unsafe { libc::geteuid() } && m.mode() & 0o077 == 0 => {
            Ok(())
        }
        Ok(_) => Err("completion correction directory custody refused".into()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            let mut b = fs::DirBuilder::new();
            b.mode(0o700);
            b.create(path).map_err(|e| e.to_string())?;
            sync(path.parent().ok_or("correction parent absent")?)
        }
        Err(e) => Err(e.to_string()),
    }
}
fn sync(path: &Path) -> Result<()> {
    File::open(path)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())
}
fn selection_path(root: &Path, ordinal: u64) -> PathBuf {
    root.join("outcome-corrections")
        .join(format!("completed-{ordinal:016}.json"))
}

pub(crate) fn qualified_count(root: &Path, recorded: u64) -> Result<u64> {
    let dir = root.join("outcome-corrections");
    let m = match fs::symlink_metadata(&dir) {
        Ok(metadata) => metadata,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(recorded),
        Err(error) => return Err(error.to_string()),
    };
    if !m.is_dir() || m.uid() != unsafe { libc::geteuid() } || m.mode() & 0o077 != 0 {
        return Err("completion correction ledger custody refused".into());
    }
    let mut seen = std::collections::BTreeSet::new();
    for entry in fs::read_dir(&dir).map_err(|e| e.to_string())? {
        if seen.len() >= 1024 {
            return Err("completion correction ledger exceeds source bound".into());
        }
        let path = entry.map_err(|e| e.to_string())?.path();
        let row: Selection =
            serde_json::from_slice(&private(&path, 65536)?).map_err(|e| e.to_string())?;
        if row.protocol != FORMAT
            || row.resident_state != root
            || row.completed_ordinal == 0
            || row.completed_ordinal > recorded
            || path != selection_path(root, row.completed_ordinal)
            || !seen.insert(row.completed_ordinal)
        {
            return Err("completion correction ordinal/identity refused".into());
        }
        let decision: Value =
            serde_json::from_slice(&pinned(&row.decision)?).map_err(|e| e.to_string())?;
        let archive = row
            .decision
            .path
            .parent()
            .ok_or("correction archive absent")?;
        if archive.parent() != Some(root.join("outcome-reviews").as_path())
            || row.decision.path.file_name().and_then(|s| s.to_str()) != Some("decision.json")
            || decision["type"] != FORMAT
            || decision["residentState"] != json!(root)
            || decision["historicalCompletedOrdinal"] != row.completed_ordinal
            || decision["historicalCompletionSha256"] != row.completion_sha256
            || decision["supersedingOutcome"] != "unsupported-completion"
            || decision["recordedCounterUnchanged"] != true
            || decision["lastInputUnchanged"] != true
        {
            return Err("completion selection differs from immutable source decision".into());
        }
    }
    recorded
        .checked_sub(seen.len() as u64)
        .ok_or_else(|| "completion correction count underflow".into())
}
fn check_history(
    old: &Journal,
    resident: &Value,
    request: &Request,
    current: &Config,
    path: &Path,
) -> Result<()> {
    let pairing = &request.forensic_pairing;
    let cfg: Config =
        serde_json::from_value(old.binding["config"].clone()).map_err(|e| e.to_string())?;
    let mut prior = serde_json::to_value(&cfg).map_err(|e| e.to_string())?;
    let mut now = serde_json::to_value(current).map_err(|e| e.to_string())?;
    // These three operational settings cannot create grain/provider authority.
    // Different Host or authority histories require their own admitted lineage.
    for field in ["maxIterations", "contextWindowTokens", "maxRequestBytes"] {
        if let Some(obj) = prior["providerTask"].as_object_mut() {
            obj.remove(field);
        }
        if let Some(obj) = now["providerTask"].as_object_mut() {
            obj.remove(field);
        }
    }
    if prior != now || old.binding["configPath"] != json!(path) || cfg.provider_task.is_none() {
        return Err("historical completion belongs to a different managed profile lineage".into());
    }
    if old.provider_prompt_requests != 0
        || !old.provider_replays.is_empty()
        || !quiescence::retained(old, quiescence::ResidentEvidence::NotConfigured).is_empty()
    {
        return Err(
            "historical checkpoint is not the supported no-admitted-generation boundary".into(),
        );
    }
    let frame = &resident["lastCompletion"];
    if pairing.kind != "mini-hermes-historical-completion-pairing-v1"
        || pairing.historical_operation_id == 0
        || pairing.historical_operation_id >= old.next_operation_id
        || pairing.assertion.len() < 100
        || pairing.assertion.len() > 4096
        || pairing.completed_ordinal == 0
        || resident["completed"] != pairing.completed_ordinal
        || !resident["pending"].is_null()
        || resident["returnPending"] != false
        || !resident["lastInput"].is_string()
        || frame["type"] != "prompt-complete"
        || frame["v"] != 1
        || frame["outcome"] != "completed"
        || frame["reviewNeeded"] != false
        || canonical(frame)? != pairing.completion_sha256
        || !frame["residentOrigin"].is_null()
        || old.hermes_session.as_ref().map(|s| s.id.as_str()) != Some(pairing.session_id.as_str())
    {
        return Err(
            "historical completion pairing is not exact or needs source-origin classification"
                .into(),
        );
    }
    Ok(())
}
impl Runtime {
    pub(crate) fn supersede_unsupported_completion(&mut self, path: &Path) -> Result<Value> {
        let request_bytes = private(path, 65536)?;
        let request: Request = serde_json::from_slice(&request_bytes).map_err(|e| e.to_string())?;
        if request.kind != FORMAT
            || canonical(&self.journal.binding)? != request.expected_binding_sha256
        {
            return Err("completion supersession request binding changed".into());
        }
        let guard = ResidentGuard::acquire(&self.config, Some(&request.resident_state))?;
        if digest(guard.bytes()?)? != request.expected_resident_sha256 {
            return Err("current resident changed before completion review".into());
        }
        let current: Value = serde_json::from_slice(guard.bytes()?).map_err(|e| e.to_string())?;
        let recorded = current["completed"]
            .as_u64()
            .ok_or("resident count absent")?;
        let old_resident = pinned(&request.historical_resident)?;
        // Use the same strict source resident schema as the other receivers.
        let old_state = resident_reconcile::decode_resident_state(&old_resident)?;
        let old_value = serde_json::to_value(&old_state).map_err(|e| e.to_string())?;
        let old_controller = pinned(&request.historical_controller)?;
        let old: Journal = serde_json::from_slice(&old_controller).map_err(|e| e.to_string())?;
        check_history(&old, &old_value, &request, &self.config, &self.config_path)?;
        let ordinal = request.forensic_pairing.completed_ordinal;
        if ordinal > recorded {
            return Err("historical completion ordinal exceeds current preserved counter".into());
        }
        let before_count = qualified_count(&request.resident_state, recorded)?;
        let selected = selection_path(&request.resident_state, ordinal);
        if selected.try_exists().map_err(|e| e.to_string())? {
            return Err("this completion ordinal already has a retained supersession; inspect its immutable decision".into());
        }
        let id = self.next_id()?;
        let status = self.inspect_quiescence_locked(&guard)?;
        if !status.closed_checkpoint || !status.session_integrity_errors.is_empty() {
            return Err(
                "completion correction requires fresh closed native/process/session boundary"
                    .into(),
            );
        }
        guard.assert_unchanged()?;
        let reviews = request.resident_state.join("outcome-reviews");
        directory(&reviews)?;
        let archive = reviews.join(format!("review-{id:016}"));
        directory(&archive)?;
        for (name, bytes) in [
            ("request.json", request_bytes),
            ("resident-current.json", guard.bytes()?.to_vec()),
            ("resident-historical.json", old_resident),
            ("controller-historical.json", old_controller),
            (
                "controller-current.json",
                serde_json::to_vec_pretty(&self.journal).map_err(|e| e.to_string())?,
            ),
            (
                "quiescence.json",
                serde_json::to_vec_pretty(&status).map_err(|e| e.to_string())?,
            ),
        ] {
            write_new(&archive.join(name), &bytes)?;
        }
        let decision = json!({"type":FORMAT,"operationId":id,"residentState":request.resident_state,"historicalOperationId":request.forensic_pairing.historical_operation_id,
            "historicalCompletedOrdinal":ordinal,"historicalCompletionSha256":request.forensic_pairing.completion_sha256,
            "historicalResidentSha256":request.historical_resident.sha256,"historicalControllerSha256":request.historical_controller.sha256,
            "supersedingOutcome":"unsupported-completion","basis":"paired managed checkpoint has no admitted provider request or settled generation evidence",
            "identityBasis":"operator-forensic-pairing","forensicPairing":request.forensic_pairing,
            "recordedCompletions":recorded,"qualifiedCompletionsBefore":before_count,"qualifiedCompletionsAfter":before_count.checked_sub(1).ok_or("qualified count underflow")?,
            "recordedCounterUnchanged":true,"lastInputUnchanged":true,"completionFrameUnchanged":true,"promptReplayed":false,"archive":archive});
        let decision_bytes = serde_json::to_vec_pretty(&decision).map_err(|e| e.to_string())?;
        let decision_path = archive.join("decision.json");
        write_new(&decision_path, &decision_bytes)?;
        sync(&archive)?;
        guard.assert_unchanged()?;
        let ledger = request.resident_state.join("outcome-corrections");
        directory(&ledger)?;
        let selection = Selection {
            protocol: FORMAT.into(),
            resident_state: request.resident_state.clone(),
            completed_ordinal: ordinal,
            completion_sha256: decision["historicalCompletionSha256"]
                .as_str()
                .unwrap()
                .into(),
            decision: Pin {
                path: decision_path,
                sha256: digest(&decision_bytes)?,
            },
        };
        write_new(
            &selected,
            &serde_json::to_vec_pretty(&selection).map_err(|e| e.to_string())?,
        )?;
        sync(&ledger)?;
        if qualified_count(&request.resident_state, recorded)? != before_count - 1 {
            return Err("completion correction receiving count differs".into());
        }
        Ok(decision)
    }
}
pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let [socket, request] = args else {
        return Err("usage: grain-runtime resident-outcome ADMIN_SOCKET PRIVATE_REQUEST".into());
    };
    let response = control::admin_call(
        Path::new(socket),
        &format!(
            "resident supersede-completion {}",
            Path::new(request).to_str().ok_or("request path UTF-8")?
        ),
    )?;
    let result: Value = serde_json::from_str(&response).map_err(|_| response)?;
    if result["type"] != FORMAT {
        return Err("unexpected completion supersession response".into());
    }
    println!("{result}");
    Ok(())
}
#[cfg(test)]
mod tests {
    use super::*;
    fn fresh_root() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "resident-outcome-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        directory(&p).unwrap();
        p
    }
    fn install(root: &Path, ordinal: u64) -> PathBuf {
        let reviews = root.join("outcome-reviews");
        directory(&reviews).unwrap();
        let archive = reviews.join(format!("review-{ordinal}"));
        directory(&archive).unwrap();
        let decision = json!({"type":FORMAT,"residentState":root,"historicalCompletedOrdinal":ordinal,"historicalCompletionSha256":"a".repeat(64),"supersedingOutcome":"unsupported-completion","recordedCounterUnchanged":true,"lastInputUnchanged":true});
        let path = archive.join("decision.json");
        let bytes = serde_json::to_vec(&decision).unwrap();
        write_new(&path, &bytes).unwrap();
        directory(&root.join("outcome-corrections")).unwrap();
        let row = Selection {
            protocol: FORMAT.into(),
            resident_state: root.into(),
            completed_ordinal: ordinal,
            completion_sha256: "a".repeat(64),
            decision: Pin {
                path: path.clone(),
                sha256: digest(&bytes).unwrap(),
            },
        };
        write_new(
            &selection_path(root, ordinal),
            &serde_json::to_vec(&row).unwrap(),
        )
        .unwrap();
        path
    }
    #[test]
    fn qualified_count_supersedes_only_exact_recorded_ordinals() {
        let root = fresh_root();
        assert_eq!(qualified_count(&root, 3).unwrap(), 3);
        install(&root, 1);
        assert_eq!(qualified_count(&root, 3).unwrap(), 2);
        assert_eq!(qualified_count(&root, 1).unwrap(), 0);
        assert!(qualified_count(&root, 0).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn decision_tampering_or_moved_ordinal_never_increases_permission() {
        let root = fresh_root();
        let decision = install(&root, 1);
        fs::write(&decision, b"edited").unwrap();
        assert!(qualified_count(&root, 2).is_err());
        fs::remove_dir_all(root).unwrap();
        let root = fresh_root();
        install(&root, 1);
        fs::rename(selection_path(&root, 1), selection_path(&root, 2)).unwrap();
        assert!(qualified_count(&root, 2).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn repeated_selection_is_not_a_second_subtraction() {
        let root = fresh_root();
        install(&root, 1);
        let bytes = private(&selection_path(&root, 1), 65536).unwrap();
        write_new(&root.join("outcome-corrections/duplicate.json"), &bytes).unwrap();
        assert!(qualified_count(&root, 4).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn correction_leaves_historical_resident_bytes_and_input_exact() {
        let root = fresh_root();
        let bytes=br#"{"completed":1,"pending":null,"lastInput":"same-assignment","lastCompletion":{"outcome":"completed"},"returnPending":false,"returned":null}"#;
        write_new(&root.join("resident.json"), bytes).unwrap();
        install(&root, 1);
        assert_eq!(qualified_count(&root, 1).unwrap(), 0);
        assert_eq!(private(&root.join("resident.json"), 65536).unwrap(), bytes);
        let state: Value = serde_json::from_slice(bytes).unwrap();
        assert_eq!(state["lastInput"], "same-assignment");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn dangling_ledger_is_corruption_not_absence() {
        let root = fresh_root();
        std::os::unix::fs::symlink(root.join("missing"), root.join("outcome-corrections")).unwrap();
        assert!(qualified_count(&root, 1).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
