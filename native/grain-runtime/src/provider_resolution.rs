//! Read-only Mini resolution of an exact guarded settlement. Native proofs own
//! history and command semantics; this boundary binds their report to this
//! controller's immutable Pending/source/hold and never releases provider funds.
use super::*;

const MAX: usize = 48_411_040;
const BASIC: &[&str] = &["attempt.json", "config.json", "intent.json", "call.bin"];
const GUARDED: &[&str] = &[
    "original-plan.bin",
    "original-plan.json",
    "plan.bin",
    "plan.json",
    "transaction-signatures.bin",
    "transaction-signatures.json",
    "outcome.bin",
    "outcome.json",
    "provider-continuity/descriptor.json",
    "provider-continuity/request.bin",
    "provider-continuity/reply.frame",
    "provider-continuity/continuity.json",
    "provider-continuity/reserve-call.bin",
    "provider-continuity/reserve-outcome.bin",
];

pub(super) enum Resolution {
    NotApplicable,
    Confirmed(PathBuf),
    Retired,
}

fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("provider resolution {key} absent"))
}
fn read(path: &Path) -> Result<Vec<u8>> {
    let stat = fs::symlink_metadata(path)
        .map_err(|e| format!("provider resolution {}: {e}", path.display()))?;
    if !stat.is_file() || stat.uid() != unsafe { libc::geteuid() } || stat.mode() & 0o077 != 0 {
        return Err("provider resolution evidence must be owned private regular data".into());
    }
    let opened = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)
        .map_err(|e| e.to_string())?;
    let after = opened.metadata().map_err(|e| e.to_string())?;
    if (stat.dev(), stat.ino()) != (after.dev(), after.ino())
        || !after.is_file()
        || after.len() > MAX as u64
    {
        return Err("provider resolution evidence changed while opening".into());
    }
    let mut bytes = Vec::new();
    opened
        .take((MAX + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() > MAX {
        return Err("provider resolution evidence grew beyond bound".into());
    }
    Ok(bytes)
}
fn json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&read(path)?).map_err(|e| format!("provider resolution JSON: {e}"))
}
fn copied_input(
    report: &Value,
    pending: &Pending,
    directory: &Path,
    name: &str,
) -> Result<Vec<u8>> {
    let item = report
        .get("inputs")
        .and_then(|v| v.get(name))
        .ok_or("provider resolution input absent")?;
    let original = pending.attempt.join(name);
    let retained = directory.join("retained").join(name);
    if Path::new(string(item, "path")?) != original
        || Path::new(string(item, "retainedPath")?) != retained
    {
        return Err("provider resolution input escaped its exact attempt/proof directory".into());
    }
    let bytes = read(&original)?;
    if read(&retained)? != bytes || sha256_bytes(&bytes)? != string(item, "sha256")? {
        return Err("provider resolution input changed from retained evidence".into());
    }
    Ok(bytes)
}
fn artifact(item: &Value, directory: &Path) -> Result<PathBuf> {
    let path = PathBuf::from(string(item, "path")?);
    // The client emits evidence in this new directory, never arbitrary external
    // receipts. Refuse dot components even when their lexical prefix matches.
    let relative = path
        .strip_prefix(directory)
        .map_err(|_| "provider resolution artifact escaped proof directory")?;
    if relative
        .components()
        .any(|c| !matches!(c, std::path::Component::Normal(_)))
        || relative.as_os_str().is_empty()
    {
        return Err("provider resolution artifact path is not canonical".into());
    }
    if sha256_bytes(&read(&path)?)? != string(item, "sha256")? {
        return Err("provider resolution artifact digest changed".into());
    }
    Ok(path)
}
fn number(value: &Value, key: &str) -> Result<u128> {
    let text = string(value, key)?;
    if text.is_empty()
        || (text.len() > 1 && text.starts_with('0'))
        || !text.bytes().all(|b| b.is_ascii_digit())
    {
        return Err("provider resolution integer is not canonical".into());
    }
    text.parse()
        .map_err(|_| "provider resolution integer exceeds consumer bound".into())
}
fn expiration(report: &Value) -> Result<()> {
    let e = report
        .get("expiration")
        .ok_or("provider resolution expiration absent")?;
    let original = report
        .get("originalPrefix")
        .ok_or("provider resolution original prefix absent")?;
    let fresh = report
        .get("freshPrefix")
        .ok_or("provider resolution current prefix absent")?;
    let g = number(e, "genesisHeight")?;
    let old = number(e, "originalAcceptedCount")?;
    let count = number(e, "checkedAcceptedCount")?;
    let height = number(e, "checkedHeight")?;
    if old == 0
        || old >= count
        || g.checked_add(count) != Some(height)
        || number(original, "checkedAcceptedCount")? != old
        || number(fresh, "checkedAcceptedCount")? != count
        || fresh.get("priorChecked")
            != Some(
                &json!({"acceptedCount":old.to_string(),"worldRoot":string(original,"checkedWorldRoot")?}),
            )
    {
        return Err("provider resolution lacks the exact original observed prefix".into());
    }
    let deadlines = e
        .get("signedDeadlines")
        .and_then(Value::as_array)
        .ok_or("provider resolution signed deadlines absent")?;
    if deadlines.is_empty() || deadlines.len() > 64 {
        return Err("provider resolution deadline count outside bound".into());
    }
    for deadline in deadlines {
        let d = number(&json!({"deadline":deadline}), "deadline")?;
        if d >= height {
            return Err("provider settlement is not strictly expired".into());
        }
    }
    Ok(())
}

fn inspect(
    config: &Config,
    pending: &Pending,
    directory: &Path,
    descriptor: &Value,
) -> Result<(bool, PathBuf, Value)> {
    if pending.publication.is_some()
        || pending.attempt
            != config
                .state_dir
                .join(format!("attempt-{:016}", pending.operation_id))
    {
        return Err("provider resolution is not the exact controller Pending".into());
    }
    let report = json(&directory.join("resolution.json"))?;
    if report["type"] != "mini-provider-continuity-resolution-v1"
        || report["heldAllowanceReleased"] != false
        || report["providerRequestRepeated"] != false
        || Path::new(string(&report, "attempt")?) != pending.attempt
        || Path::new(string(&report, "host")?) != config.host
        || string(&report, "hostSha256")? != sha256_file(&config.host)?
        || Path::new(string(&report, "config")?) != config.host_config
        || string(&report, "configSha256")? != sha256_file(&config.host_config)?
        || Some(Path::new(string(&report, "socket")?)) != config.host_socket.as_deref()
    {
        return Err("provider resolution differs from pinned controller execution".into());
    }
    let inputs = report["inputs"]
        .as_object()
        .ok_or("provider resolution input map absent")?;
    if inputs.len() > 24 {
        return Err("provider resolution input map exceeds bound".into());
    }
    for name in inputs.keys() {
        if Path::new(name)
            .components()
            .any(|c| !matches!(c, std::path::Component::Normal(_)))
        {
            return Err("provider resolution input name is not canonical".into());
        }
        copied_input(&report, pending, directory, name)?;
    }
    for name in BASIC {
        copied_input(&report, pending, directory, name)?;
    }
    let source_bytes = copied_input(&report, pending, directory, "intent.json")?;
    if source_bytes
        != read(
            &config
                .state_dir
                .join(format!("source-{:016}.json", pending.operation_id)),
        )?
        || copied_input(&report, pending, directory, "config.json")?
            != bounded_regular_file(&config.host_config, 65_536)?
    {
        return Err("provider resolution differs from retained source/config".into());
    }
    let source: Value = serde_json::from_slice(&source_bytes).map_err(|e| e.to_string())?;
    provider_continuity_rejection::verify_source(config, pending, &source)?;
    let lookup = report
        .get("lookup")
        .ok_or("provider resolution exact lookup absent")?;
    let binary = artifact(&lookup["binary"], directory)?;
    let presentation = artifact(&lookup["presentation"], directory)?;
    if presentation.with_extension("bin") != binary || json(&presentation)? != lookup["outcome"] {
        return Err("provider resolution lookup presentation differs from native receipt".into());
    }
    match string(&report, "decision")? {
        "already-confirmed" if lookup["outcome"]["type"] == "confirmed" => {
            Ok((false, presentation, report))
        }
        "retire-expired-contention" => {
            if lookup["outcome"] != json!({"type":"absent"})
                || json(&pending.attempt.join("outcome.json"))? != json!({"type":"contention"})
            {
                return Err(
                    "provider resolution is not exact contention followed by native absence".into(),
                );
            }
            for name in GUARDED {
                copied_input(&report, pending, directory, name)?;
            }
            let exact_descriptor: Value = serde_json::from_slice(&copied_input(
                &report,
                pending,
                directory,
                "provider-continuity/descriptor.json",
            )?)
            .map_err(|e| e.to_string())?;
            if &exact_descriptor != descriptor
                || read(&config.state_dir.join(format!(
                    "provider-continuity-source-{:016}.json",
                    pending.operation_id
                )))? != copied_input(
                    &report,
                    pending,
                    directory,
                    "provider-continuity/descriptor.json",
                )?
            {
                return Err(
                    "provider resolution no longer names the retained reserve/fence".into(),
                );
            }
            if !descriptor["fence"].is_null() {
                for name in [
                    "provider-continuity/fence-call.bin",
                    "provider-continuity/fence-outcome.bin",
                ] {
                    copied_input(&report, pending, directory, name)?;
                }
            }
            let fresh = &report["freshProof"];
            for key in ["request", "frame", "presentation"] {
                artifact(&fresh[key], directory)?;
            }
            if json(&artifact(&fresh["presentation"], directory)?)? != report["freshPrefix"] {
                return Err("provider resolution fresh prefix presentation changed".into());
            }
            for key in ["reassembledCall", "profile", "settlementCommand"] {
                artifact(&report[key], directory)?;
            }
            if read(&artifact(&report["reassembledCall"], directory)?)?
                != copied_input(&report, pending, directory, "call.bin")?
            {
                return Err(
                    "provider resolution reassembly differs from retained signed call".into(),
                );
            }
            if serde_json::from_slice::<Value>(&copied_input(
                &report,
                pending,
                directory,
                "provider-continuity/continuity.json",
            )?)
            .map_err(|e| e.to_string())?
                != report["originalPrefix"]
            {
                return Err("provider resolution original checked prefix changed".into());
            }
            let profile = json(&artifact(&report["profile"], directory)?)?;
            if profile["providerContinuityAdmission"] != "exact-height-v1"
                || profile["genesisHeight"] != report["expiration"]["genesisHeight"]
            {
                return Err("provider resolution differs from native admission profile".into());
            }
            let plan: Value =
                serde_json::from_slice(&copied_input(&report, pending, directory, "plan.json")?)
                    .map_err(|e| e.to_string())?;
            let slots = plan["slots"]
                .as_array()
                .ok_or("provider resolution signed slots absent")?;
            let deadlines: Vec<Value> = slots
                .iter()
                .map(|slot| slot["signing"]["validUntil"].clone())
                .collect();
            if report["expiration"]["signedDeadlines"] != json!(deadlines) {
                return Err("provider resolution deadlines differ from exact signed slots".into());
            }
            expiration(&report)?;
            Ok((true, presentation, report))
        }
        _ => Err("provider resolution has no supported positive decision".into()),
    }
}

impl Runtime {
    pub(super) fn resolve_guarded_provider_pending(
        &mut self,
        pending: &Pending,
    ) -> Result<Resolution> {
        if !matches!(
            pending.operation.as_str(),
            "provider settle" | "provider recovery settle"
        ) {
            return Ok(Resolution::NotApplicable);
        }
        // This selects a read-only investigation only. Mini independently
        // decodes the native outcome before it can emit a retirement decision.
        let outcome = match fs::symlink_metadata(pending.attempt.join("outcome.json")) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(Resolution::NotApplicable),
            Err(e) => return Err(e.to_string()),
            Ok(_) => json(&pending.attempt.join("outcome.json"))?,
        };
        if outcome["type"] != "contention" {
            return Ok(Resolution::NotApplicable);
        }
        let stop = |runtime: &Runtime| {
            if runtime.startup_recovery_active {
                runtime.quiescence_recovery_stop_proof()
            } else {
                runtime.quiescence_stop_proof()
            }
        };
        stop(self)?;
        let hold_before =
            serde_json::to_value(&self.journal.provider_hold).map_err(|e| e.to_string())?;
        let descriptor = self.provider_continuity_value()?;
        let id = self.next_id()?;
        let directory = self
            .config
            .state_dir
            .join(format!("provider-resolution-{id:016}"));
        self.journal.reconciliation_log.push(json!({"action":"inspect-expired-provider-contention","operationId":pending.operation_id.to_string(),"proof":directory,"heldAllowanceReleased":false,"providerRequestRepeated":false}));
        self.save()?;
        let socket = self
            .config
            .host_socket
            .as_ref()
            .ok_or("provider resolution requires pinned socket")?;
        let paths = [
            &self.config.host,
            &self.config.host_config,
            socket,
            &pending.attempt,
            &directory,
        ];
        let text: Vec<&str> = paths
            .iter()
            .map(|p| p.to_str().ok_or("provider resolution path UTF-8"))
            .collect::<std::result::Result<_, _>>()?;
        self.command_output(
            &self.config.mini,
            &[
                "provider-continuity",
                "--host",
                text[0],
                "--config",
                text[1],
                "--socket",
                text[2],
                "--guarded-attempt",
                text[3],
                "--dir",
                text[4],
            ],
        )?;
        let (retire, receipt, report) = inspect(&self.config, pending, &directory, &descriptor)?;
        stop(self)?;
        let (_, again, report_again) = inspect(
            &self.config,
            pending,
            &directory,
            &self.provider_continuity_value()?,
        )?;
        if again != receipt
            || report_again != report
            || serde_json::to_value(&self.journal.provider_hold).map_err(|e| e.to_string())?
                != hold_before
            || serde_json::to_value(&self.journal.provider_pending).map_err(|e| e.to_string())?
                != serde_json::to_value(Some(pending)).map_err(|e| e.to_string())?
        {
            return Err("provider resolution ownership changed while observing".into());
        }
        self.journal.reconciliation_log.push(json!({"action":if retire {"retire-expired-provider-contention"} else {"recognize-exact-provider-settlement"},"operationId":pending.operation_id.to_string(),"proof":directory,"reportSha256":sha256_file(&directory.join("resolution.json"))?,"heldAllowanceReleased":false,"providerRequestRepeated":false}));
        if retire {
            self.journal.provider_pending = None;
        }
        self.save()?;
        Ok(if retire {
            Resolution::Retired
        } else {
            Resolution::Confirmed(receipt)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn proof() -> Value {
        json!({"expiration":{"genesisHeight":"10","originalAcceptedCount":"7","checkedAcceptedCount":"8","checkedHeight":"18","signedDeadlines":["17","16"]},"originalPrefix":{"checkedAcceptedCount":"7","checkedWorldRoot":"991"},"freshPrefix":{"checkedAcceptedCount":"8","priorChecked":{"acceptedCount":"7","worldRoot":"991"}}})
    }
    fn files() -> (PathBuf, PathBuf, Pending, Value) {
        let root = std::env::temp_dir().join(format!(
            "provider-resolution-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let attempt = root.join("attempt");
        let directory = root.join("proof");
        fs::create_dir_all(&attempt).unwrap();
        fs::create_dir_all(directory.join("retained")).unwrap();
        let pending = Pending {
            operation_id: 1,
            operation: "provider settle".into(),
            attempt: attempt.clone(),
            uncertain: true,
            publication: None,
        };
        for p in [
            attempt.join("call.bin"),
            directory.join("retained/call.bin"),
        ] {
            write_new(&p, b"exact signed call").unwrap();
        }
        let report = json!({"inputs":{"call.bin":{"path":attempt.join("call.bin"),"retainedPath":directory.join("retained/call.bin"),"sha256":sha256_bytes(b"exact signed call").unwrap()}}});
        (root, directory, pending, report)
    }
    #[test]
    fn copied_evidence_binds_both_paths_and_bytes() {
        let (root, directory, pending, report) = files();
        assert!(copied_input(&report, &pending, &directory, "call.bin").is_ok());
        for key in ["path", "retainedPath"] {
            let mut changed = report.clone();
            changed["inputs"]["call.bin"][key] = json!(root.join("elsewhere"));
            assert!(copied_input(&changed, &pending, &directory, "call.bin").is_err());
        }
        fs::write(directory.join("retained/call.bin"), b"replacement").unwrap();
        assert!(copied_input(&report, &pending, &directory, "call.bin").is_err());
        fs::write(directory.join("retained/call.bin"), b"exact signed call").unwrap();
        fs::write(pending.attempt.join("call.bin"), b"changed original").unwrap();
        assert!(copied_input(&report, &pending, &directory, "call.bin").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn receipt_artifacts_refuse_escape_symlink_and_nonprivate_file() {
        let (root, directory, pending, report) = files();
        let path = directory.join("lookup.bin");
        write_new(&path, b"receipt").unwrap();
        let mut item = json!({"path":path,"sha256":sha256_bytes(b"receipt").unwrap()});
        assert!(artifact(&item, &directory).is_ok());
        item["path"] = json!(directory.join("../proof/lookup.bin"));
        assert!(artifact(&item, &directory).is_err());
        item["path"] = json!(path);
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(artifact(&item, &directory).is_err());
        fs::remove_file(&path).unwrap();
        std::os::unix::fs::symlink(pending.attempt.join("call.bin"), &path).unwrap();
        assert!(artifact(&item, &directory).is_err());
        fs::remove_file(directory.join("retained/call.bin")).unwrap();
        std::os::unix::fs::symlink(
            pending.attempt.join("call.bin"),
            directory.join("retained/call.bin"),
        )
        .unwrap();
        assert!(copied_input(&report, &pending, &directory, "call.bin").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn strict_expiry_requires_exact_original_observed_prefix() {
        assert!(expiration(&proof()).is_ok());
        for field in ["acceptedCount", "worldRoot"] {
            let mut p = proof();
            p["freshPrefix"]["priorChecked"][field] = json!("9");
            assert!(expiration(&p).is_err());
        }
        let mut p = proof();
        p["freshPrefix"]
            .as_object_mut()
            .unwrap()
            .remove("priorChecked");
        assert!(expiration(&p).is_err());
    }
    #[test]
    fn same_height_unknown_or_overflow_never_retire() {
        for deadline in [
            "18",
            "19",
            "-1",
            "018",
            "340282366920938463463374607431768211456",
        ] {
            let mut p = proof();
            p["expiration"]["signedDeadlines"] = json!([deadline]);
            assert!(expiration(&p).is_err());
        }
        let mut p = proof();
        p["expiration"]["signedDeadlines"] = json!([]);
        assert!(expiration(&p).is_err());
        let mut p = proof();
        p["expiration"]["genesisHeight"] = json!("11");
        assert!(expiration(&p).is_err());
        let mut p = proof();
        p["freshPrefix"]["checkedAcceptedCount"] = json!("9");
        assert!(expiration(&p).is_err());
    }
}
