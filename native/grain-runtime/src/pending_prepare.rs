//! Recovery of an interrupted parent settlement preparation. Never releases a
//! hold from missing files: reauthors the retained semantic operation through
//! current signed Mini admission after proving the old custody process stopped.
use super::*;

fn ancestry(config: &Config, pending: &Pending) -> Result<Vec<PathBuf>> {
    let base = config
        .state_dir
        .join(format!("attempt-{:016}", pending.operation_id));
    let relative = pending
        .attempt
        .strip_prefix(&base)
        .map_err(|_| "pending prepare path differs from operation identity")?;
    let mut paths = vec![base.clone()];
    let mut next = base;
    for component in relative.components() {
        if component.as_os_str() != "reprepare" || paths.len() >= 8 {
            return Err("pending prepare recovery ancestry is invalid or exhausted".into());
        }
        next.push("reprepare");
        paths.push(next.clone());
    }
    Ok(paths)
}

fn validate_source(
    config: &Config,
    pending: &Pending,
    hold: &HeldCharge,
    due: &str,
    source: &Value,
    observed: &Value,
) -> Result<()> {
    let before = observed.get("grain").ok_or("signed parent grain absent")?;
    let payload = source
        .pointer("/grain/context/payload")
        .and_then(Value::as_str)
        .ok_or("retained settlement payload absent")?;
    if pending.operation != "settle"
        || pending.publication.is_some()
        || pending.uncertain
        || !hold.reserve_confirmed
        || hold.reserve_refused
        || due != hold.charge
        || before.get("generation").and_then(Value::as_str) != Some(hold.before_generation.as_str())
        || before.get("reserved").and_then(Value::as_str) != Some(hold.reserve.as_str())
        || !matches!(
            before.get("status").and_then(Value::as_str),
            Some("3" | "4")
        )
    {
        return Err(
            "interrupted preparation is not this completed parent hold's settlement".into(),
        );
    }
    if !grain_source::retained_identity(
        source,
        &config.task,
        &config.task,
        &config.subject,
        pending.operation_id,
    ) {
        return Err("retained settlement operation identity differs".into());
    }
    let authority = Authority {
        task: config.task.clone(),
        subject: config.subject.clone(),
        capability: config.capability.clone(),
        query_capability: config.query_capability.clone(),
        custody_key: config.custody_key.clone(),
    };
    let expected = grain_source::source(
        &authority,
        observed,
        grain_source::Transition {
            identity: source["intentNonce"]
                .as_str()
                .ok_or("retained intent nonce absent")?,
            payload,
            operation: json!({"type":"settle","charge":due}),
            publications: vec![],
            parent_witness: None,
            grants: grain_observation_grants(&authority, None, &[])?,
        },
    )?;
    if source != &expected {
        return Err(
            "retained settlement differs from its identity, pinned charge or fresh signed state"
                .into(),
        );
    }
    Ok(())
}

fn absent(path: &Path) -> Result<bool> {
    match fs::symlink_metadata(path) {
        Ok(_) => Ok(false),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(true),
        Err(e) => Err(format!(
            "inspect retained preparation {}: {e}",
            path.display()
        )),
    }
}

fn next_attempt(paths: &[PathBuf]) -> Result<PathBuf> {
    // The journal is durable before Mini creates its directory. If interrupted
    // in that window, retry the already-claimed absent destination itself.
    for path in paths.iter().skip(1) {
        if absent(path)? {
            return Ok(path.clone());
        }
    }
    let next = paths
        .last()
        .ok_or("preparation ancestry empty")?
        .join("reprepare");
    if !absent(&next)? {
        return Err("next preparation path already exists without a journal binding".into());
    }
    Ok(next)
}

fn prove_prepare_senders_stopped(task: &str) -> Result<()> {
    prove_prior_run_stopped(task)
}

impl Runtime {
    pub(super) fn reprepare_parent_settlement(
        &mut self,
        slot: AuthoritySlot,
        pending: &Pending,
    ) -> Result<bool> {
        if slot != AuthoritySlot::Parent || pending.operation != "settle" {
            return Ok(false);
        }
        // This repair runs before input admission in a restarted controller,
        // never as a competing retry while an old/current child could dispatch.
        if !self.startup_recovery_active
            || self.child.is_some()
            || self.journal.child.is_some()
            || self.journal.tool_pending.is_some()
            || self.journal.tool_hold.is_some()
            || self.journal.provider_pending.is_some()
            || self.journal.provider_hold.is_some()
            || self.journal.provider_attempt.is_some()
            || self.journal.dispatch_pending.is_some()
            || self.journal.dispatch_hold.is_some()
            || self.journal.dispatch_attempt.is_some()
            || !self.custody_gate.is_idle()
        {
            return Ok(false);
        }
        prove_prepare_senders_stopped(&self.config.task)?;
        let paths = ancestry(&self.config, pending)?;
        let source_path = self
            .config
            .state_dir
            .join(format!("source-{:016}.json", pending.operation_id));
        let source_bytes = bounded_regular_file(&source_path, 1_048_576)?;
        let source: Value = serde_json::from_slice(&source_bytes).map_err(|e| e.to_string())?;
        let config_bytes = bounded_regular_file(&self.config.host_config, 1_048_576)?;
        for (index, path) in paths.iter().enumerate() {
            if !absent(&path.join("call.bin"))? {
                return Err("retained signed call requires exact lookup; never reprepare".into());
            }
            match fs::symlink_metadata(path) {
                Ok(meta) if meta.is_dir() && meta.uid() == unsafe { libc::geteuid() } => {}
                Err(e) if e.kind() == io::ErrorKind::NotFound && index != 0 => continue,
                _ => {
                    return Err(
                        "retained preparation directory is absent or not owner-controlled".into(),
                    )
                }
            }
            // The original attempt must identify its exact native submission.
            // A later retry may have died before copying these same artifacts.
            for (name, expected) in [
                ("intent.json", &source_bytes),
                ("config.json", &config_bytes),
            ] {
                let file = path.join(name);
                if index != 0 && absent(&file)? {
                    continue;
                }
                if bounded_regular_file(&file, 1_048_576)? != *expected {
                    return Err(format!("retained preparation {name} differs"));
                }
            }
            let manifest_path = path.join("attempt.json");
            if index != 0 && absent(&manifest_path)? {
                continue;
            }
            let manifest: Value =
                serde_json::from_slice(&bounded_regular_file(&manifest_path, 65536)?)
                    .map_err(|e| e.to_string())?;
            if manifest["format"] != "minidregg-resource-client-attempt-v1"
                || manifest["operation"] != "submit"
                || manifest["host"] != json!(self.config.host)
                || manifest["config"] != json!(path.join("config.json"))
                || manifest.get("socket")
                    != self.config.host_socket.as_ref().map(|v| json!(v)).as_ref()
            {
                return Err("retained preparation manifest differs from controller binding".into());
            }
        }
        let hold = self
            .journal
            .parent_hold
            .clone()
            .ok_or("parent settlement hold absent")?;
        let due = self
            .journal
            .settlement_due
            .clone()
            .ok_or("parent completion charge absent")?;
        let observed = self.query_as(&self.parent())?;
        validate_source(&self.config, pending, &hold, &due, &source, &observed)?;
        // query_as has joined its custody child. Recheck physical quiescence and
        // the negative send boundary immediately before publishing the retry.
        prove_prepare_senders_stopped(&self.config.task)?;
        for path in &paths {
            if !absent(&path.join("call.bin"))? {
                return Err(
                    "signed call appeared during prepare recovery; use exact lookup".into(),
                );
            }
        }
        let next = next_attempt(&paths)?;
        self.journal.reconciliation_log.push(json!({
            "action":"reprepare-interrupted-parent-settlement","operationId":pending.operation_id.to_string(),
            "originalAttempt":paths[0],"previousAttempt":pending.attempt,"attempt":next,
            "sourceSha256":sha256_file(&source_path)?,"charge":due,
            "basis":"fresh controller cgroup sole-member proof; exact retained source/config; no durable call in ancestry; unchanged signed parent hold",
            "signedTargetRoot":observed["targetRoot"],"heldAllowanceReleased":false}));
        self.journal
            .pending
            .as_mut()
            .ok_or("pending settlement disappeared")?
            .attempt = next.clone();
        self.save()?;
        let cfg = &self.config;
        let mut args = vec![
            "submit",
            "--host",
            cfg.host.to_str().ok_or("host UTF8")?,
            "--config",
            cfg.host_config.to_str().ok_or("config UTF8")?,
            "--intent",
            source_path.to_str().ok_or("source UTF8")?,
            "--intent-kind",
            "grain-intent",
            "--key",
            cfg.custody_key.to_str().ok_or("key UTF8")?,
            "--dir",
            next.to_str().ok_or("attempt UTF8")?,
        ];
        if let Some(socket) = &cfg.host_socket {
            args.extend(["--socket", socket.to_str().ok_or("socket UTF8")?]);
        }
        // Mini fsyncs call.bin and its directory before sending any submit.
        // On interruption the updated pending record still owns this exact call.
        self.command_output(&cfg.mini, &args)?;
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (Config, Pending, HeldCharge, Value, Value) {
        let config: Config = serde_json::from_value(json!({
            "mini":"/mini","host":"/host","hostConfig":"/config","controlSocket":"/control",
            "custodyKey":"/key","stateDir":"/state","cwd":"/cwd","task":"8903",
            "subject":"7","capability":"71","queryCapability":"71","commands":[]
        }))
        .unwrap();
        let pending: Pending =
            serde_json::from_value(json!({"operationId":33,"operation":"settle",
            "attempt":"/state/attempt-0000000000000033","uncertain":false,"publication":null}))
            .unwrap();
        let hold:HeldCharge=serde_json::from_value(json!({"reserve":"3","charge":"1","beforeGeneration":"1",
            "beforeTargetRoot":"old","reserveAttempt":null,"reserveConfirmed":true,"reserveRefused":false,
            "reserveBoundary":"accepted"})).unwrap();
        let observed = json!({"targetRoot":"fresh","grain":{"generation":"1","status":"4","remaining":"997","reserved":"3"}});
        let authority = Authority {
            task: config.task.clone(),
            subject: config.subject.clone(),
            capability: config.capability.clone(),
            query_capability: config.query_capability.clone(),
            custody_key: config.custody_key.clone(),
        };
        let source = grain_source::source(
            &authority,
            &observed,
            grain_source::Transition {
                identity: "33",
                payload: "worker ended",
                operation: json!({"type":"settle","charge":"1"}),
                publications: vec![],
                parent_witness: None,
                grants: grain_observation_grants(&authority, None, &[]).unwrap(),
            },
        )
        .unwrap();
        (config, pending, hold, observed, source)
    }
    #[test]
    fn pending_prepare_requires_exact_retained_identity_charge_and_signed_prestate() {
        let (config, pending, hold, observed, source) = fixture();
        validate_source(&config, &pending, &hold, "1", &source, &observed).unwrap();
        let mut namespaced = source.clone();
        let id = grain_source::operation_id(&config.task, &config.task, &config.subject, 33);
        namespaced["intentNonce"] = json!(id);
        namespaced["grain"]["context"]["operationId"] = json!(id);
        validate_source(&config, &pending, &hold, "1", &namespaced, &observed).unwrap();
        for pointer in [
            "/targetRoot",
            "/grain/generation",
            "/grain/reserved",
            "/grain/remaining",
            "/grain/status",
        ] {
            let mut changed = observed.clone();
            *changed.pointer_mut(pointer).unwrap() = json!("999");
            assert!(
                validate_source(&config, &pending, &hold, "1", &source, &changed).is_err(),
                "{pointer}"
            );
        }
        for pointer in [
            "/grain/context/operationId",
            "/intentNonce",
            "/grain/subject",
            "/grain/capability",
            "/grain/operation/charge",
        ] {
            let mut changed = source.clone();
            *changed.pointer_mut(pointer).unwrap() = json!("999");
            assert!(
                validate_source(&config, &pending, &hold, "1", &changed, &observed).is_err(),
                "{pointer}"
            );
        }
        assert!(validate_source(&config, &pending, &hold, "2", &source, &observed).is_err());
        let mut uncertain = pending.clone();
        uncertain.uncertain = true;
        assert!(validate_source(&config, &uncertain, &hold, "1", &source, &observed).is_err());
        uncertain = pending.clone();
        uncertain.operation = "provider settle".into();
        assert!(validate_source(&config, &uncertain, &hold, "1", &source, &observed).is_err());
        let mut unconfirmed = hold.clone();
        unconfirmed.reserve_confirmed = false;
        assert!(validate_source(&config, &pending, &unconfirmed, "1", &source, &observed).is_err());
    }
    #[test]
    fn pending_prepare_ancestry_cannot_escape_or_change_operation() {
        let (config, mut pending, _, _, _) = fixture();
        assert_eq!(ancestry(&config, &pending).unwrap().len(), 1);
        pending.attempt.push("reprepare");
        assert_eq!(ancestry(&config, &pending).unwrap().len(), 2);
        pending.attempt.push("../reprepare");
        assert!(ancestry(&config, &pending).is_err());
        pending.attempt = PathBuf::from("/state/attempt-0000000000000034");
        assert!(ancestry(&config, &pending).is_err());
    }
    #[test]
    fn pending_prepare_reuses_journaled_path_when_create_never_ran() {
        let root =
            std::env::temp_dir().join(format!("pending-prepare-next-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let next = root.join("reprepare");
        assert_eq!(next_attempt(&[root.clone()]).unwrap(), next);
        assert_eq!(next_attempt(&[root.clone(), next.clone()]).unwrap(), next);
        fs::create_dir(&next).unwrap();
        assert_eq!(
            next_attempt(&[root.clone(), next.clone()]).unwrap(),
            next.join("reprepare")
        );
        fs::remove_dir(next).unwrap();
        fs::remove_dir(root).unwrap();
    }
    #[test]
    fn pending_prepare_dangling_call_is_not_absence() {
        let root =
            std::env::temp_dir().join(format!("pending-prepare-test-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let call = root.join("call.bin");
        assert!(absent(&call).unwrap());
        std::os::unix::fs::symlink(root.join("missing"), &call).unwrap();
        assert!(!absent(&call).unwrap());
        fs::remove_file(call).unwrap();
        fs::remove_dir(root).unwrap();
    }
}
