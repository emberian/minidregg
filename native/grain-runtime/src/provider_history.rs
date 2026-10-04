//! Exact historical inputs for guarded provider settlement/fencing. The Mini
//! client binds the native continuity result to an expiring signed plan; this
//! module never treats equal present-day balances as a reservation identity.
use super::*;

pub(super) fn require_native_support(profile: &Value) -> Result<()> {
    if profile
        .get("providerContinuityAdmission")
        .and_then(Value::as_str)
        != Some("exact-height-v1")
    {
        return Err("pinned Host lacks provider history-bound settlement admission".into());
    }
    Ok(())
}

#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct Fence {
    operation_id: u64,
    attempt: PathBuf,
    source_sha256: String,
    call_sha256: String,
    outcome_path: PathBuf,
    outcome_sha256: String,
    receipt: ReserveAnchor,
}

fn prefix(receipt: &ReserveAnchor) -> Value {
    json!({"type":"verified-mini-native-prefix-v1", "transactionId":receipt.transaction_id,
        "eventId":receipt.event_id,"acceptedCount":receipt.accepted_count,"worldRoot":receipt.world_root})
}
fn input(
    call: &Path,
    call_hash: &str,
    outcome: &Path,
    outcome_hash: &str,
    receipt: &ReserveAnchor,
) -> Result<Value> {
    for (path, hash, limit) in [(call, call_hash, 4_194_304), (outcome, outcome_hash, 1024)] {
        if !path.is_absolute() || sha256_bytes(&bounded_regular_file(path, limit)?)? != hash {
            return Err("provider continuity input differs from exact retained evidence".into());
        }
    }
    Ok(
        json!({"call":{"path":call,"sha256":call_hash},"outcome":{"path":outcome,"sha256":outcome_hash},"receipt":prefix(receipt)}),
    )
}

fn validate_fence_source(
    controller_task: &str,
    authority: &Authority,
    operation_id: u64,
    hold: &HeldCharge,
    route: &str,
    source: &Value,
) -> Result<()> {
    // Metering retains the route name, while the source grain state carries
    // its declared numeric code. Use the same mapping as reserve/settlement.
    let route = provider_route_code(route)?;
    let before = source
        .pointer("/grain/before")
        .ok_or("provider fence pre-state absent")?;
    let identity = source
        .get("intentNonce")
        .and_then(Value::as_str)
        .ok_or("provider fence identity absent")?;
    let payload = source
        .pointer("/grain/context/payload")
        .and_then(Value::as_str)
        .ok_or("provider fence payload absent")?;
    if !matches!(
        payload,
        "parent hard connection lost" | "operator fenced provider request"
    ) || !grain_source::retained_identity(
        &source,
        controller_task,
        &authority.task,
        &authority.subject,
        operation_id,
    ) || before.get("generation").and_then(Value::as_str)
        != Some(hold.before_generation.as_str())
        || before.get("status").and_then(Value::as_str) != Some("3")
        || before.get("reserved").and_then(Value::as_str) != Some(hold.reserve.as_str())
        || before.get("route").and_then(Value::as_str) != Some(route)
    {
        return Err("provider fence differs from this request's hard-held origin".into());
    }
    let observed = json!({"grain":before,"targetRoot":source.pointer("/grain/expectedTargetRoot").ok_or("provider fence target root absent")?});
    let expected = grain_source::source(
        authority,
        &observed,
        grain_source::Transition {
            identity,
            payload,
            operation: json!({"type":"disconnect"}),
            publications: vec![],
            parent_witness: None,
            grants: grain_observation_grants(authority, None, &[])?,
        },
    )?;
    if source != &expected {
        return Err("provider fence is not the complete source-owned disconnect".into());
    }
    Ok(())
}

impl Runtime {
    pub(super) fn retire_continuity_rejection(&mut self, pending: &Pending) -> Result<bool> {
        if !matches!(
            pending.operation.as_str(),
            "provider settle" | "provider recovery settle" | "provider disconnect"
        ) {
            return Ok(false);
        }
        let evidence = provider_continuity_rejection::inspect(&self.config, pending, || {
            if self.startup_recovery_active {
                self.quiescence_recovery_stop_proof()
            } else {
                self.quiescence_stop_proof()
            }
        })?;
        let Some(evidence) = evidence else {
            return Ok(false);
        };
        // The native reservation and response remain held. This retires only
        // an exact source-owned attempt proven unable to have reached signing.
        // Any later attempt starts from fresh state and native continuity.
        self.journal.reconciliation_log.push(json!({
            "action":"recognize-provider-continuity-rejection",
            "operationId":pending.operation_id.to_string(), "operation":pending.operation,
            "attempt":pending.attempt, "evidence":evidence, "heldAllowanceReleased":false,
            "providerRequestRepeated":false
        }));
        self.journal.provider_pending = None;
        self.save()?;
        Ok(true)
    }

    pub(super) fn provider_fence_record(
        &self,
        pending: &Pending,
        outcome_path: &Path,
    ) -> Result<Fence> {
        let authority = self.provider()?;
        let hold = self
            .journal
            .provider_hold
            .as_ref()
            .ok_or("provider fence has no retained reservation")?;
        let provider = self
            .journal
            .provider_attempt
            .as_ref()
            .ok_or("provider fence has no exact request")?;
        let pin = provider
            .metering_pin
            .as_ref()
            .ok_or("provider fence route absent")?;
        if !hold.reserve_confirmed
            || hold.reserve_refused
            || pending.attempt
                != self
                    .config
                    .state_dir
                    .join(format!("attempt-{:016}", pending.operation_id))
            || outcome_path.parent() != Some(pending.attempt.as_path())
        {
            return Err("provider fence has no exact confirmed origin".into());
        }
        let source_path = self
            .config
            .state_dir
            .join(format!("source-{:016}.json", pending.operation_id));
        let bytes = bounded_regular_file(&source_path, 131_072)?;
        if bytes != bounded_regular_file(&pending.attempt.join("intent.json"), 131_072)? {
            return Err("provider fence source differs from submitted intent".into());
        }
        let source: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
        validate_fence_source(
            &self.config.task,
            &authority,
            pending.operation_id,
            hold,
            &pin.route,
            &source,
        )?;
        let outcome: Value = serde_json::from_slice(&bounded_regular_file(outcome_path, 131_072)?)
            .map_err(|e| e.to_string())?;
        if !matches!(
            outcome.get("confirmation").and_then(Value::as_str),
            Some("installed" | "replayed")
        ) {
            return Err("provider fence is not confirmed".into());
        }
        let receipt = ReserveAnchor::from_confirmed(&outcome)?;
        let origin = hold
            .reserve_anchor
            .as_ref()
            .ok_or("provider original reserve receipt absent")?;
        let count = receipt
            .accepted_count
            .parse::<u64>()
            .map_err(|_| "provider fence receipt count exceeds bound")?;
        let original = origin
            .accepted_count
            .parse::<u64>()
            .map_err(|_| "provider reserve receipt count exceeds bound")?;
        if count <= original {
            return Err("provider fence precedes its retained reserve".into());
        }
        Ok(Fence {
            operation_id: pending.operation_id,
            attempt: pending.attempt.clone(),
            source_sha256: sha256_bytes(&bytes)?,
            call_sha256: sha256_bytes(&bounded_regular_file(
                &pending.attempt.join("call.bin"),
                4_194_304,
            )?)?,
            outcome_path: outcome_path.to_owned(),
            outcome_sha256: sha256_bytes(&bounded_regular_file(
                &outcome_path.with_extension("bin"),
                1024,
            )?)?,
            receipt,
        })
    }

    pub(super) fn record_provider_fence(
        &mut self,
        pending: &Pending,
        outcome_path: &Path,
    ) -> Result<()> {
        let record = self.provider_fence_record(pending, outcome_path)?;
        let attempt = self
            .journal
            .provider_attempt
            .as_mut()
            .ok_or("provider request disappeared")?;
        if attempt.fence.as_ref().is_some_and(|old| old != &record) {
            return Err("provider request already retains a different fence".into());
        }
        attempt.fence = Some(record);
        Ok(())
    }

    /// Older journals did not index the fence. Select only one complete local
    /// source-owned confirmed disconnect, then let native historical admission
    /// verify its exact call, receipt, position and every intervening write.
    pub(super) fn recover_provider_fence(&mut self) -> Result<()> {
        if self
            .journal
            .provider_attempt
            .as_ref()
            .and_then(|a| a.fence.as_ref())
            .is_some()
        {
            return Ok(());
        }
        let hold = self
            .journal
            .provider_hold
            .as_ref()
            .ok_or("provider hold absent")?;
        let reserve = hold
            .reserve_attempt
            .as_ref()
            .and_then(|p| p.file_name())
            .and_then(|s| s.to_str())
            .and_then(|s| s.strip_prefix("attempt-"))
            .and_then(|s| s.parse::<u64>().ok())
            .ok_or("provider reserve directory identity absent")?;
        let end = self.journal.next_operation_id;
        if end.saturating_sub(reserve) > 4096 {
            return Err("legacy provider fence search exceeds bounded retained history".into());
        }
        let mut found = None;
        for id in reserve.saturating_add(1)..end {
            let directory = self.config.state_dir.join(format!("attempt-{id:016}"));
            let source = self.config.state_dir.join(format!("source-{id:016}.json"));
            match fs::symlink_metadata(&source) {
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(format!("provider fence source metadata: {e}")),
                Ok(_) => {}
            }
            let value: Value = serde_json::from_slice(&bounded_regular_file(&source, 131_072)?)
                .map_err(|e| e.to_string())?;
            if value.pointer("/grain/task").and_then(Value::as_str)
                != self.config.provider_task.as_ref().map(|t| t.task.as_str())
                || value
                    .pointer("/grain/operation/type")
                    .and_then(Value::as_str)
                    != Some("disconnect")
                || value
                    .pointer("/grain/before/status")
                    .and_then(Value::as_str)
                    != Some("3")
            {
                continue;
            }
            let mut candidates = Vec::new();
            let entries = match fs::read_dir(&directory) {
                Ok(entries) => entries,
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => return Err(format!("provider fence attempt directory: {e}")),
            };
            {
                for entry in entries {
                    let entry = entry.map_err(|e| e.to_string())?;
                    let name = entry.file_name();
                    let Some(name) = name.to_str() else {
                        continue;
                    };
                    let retry = name
                        .strip_prefix("retry-")
                        .and_then(|n| n.strip_suffix(".json"))
                        .is_some_and(|n| {
                            (4..=16).contains(&n.len()) && n.bytes().all(|b| b.is_ascii_digit())
                        });
                    if name == "outcome.json" || retry {
                        candidates.push(entry.path());
                    }
                }
            }
            candidates.sort();
            for outcome in candidates {
                let value: Value =
                    serde_json::from_slice(&bounded_regular_file(&outcome, 131_072)?)
                        .map_err(|e| e.to_string())?;
                if value.get("type").and_then(Value::as_str) != Some("confirmed") {
                    continue;
                }
                let pending = Pending {
                    operation_id: id,
                    operation: "provider disconnect".into(),
                    attempt: directory.clone(),
                    uncertain: false,
                    publication: None,
                };
                let record = self.provider_fence_record(&pending, &outcome)?;
                if found.as_ref().is_some_and(|old: &Fence| {
                    old.operation_id != record.operation_id || old.receipt != record.receipt
                }) {
                    return Err("multiple different confirmed provider fences require exact history reconciliation".into());
                }
                found = Some(record);
            }
        }
        let record = found.ok_or("no exact source-owned provider fence retained")?;
        self.journal.reconciliation_log.push(json!({"action":"retain-original-provider-fence","operationId":record.operation_id.to_string(),"receipt":record.receipt,"heldAllowanceReleased":false}));
        self.journal
            .provider_attempt
            .as_mut()
            .ok_or("provider request absent")?
            .fence = Some(record);
        self.save()
    }

    pub(super) fn provider_continuity_value(&self) -> Result<Value> {
        let task = self
            .config
            .provider_task
            .as_ref()
            .ok_or("provider task absent")?;
        let hold = self
            .journal
            .provider_hold
            .as_ref()
            .ok_or("provider continuity requires retained hold")?;
        if !hold.reserve_confirmed || hold.reserve_refused {
            return Err("provider continuity requires exact confirmed reserve".into());
        }
        let path = hold
            .reserve_attempt
            .as_ref()
            .ok_or("provider reserve attempt absent")?;
        let source_hash = hold
            .reserve_source_sha256
            .as_deref()
            .ok_or("provider reserve source hash absent")?;
        if sha256_bytes(&bounded_regular_file(&path.join("intent.json"), 131_072)?)? != source_hash
        {
            return Err("provider reserve intent differs from confirmed source".into());
        }
        let call = path.join("call.bin");
        let outcome = hold
            .reserve_outcome_path
            .as_ref()
            .ok_or("provider reserve receipt absent")?
            .with_extension("bin");
        let reserve = input(
            &call,
            hold.reserve_call_sha256
                .as_deref()
                .ok_or("provider reserve call hash absent")?,
            &outcome,
            hold.reserve_outcome_sha256
                .as_deref()
                .ok_or("provider reserve outcome hash absent")?,
            hold.reserve_anchor
                .as_ref()
                .ok_or("provider reserve anchor absent")?,
        )?;
        let fence = if let Some(fence) = self
            .journal
            .provider_attempt
            .as_ref()
            .and_then(|a| a.fence.as_ref())
        {
            let pending = Pending {
                operation_id: fence.operation_id,
                operation: "provider disconnect".into(),
                attempt: fence.attempt.clone(),
                uncertain: false,
                publication: None,
            };
            if self.provider_fence_record(&pending, &fence.outcome_path)? != *fence {
                return Err("retained provider fence evidence changed".into());
            }
            input(
                &fence.attempt.join("call.bin"),
                &fence.call_sha256,
                &fence.outcome_path.with_extension("bin"),
                &fence.outcome_sha256,
                &fence.receipt,
            )?
        } else {
            Value::Null
        };
        let descriptor = json!({"type":"mini-provider-continuity-v1","providerResourceId":task.task,"reserve":reserve,"fence":fence});
        Ok(descriptor)
    }

    pub(super) fn provider_continuity_descriptor(&self, id: u64) -> Result<PathBuf> {
        let descriptor = self.provider_continuity_value()?;
        let path = self
            .config
            .state_dir
            .join(format!("provider-continuity-source-{id:016}.json"));
        write_new(
            &path,
            &serde_json::to_vec_pretty(&descriptor).map_err(|e| e.to_string())?,
        )?;
        Ok(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn fresh_work_requires_exact_native_feature() {
        assert!(
            require_native_support(&json!({"providerContinuityAdmission":"exact-height-v1"}))
                .is_ok()
        );
        for value in [
            json!({}),
            json!({"providerContinuityAdmission":true}),
            json!({"providerContinuityAdmission":"v1"}),
        ] {
            assert!(require_native_support(&value).is_err());
        }
    }
    fn source_fixture() -> (Authority, HeldCharge, Value) {
        let authority = Authority {
            task: "104".into(),
            subject: "9".into(),
            capability: "103".into(),
            query_capability: "103".into(),
            custody_key: "/fixture.key".into(),
        };
        let hold: HeldCharge = serde_json::from_value(json!({"reserve":"3","charge":"3",
            "beforeGeneration":"1","beforeTargetRoot":"100","reserveAttempt":"/attempt",
            "reserveConfirmed":true,"reserveRefused":false,"reserveBoundary":"200"}))
        .unwrap();
        let observed = json!({"targetRoot":"300","grain":{"generation":"1","status":"3",
            "remaining":"9","reserved":"3","route":"3"}});
        let identity = grain_source::operation_id("101", &authority.task, &authority.subject, 7);
        let source = grain_source::source(
            &authority,
            &observed,
            grain_source::Transition {
                identity: &identity,
                payload: "parent hard connection lost",
                operation: json!({"type":"disconnect"}),
                publications: vec![],
                parent_witness: None,
                grants: grain_observation_grants(&authority, None, &[]).unwrap(),
            },
        )
        .unwrap();
        (authority, hold, source)
    }
    #[test]
    fn exact_fence_source_rejects_other_controller_provider_or_action() {
        let (authority, hold, source) = source_fixture();
        assert!(validate_fence_source("101", &authority, 7, &hold, "homelab", &source).is_ok());
        // Real metering pins name the route; legacy numeric strings cannot
        // accidentally bypass the declared route conversion.
        assert!(validate_fence_source("101", &authority, 7, &hold, "3", &source).is_err());
        assert!(validate_fence_source("101", &authority, 7, &hold, "pool", &source).is_err());
        for (name, code) in [("user", "1"), ("pool", "2"), ("homelab", "3")] {
            let mut observed = source.clone();
            observed["grain"]["before"]["route"] = json!(code);
            assert!(validate_fence_source("101", &authority, 7, &hold, name, &observed).is_ok());
        }

        assert!(validate_fence_source("102", &authority, 7, &hold, "homelab", &source).is_err());
        assert!(validate_fence_source("101", &authority, 8, &hold, "homelab", &source).is_err());
        for (pointer, value) in [
            ("/grain/task", json!("105")),
            ("/grain/subject", json!("19")),
            ("/grain/operation/type", json!("settle")),
            ("/grain/before/generation", json!("2")),
            ("/grain/before/status", json!("1")),
            ("/grain/before/reserved", json!("4")),
            ("/grain/before/route", json!("2")),
            ("/grain/context/payload", json!("same-shaped foreign fence")),
            ("/grain/capability", json!("104")),
            ("/grain/context/operationId", json!("7")),
        ] {
            let mut changed = source.clone();
            *changed.pointer_mut(pointer).unwrap() = value;
            assert!(
                validate_fence_source("101", &authority, 7, &hold, "homelab", &changed).is_err(),
                "{pointer}"
            );
        }
        let mut changed = source.clone();
        changed["unrecognized"] = json!(true);
        assert!(validate_fence_source("101", &authority, 7, &hold, "homelab", &changed).is_err());
    }
    #[test]
    fn legacy_fence_identity_requires_both_complete_old_fields() {
        let (authority, hold, mut source) = source_fixture();
        source["intentNonce"] = json!("7");
        source["grain"]["context"]["operationId"] = json!("7");
        assert!(validate_fence_source("101", &authority, 7, &hold, "homelab", &source).is_ok());
        source["grain"]["context"]["operationId"] = json!("8");
        assert!(validate_fence_source("101", &authority, 7, &hold, "homelab", &source).is_err());
    }
    #[test]
    fn fence_record_schema_rejects_extra_fields_and_bad_receipt() {
        let value = json!({"operationId":7,"attempt":"/attempt","sourceSha256":"s","callSha256":"c",
            "outcomePath":"/outcome.json","outcomeSha256":"o",
            "receipt":{"transactionId":"1","eventId":"2","acceptedCount":"3","worldRoot":"4"}});
        let record: Fence = serde_json::from_value(value.clone()).unwrap();
        assert_eq!(prefix(&record.receipt)["acceptedCount"], "3");
        let mut changed = value;
        changed["differentRequest"] = json!(true);
        assert!(serde_json::from_value::<Fence>(changed).is_err());
        assert!(ReserveAnchor::from_confirmed(&json!({"type":"refused"})).is_err());
    }
}

#[cfg(test)]
mod reserve_origin_tests {
    use super::*;

    fn fixture() -> (Runtime, PathBuf, PathBuf) {
        // Only native-client receipt bytes are controlled here; exercise the
        // real reserve marker, journal and continuity descriptor consumers.
        let (mut runtime, root) = crate::publication_refusal_tests::fixture(false, false, false);
        runtime.config.provider_task = Some(serde_json::from_value(json!({
            "task":"7103","subject":"9","capability":"103","queryCapability":"103",
            "custodyKey":root.join("provider.key"),"parentCapability":"105",
            "parentObserveCapability":"105","reserve":"3","maxInputTokens":1000,
            "maxOutputTokens":100,"model":"fixture-model","providers":root.join("providers.json"),
            "credentialBroker":root.join("keys-client.json"),
            "gatewayBind":"127.0.0.1:0","maxRequestBytes":65536,"maxResponseBytes":65536,
            "timeoutSeconds":60
        })).unwrap());
        let attempt = runtime.config.state_dir.join("attempt-0000000000000019");
        fs::create_dir(&attempt).unwrap();
        fs::write(attempt.join("intent.json"), br#"{"source":"native reserve"}"#).unwrap();
        fs::write(attempt.join("call.bin"), b"exact signed reserve call").unwrap();
        fs::write(attempt.join("outcome.bin"), b"exact native reserve receipt").unwrap();
        fs::write(attempt.join("outcome.json"), br#"{"type":"confirmed","confirmation":"installed","transactionId":"11","eventId":"12","acceptedCount":"13","worldRoot":"300"}"#).unwrap();
        runtime.journal.provider_hold = Some(HeldCharge {
            reserve:"3".into(), charge:"0".into(), before_generation:"1".into(),
            before_target_root:"100".into(), reserve_attempt:Some(attempt.clone()),
            reserve_confirmed:false, reserve_refused:false, reserve_boundary:None,
            reserve_call_sha256:None, reserve_source_sha256:None, reserve_outcome_path:None,
            reserve_outcome_sha256:None, reserve_anchor:None,
        });
        (runtime, root, attempt)
    }

    #[test]
    fn normal_provider_reserve_pins_intent_before_historical_settlement() {
        let (mut runtime, root, attempt) = fixture();
        runtime.record_reserve_confirmation(AuthoritySlot::Provider, &attempt, &attempt.join("outcome.json")).unwrap();
        let source = sha256_file(&attempt.join("intent.json")).unwrap();
        assert_eq!(runtime.journal.provider_hold.as_ref().unwrap().reserve_source_sha256.as_deref(), Some(source.as_str()));
        runtime.save().unwrap();
        let durable: Value = serde_json::from_slice(&fs::read(runtime.config.state_dir.join("journal.json")).unwrap()).unwrap();
        assert_eq!(durable["providerHold"]["reserveSourceSha256"], source);
        let descriptor = runtime.provider_continuity_value().unwrap();
        assert_eq!(descriptor["providerResourceId"], "7103");
        assert_eq!(descriptor["reserve"]["receipt"]["transactionId"], "11");
        fs::write(attempt.join("intent.json"), b"tampered after confirmation").unwrap();
        assert!(runtime.provider_continuity_value().unwrap_err().contains("differs from confirmed source"));
        drop(runtime); fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn normal_provider_missing_intent_never_publishes_confirmed_marker() {
        let (mut runtime, root, attempt) = fixture();
        fs::remove_file(attempt.join("intent.json")).unwrap();
        assert!(runtime.record_reserve_confirmation(AuthoritySlot::Provider, &attempt, &attempt.join("outcome.json")).is_err());
        let hold = runtime.journal.provider_hold.as_ref().unwrap();
        assert!(!hold.reserve_confirmed);
        assert!(hold.reserve_source_sha256.is_none());
        assert_eq!(hold.reserve_attempt.as_deref(), Some(attempt.as_path()));
        drop(runtime); fs::remove_dir_all(root).unwrap();
    }
}
