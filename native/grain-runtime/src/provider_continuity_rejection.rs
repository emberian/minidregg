//! Positive Mini control-flow evidence for a rejected continuity gate. This
//! verifier never submits, retries, changes Pending, or releases an allowance.
//! The caller must supply fresh physical proof that the old Mini sender stopped.
use super::*;

const FRAME_MAX: usize = 12_102_760;
const MARKER: &str = "provider-continuity-rejection.json";
const LATE: [&str; 5] = [
    "call.bin",
    "transaction-signatures.bin",
    "transaction-signatures.json",
    "outcome.bin",
    "outcome.json",
];

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
struct Binding {
    path: String,
    sha256: String,
}
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Marker {
    #[serde(rename = "type")]
    kind: String,
    stage: String,
    held_allowance_released: bool,
    reason: String,
    intent: Binding,
    config: Binding,
    manifest: Binding,
    descriptor: Binding,
    original_plan: Binding,
    original_plan_presentation: Binding,
}
#[derive(Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub(super) struct VerifiedRejection {
    #[serde(rename = "type")]
    kind: &'static str,
    operation_id: String,
    operation: String,
    attempt: PathBuf,
    marker_sha256: String,
    held_allowance_released: bool,
    marker: Marker,
}
fn private_owned(path: &Path, directory: bool) -> Result<()> {
    let stat =
        fs::symlink_metadata(path).map_err(|e| format!("continuity rejection custody: {e}"))?;
    if (directory && !stat.file_type().is_dir())
        || (!directory && !stat.file_type().is_file())
        || stat.uid() != unsafe { libc::geteuid() }
        || stat.mode() & 0o077 != 0
    {
        return Err("continuity rejection custody must be owned private regular data".into());
    }
    Ok(())
}
fn read(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let named = fs::symlink_metadata(path)
        .map_err(|e| format!("continuity rejection input {}: {e}", path.display()))?;
    if !named.file_type().is_file()
        || named.len() > limit as u64
        || (named.uid() != 0 && named.uid() != unsafe { libc::geteuid() })
    {
        return Err("continuity rejection input is not owned bounded regular data".into());
    }
    let file = File::open(path).map_err(|e| e.to_string())?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if !opened.is_file() || (named.dev(), named.ino()) != (opened.dev(), opened.ino()) {
        return Err("continuity rejection input changed while opening".into());
    }
    let mut bytes = Vec::new();
    file.take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err("continuity rejection input exceeds bounds".into());
    }
    Ok(bytes)
}
fn absent_late(attempt: &Path) -> Result<()> {
    for name in LATE {
        match fs::symlink_metadata(attempt.join(name)) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Ok(_) => {
                return Err(format!(
                    "continuity rejection has possible later artifact {name}"
                ))
            }
            Err(e) => return Err(format!("cannot prove {name} absent: {e}")),
        }
    }
    Ok(())
}
fn bound(attempt: &Path, binding: &Binding, name: &str, limit: usize) -> Result<Vec<u8>> {
    if binding.path != name
        || binding.sha256.len() != 64
        || !binding
            .sha256
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("continuity rejection binding has unexpected path or digest".into());
    }
    let bytes = read(&attempt.join(name), limit)?;
    if sha256_bytes(&bytes)? != binding.sha256 {
        return Err(format!("continuity rejection {name} changed"));
    }
    Ok(bytes)
}
fn verify_bindings(config: &Config, pending: &Pending, marker: &Marker) -> Result<()> {
    let provider = config
        .provider_task
        .as_ref()
        .ok_or("continuity rejection has no configured provider")?;
    if pending.publication.is_some()
        || pending.attempt
            != config
                .state_dir
                .join(format!("attempt-{:016}", pending.operation_id))
    {
        return Err("continuity rejection attempt differs from current Pending".into());
    }
    private_owned(&pending.attempt, true)?;
    private_owned(&pending.attempt.join("provider-continuity"), true)?;
    private_owned(&pending.attempt.join(MARKER), false)?;
    absent_late(&pending.attempt)?;
    if marker.kind != "minidregg-provider-continuity-rejection-v1"
        || marker.stage != "before-signing"
        || marker.held_allowance_released
        || marker.reason != "continuity-gate-rejected"
    {
        return Err("continuity rejection marker has the wrong contract".into());
    }
    let intent = bound(&pending.attempt, &marker.intent, "intent.json", FRAME_MAX)?;
    let copied_config = bound(&pending.attempt, &marker.config, "config.json", 65_536)?;
    let manifest = bound(&pending.attempt, &marker.manifest, "attempt.json", 65_536)?;
    let descriptor = bound(
        &pending.attempt,
        &marker.descriptor,
        "provider-continuity/descriptor.json",
        16_384,
    )?;
    bound(
        &pending.attempt,
        &marker.original_plan,
        "original-plan.bin",
        FRAME_MAX,
    )?;
    bound(
        &pending.attempt,
        &marker.original_plan_presentation,
        "original-plan.json",
        4 * FRAME_MAX,
    )?;
    if intent
        != read(
            &config
                .state_dir
                .join(format!("source-{:016}.json", pending.operation_id)),
            FRAME_MAX,
        )?
        || descriptor
            != read(
                &config.state_dir.join(format!(
                    "provider-continuity-source-{:016}.json",
                    pending.operation_id
                )),
                16_384,
            )?
        || copied_config != read(&config.host_config, 65_536)?
    {
        return Err(
            "continuity rejection differs from controller source or operator config".into(),
        );
    }
    let manifest: Value = serde_json::from_slice(&manifest)
        .map_err(|e| format!("continuity rejection manifest: {e}"))?;
    if config.host_socket.is_none()
        || manifest["format"] != "minidregg-resource-client-attempt-v1"
        || manifest["operation"] != "submit"
        || manifest["host"].as_str().map(Path::new) != Some(config.host.as_path())
        || manifest["config"].as_str().map(Path::new)
            != Some(pending.attempt.join("config.json").as_path())
        || manifest["socket"].as_str().map(Path::new) != config.host_socket.as_deref()
    {
        return Err("continuity rejection manifest differs from pinned Host submission".into());
    }
    let source: Value =
        serde_json::from_slice(&intent).map_err(|e| format!("continuity rejection source: {e}"))?;
    verify_source(config, pending, &source)?;
    let descriptor: Value = serde_json::from_slice(&descriptor)
        .map_err(|e| format!("continuity rejection descriptor: {e}"))?;
    if descriptor["type"] != "mini-provider-continuity-v1"
        || descriptor["providerResourceId"] != provider.task
    {
        return Err("continuity rejection descriptor names another provider".into());
    }
    Ok(())
}
/// Full source-owned constructor equality, shared by positive before-signing
/// rejection and expired-contention recovery. Numeric identity alone is never
/// enough to authorize retirement of a pending operation.
pub(super) fn verify_source(config: &Config, pending: &Pending, source: &Value) -> Result<()> {
    let provider = config
        .provider_task
        .as_ref()
        .ok_or("continuity source has no configured provider")?;
    let operation = match pending.operation.as_str() {
        "provider settle" | "provider recovery settle" => "settle",
        "provider disconnect" => "disconnect",
        _ => return Err("continuity source is not a guarded provider transition".into()),
    };
    let identity = grain_source::operation_id(
        &config.task,
        &provider.task,
        &provider.subject,
        pending.operation_id,
    );
    if source["intentNonce"].as_str() != Some(&identity)
        || source
            .pointer("/grain/context/operationId")
            .and_then(Value::as_str)
            != Some(&identity)
        || source["grain"]["task"] != provider.task
        || source["grain"]["subject"] != provider.subject
        || source["grain"]["capability"] != provider.capability
        || source["grain"]["observeCapability"] != provider.query_capability
        || source["grain"]["operation"]["type"] != operation
        || source["grain"]["publications"] != json!([])
        || source["grain"].get("parentWitness").is_some()
        || (operation == "disconnect" && source["grain"]["before"]["status"] != "3")
    {
        return Err("continuity rejection intent differs from pending provider identity".into());
    }
    let payload = match pending.operation.as_str() {
        "provider settle" => "gateway source-quoted provider settlement",
        "provider recovery settle" => "recovered delivered source-quoted provider charge",
        "provider disconnect" => "parent hard connection lost",
        _ => unreachable!(),
    };
    let operation = if operation == "disconnect" {
        json!({"type":"disconnect"})
    } else {
        let charge = source
            .pointer("/grain/operation/charge")
            .and_then(Value::as_str)
            .ok_or("continuity rejection settlement charge absent")?;
        let route = source
            .pointer("/grain/operation/route")
            .and_then(Value::as_str)
            .ok_or("continuity rejection settlement route absent")?;
        decimal(charge, "continuity rejection charge")?;
        if !matches!(route, "user" | "pool" | "homelab") {
            return Err("continuity rejection settlement route is unknown".into());
        }
        json!({"type":"settle","charge":charge,"route":route})
    };
    let authority = Authority {
        task: provider.task.clone(),
        subject: provider.subject.clone(),
        capability: provider.capability.clone(),
        query_capability: provider.query_capability.clone(),
        custody_key: provider.custody_key.clone(),
    };
    let before = source
        .pointer("/grain/before")
        .ok_or("continuity rejection pre-state absent")?;
    let target = source
        .pointer("/grain/expectedTargetRoot")
        .ok_or("continuity rejection target root absent")?;
    let observed = json!({"grain":before,"targetRoot":target});
    let expected = grain_source::source(
        &authority,
        &observed,
        grain_source::Transition {
            identity: &identity,
            payload,
            operation,
            publications: vec![],
            parent_witness: None,
            grants: grain_observation_grants(&authority, None, &[])?,
        },
    )?;
    if source != &expected {
        return Err("continuity rejection is not the complete pending provider transition".into());
    }
    Ok(())
}
/// The proof callback must inspect the actual custody sender, including any
/// escaped descendants; a stopped worker alone does not suffice. It runs both
/// before observation and before final revalidation. `uncertain` is deliberately
/// not a veto: Mini errors set that bit before this positive evidence is read.
/// None means no marker, never permission to retire Pending or a hold.
pub(super) fn inspect(
    config: &Config,
    pending: &Pending,
    mut prove_sender_stopped: impl FnMut() -> Result<()>,
) -> Result<Option<VerifiedRejection>> {
    let path = pending.attempt.join(MARKER);
    match fs::symlink_metadata(&path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(format!("continuity rejection marker stat: {e}")),
        Ok(_) => {}
    }
    prove_sender_stopped()?;
    let bytes = read(&path, 65_536)?;
    let marker: Marker =
        serde_json::from_slice(&bytes).map_err(|e| format!("continuity rejection marker: {e}"))?;
    verify_bindings(config, pending, &marker)?;
    prove_sender_stopped()?;
    if read(&path, 65_536)? != bytes {
        return Err("continuity rejection marker changed during inspection".into());
    }
    verify_bindings(config, pending, &marker)?;
    absent_late(&pending.attempt)?;
    Ok(Some(VerifiedRejection {
        kind: "minidregg-verified-provider-continuity-rejection-v1",
        operation_id: pending.operation_id.to_string(),
        operation: pending.operation.clone(),
        attempt: pending.attempt.clone(),
        marker_sha256: sha256_bytes(&bytes)?,
        held_allowance_released: false,
        marker,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::env;
    use std::os::unix::fs::PermissionsExt;
    use std::time::{SystemTime, UNIX_EPOCH};
    fn fixture() -> (PathBuf, Config, Pending) {
        let root = env::temp_dir().join(format!(
            "grain-continuity-rejection-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::create_dir(&root).unwrap();
        let config:Config=serde_json::from_value(json!({"mini":root.join("mini"),"host":root.join("host"),"hostConfig":root.join("host.json"),"hostSocket":root.join("host.sock"),"controlSocket":root.join("control.sock"),"custodyKey":root.join("unused.key"),"stateDir":root,"cwd":root,"task":"10","subject":"7","capability":"71","queryCapability":"72","commands":[],
        "providerTask":{"task":"14","subject":"9","capability":"91","queryCapability":"92","custodyKey":root.join("provider-unused.key"),"parentCapability":"71","parentObserveCapability":"72","reserve":"30","maxInputTokens":10,"maxOutputTokens":10,"model":"fixture","providers":root.join("providers.json"),"credentialsRoot":root.join("credentials"),"credentialsKey":root.join("credentials.key"),"gatewayBind":"127.0.0.1:0","maxRequestBytes":4096,"maxResponseBytes":4096,"timeoutSeconds":10}})).unwrap();
        fs::write(&config.host_config, b"exact pinned config").unwrap();
        let pending = Pending {
            operation_id: 17,
            operation: "provider settle".into(),
            attempt: root.join("attempt-0000000000000017"),
            uncertain: true,
            publication: None,
        };
        fs::create_dir(&pending.attempt).unwrap();
        fs::set_permissions(&pending.attempt, fs::Permissions::from_mode(0o700)).unwrap();
        fs::create_dir(pending.attempt.join("provider-continuity")).unwrap();
        fs::set_permissions(
            pending.attempt.join("provider-continuity"),
            fs::Permissions::from_mode(0o700),
        )
        .unwrap();
        let authority = Authority {
            task: "14".into(),
            subject: "9".into(),
            capability: "91".into(),
            query_capability: "92".into(),
            custody_key: root.join("provider-unused.key"),
        };
        let observed = json!({"targetRoot":"100","grain":{"generation":"1","status":"3","remaining":"70","reserved":"30","route":"2"}});
        let identity = grain_source::operation_id("10", "14", "9", 17);
        let source = grain_source::source(
            &authority,
            &observed,
            grain_source::Transition {
                identity: &identity,
                payload: "gateway source-quoted provider settlement",
                operation: json!({"type":"settle","charge":"3","route":"homelab"}),
                publications: vec![],
                parent_witness: None,
                grants: grain_observation_grants(&authority, None, &[]).unwrap(),
            },
        )
        .unwrap();
        let source = serde_json::to_vec(&source).unwrap();
        fs::write(root.join("source-0000000000000017.json"), &source).unwrap();
        fs::write(pending.attempt.join("intent.json"), source).unwrap();
        let descriptor=serde_json::to_vec(&json!({"type":"mini-provider-continuity-v1","providerResourceId":"14","reserve":{},"fence":null})).unwrap();
        fs::write(
            root.join("provider-continuity-source-0000000000000017.json"),
            &descriptor,
        )
        .unwrap();
        fs::write(
            pending.attempt.join("provider-continuity/descriptor.json"),
            descriptor,
        )
        .unwrap();
        fs::copy(&config.host_config, pending.attempt.join("config.json")).unwrap();
        fs::write(pending.attempt.join("attempt.json"),serde_json::to_vec(&json!({"format":"minidregg-resource-client-attempt-v1","operation":"submit","host":config.host,"config":pending.attempt.join("config.json"),"socket":config.host_socket})).unwrap()).unwrap();
        fs::write(
            pending.attempt.join("original-plan.bin"),
            b"opaque native original plan",
        )
        .unwrap();
        fs::write(
            pending.attempt.join("original-plan.json"),
            b"opaque original native inspection",
        )
        .unwrap();
        refresh_marker(&pending);
        (root, config, pending)
    }
    fn refresh_marker(pending: &Pending) {
        let b = |name: &str| Binding {
            path: name.into(),
            sha256: sha256_bytes(&fs::read(pending.attempt.join(name)).unwrap()).unwrap(),
        };
        let marker = Marker {
            kind: "minidregg-provider-continuity-rejection-v1".into(),
            stage: "before-signing".into(),
            held_allowance_released: false,
            reason: "continuity-gate-rejected".into(),
            intent: b("intent.json"),
            config: b("config.json"),
            manifest: b("attempt.json"),
            descriptor: b("provider-continuity/descriptor.json"),
            original_plan: b("original-plan.bin"),
            original_plan_presentation: b("original-plan.json"),
        };
        fs::write(
            pending.attempt.join(MARKER),
            serde_json::to_vec(&marker).unwrap(),
        )
        .unwrap();
        fs::set_permissions(
            pending.attempt.join(MARKER),
            fs::Permissions::from_mode(0o600),
        )
        .unwrap();
    }
    #[test]
    fn positive_evidence_binds_current_uncertain_pending_and_keeps_hold() {
        let (root, config, pending) = fixture();
        let mut calls = 0;
        let evidence = inspect(&config, &pending, || {
            calls += 1;
            Ok(())
        })
        .unwrap()
        .unwrap();
        assert_eq!(calls, 2);
        let value = serde_json::to_value(evidence).unwrap();
        assert_eq!(value["operationId"], "17");
        assert_eq!(value["heldAllowanceReleased"], false);
        assert!(pending.uncertain);
        assert!(!pending.attempt.join("call.bin").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn absent_marker_never_classifies_and_failed_stop_never_verifies() {
        let (root, config, pending) = fixture();
        assert!(inspect(&config, &pending, || Err("sender still running".into())).is_err());
        fs::remove_file(pending.attempt.join(MARKER)).unwrap();
        assert!(inspect(&config, &pending, || Err(
            "unrelated sender proof is not consumed without a marker".into()
        ))
        .unwrap()
        .is_none());
        std::os::unix::fs::symlink(root.join("missing"), pending.attempt.join(MARKER)).unwrap();
        assert!(inspect(&config, &pending, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn changed_retained_or_controller_inputs_never_verify() {
        for name in [
            "intent.json",
            "config.json",
            "attempt.json",
            "provider-continuity/descriptor.json",
            "original-plan.bin",
            "original-plan.json",
        ] {
            let (root, config, pending) = fixture();
            fs::write(pending.attempt.join(name), b"changed").unwrap();
            assert!(inspect(&config, &pending, || Ok(())).is_err(), "{name}");
            fs::remove_dir_all(root).unwrap();
        }
        for name in [
            "source-0000000000000017.json",
            "provider-continuity-source-0000000000000017.json",
            "host.json",
        ] {
            let (root, config, pending) = fixture();
            fs::write(root.join(name), b"changed").unwrap();
            assert!(inspect(&config, &pending, || Ok(())).is_err(), "{name}");
            fs::remove_dir_all(root).unwrap();
        }
    }
    #[test]
    fn another_pending_or_modified_full_source_cannot_use_marker() {
        let (root, config, pending) = fixture();
        let mut other = pending.clone();
        other.operation_id += 1;
        assert!(inspect(&config, &other, || Ok(())).is_err());
        other = pending.clone();
        other.operation = "provider reserve".into();
        assert!(inspect(&config, &other, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();
        for pointer in [
            "/intentNonce",
            "/grain/context/payload",
            "/grain/schemaVersion",
            "/grain/operation/type",
            "/grain/capability",
        ] {
            let (root, config, pending) = fixture();
            let mut source: Value =
                serde_json::from_slice(&fs::read(pending.attempt.join("intent.json")).unwrap())
                    .unwrap();
            *source.pointer_mut(pointer).unwrap() = json!("999");
            let bytes = serde_json::to_vec(&source).unwrap();
            fs::write(root.join("source-0000000000000017.json"), &bytes).unwrap();
            fs::write(pending.attempt.join("intent.json"), bytes).unwrap();
            refresh_marker(&pending);
            assert!(inspect(&config, &pending, || Ok(())).is_err(), "{pointer}");
            fs::remove_dir_all(root).unwrap();
        }
    }
    #[test]
    fn late_artifacts_including_dangling_paths_and_sender_race_refuse() {
        for name in LATE {
            for dangling in [false, true] {
                let (root, config, pending) = fixture();
                if dangling {
                    std::os::unix::fs::symlink(root.join("missing"), pending.attempt.join(name))
                        .unwrap();
                } else {
                    fs::write(pending.attempt.join(name), b"possible signed call").unwrap();
                }
                assert!(inspect(&config, &pending, || Ok(())).is_err(), "{name}");
                fs::remove_dir_all(root).unwrap();
            }
        }
        let (root, config, pending) = fixture();
        let mut calls = 0;
        assert!(inspect(&config, &pending, || {
            calls += 1;
            if calls == 2 {
                fs::write(pending.attempt.join("call.bin"), b"late sender").unwrap();
            }
            Ok(())
        })
        .is_err());
        assert_eq!(calls, 2);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn marker_contract_paths_duplicates_and_post_proof_tampering_refuse() {
        let (root, config, pending) = fixture();
        let original = fs::read_to_string(pending.attempt.join(MARKER)).unwrap();
        let duplicate = original.replacen("{", r#"{"stage":"before-signing","#, 1);
        fs::write(pending.attempt.join(MARKER), duplicate).unwrap();
        assert!(inspect(&config, &pending, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();

        for field in ["heldAllowanceReleased", "reason", "stage", "extra"] {
            let (root, config, pending) = fixture();
            let mut marker: Value =
                serde_json::from_slice(&fs::read(pending.attempt.join(MARKER)).unwrap()).unwrap();
            marker[field] = json!(true);
            fs::write(
                pending.attempt.join(MARKER),
                serde_json::to_vec(&marker).unwrap(),
            )
            .unwrap();
            assert!(inspect(&config, &pending, || Ok(())).is_err());
            fs::remove_dir_all(root).unwrap();
        }
        let (root, config, pending) = fixture();
        let mut marker: Value =
            serde_json::from_slice(&fs::read(pending.attempt.join(MARKER)).unwrap()).unwrap();
        marker["intent"]["path"] = json!("../source-0000000000000017.json");
        fs::write(
            pending.attempt.join(MARKER),
            serde_json::to_vec(&marker).unwrap(),
        )
        .unwrap();
        assert!(inspect(&config, &pending, || Ok(())).is_err());
        fs::remove_dir_all(root).unwrap();
        let (root, config, pending) = fixture();
        let mut calls = 0;
        assert!(inspect(&config, &pending, || {
            calls += 1;
            if calls == 2 {
                fs::write(
                    pending.attempt.join("original-plan.bin"),
                    b"changed after proof",
                )
                .unwrap();
            }
            Ok(())
        })
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
