//! Durable custody for one explicitly source-authorized selected article.
//! Lean owns selection, source-law admission, and exact ingress/article equality.
//! This client retains those bytes and moves them across the protected fn POST.
use super::*;
use sha2::{Digest, Sha256};
use std::os::unix::fs::DirBuilderExt;

fn bounded(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    File::open(path)
        .map_err(|e| format!("cannot open {}: {e}", path.display()))?
        .take((limit + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    if bytes.is_empty() || bytes.len() > limit {
        return Err(format!("{} must contain 1..={limit} bytes", path.display()));
    }
    Ok(bytes)
}


/// The only source-envelope signer. Host selects the current source page and
/// canonical `.delegateObject` header from the exact owner packet; custody
/// signs those returned bytes and asks Host to assemble the native envelope.
pub(super) fn sign_source(
    host: &Path,
    config: &Path,
    packet_path: &Path,
    capability: &str,
    key: &Path,
    directory: &Path,
) -> Result<()> {
    if SOCKET.get().is_some() {
        return Err("selected source signer requires direct source Host validation".into());
    }
    if !mini_sdk::decimal::is_canonical_max(capability, 80)
    {
        return Err("source delegate capability must be canonical decimal".into());
    }
    let packet = bounded(packet_path, 1_048_576)?;
    let signing = crate::read_secret(key)?;
    let host = absolute(host)?;
    let config = absolute(config)?;
    let directory = absolute(directory)?;
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&directory)
        .map_err(|e| format!("cannot create new selected source signing directory: {e}"))?;
    sync_directory_ancestors(&directory)?;
    let packet_file = directory.join("packet.bin");
    create_private(&packet_file, &packet)?;
    let spec = directory.join("spec.bin");
    let header = directory.join("header.bin");
    let root = directory.join("source-root.txt");
    process(
        &host,
        &config,
        &[
            OsStr::new("selected-release-source-plan"),
            packet_file.as_os_str(),
            OsStr::new(capability),
            spec.as_os_str(),
            header.as_os_str(),
            root.as_os_str(),
        ],
    )?;
    let header_bytes = bounded(&header, 65_536)?;
    let signature = directory.join("signature.bin");
    create_private(&signature, &signing.sign(&header_bytes).to_bytes())?;
    sync_directory_ancestors(&directory)?;
    let ingress = directory.join("ingress.bin");
    process(
        &host,
        &config,
        &[
            OsStr::new("selected-release-source-assemble"),
            spec.as_os_str(),
            header.as_os_str(),
            signature.as_os_str(),
            ingress.as_os_str(),
        ],
    )?;
    let ingress_bytes = bounded(&ingress, transport::HOST_MAX_FRAME - 1)?;
    let config_bytes = bounded(&config, 65_536)?;
    durable_json(
        &directory.join("pin.json"),
        &json!({"type":"minidregg-selected-source-sign-v1",
            "host":utf8_path(&host)?,"hostSha256":host_image_sha256(&host)?,
            "configPath":utf8_path(&config)?,"configSha256":digest(&config_bytes),
            "packetSha256":digest(&packet),"delegateCapability":capability,
            "signerPublicKey":hex(&signing.verifying_key().to_bytes()),
            "headerSha256":digest(&header_bytes),"ingressSha256":digest(&ingress_bytes)}),
    )
}

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&bounded(path, 65_536)?).map_err(|e| format!("{}: {e}", path.display()))
}

fn durable_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(
        path.parent()
            .ok_or("selected publisher state has no parent")?,
    )
}

fn confirmed(value: &Value) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Err("selected source publication is not confirmed".into());
    }
    for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        let number = value
            .get(field)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("selected source receipt lacks {field}"))?;
        if !mini_sdk::decimal::is_canonical_max(number, 80)
        {
            return Err(format!("selected source receipt has noncanonical {field}"));
        }
    }
    Ok(())
}

fn host_route(
    host: &Path,
    config: &Path,
    command: &str,
    input: &Path,
    output: &Path,
) -> Result<()> {
    process(
        host,
        config,
        &[OsStr::new(command), input.as_os_str(), output.as_os_str()],
    )?;
    if !output.is_file() {
        return Err(format!("{command} did not retain an outcome"));
    }
    sync_directory_ancestors(output.parent().ok_or("source outcome has no parent")?)
}

fn inspect_outcome(host: &Path, config: &Path, binary: &Path, json_path: &Path) -> Result<Value> {
    if json_path.exists() {
        let value = read_json(json_path)?;
        // The retained JSON is a presentation; re-decode the binary with the
        // pinned source Host on each resumption before trusting confirmation.
        let replay = (0..1000)
            .map(|index| json_path.with_extension(format!("reinspect-{index:03}.json")))
            .find(|path| !path.exists())
            .ok_or("selected source outcome reinspection names exhausted")?;
        let checked = inspect(host, config, "outcome", binary, &replay)?;
        if checked != value {
            return Err("selected source retained outcome presentation changed".into());
        }
        return Ok(checked);
    }
    inspect(host, config, "outcome", binary, json_path)
}

#[derive(Debug, Eq, PartialEq)]
enum SourceAction {
    Submit,
    InspectSubmitted,
    Lookup,
}

fn source_action(marker: bool, submitted: bool) -> Result<SourceAction> {
    match (marker, submitted) {
        (false, false) => Ok(SourceAction::Submit),
        (true, true) => Ok(SourceAction::InspectSubmitted),
        (true, false) => Ok(SourceAction::Lookup),
        (false, true) => {
            Err("selected source outcome lacks preceding durable submit marker".into())
        }
    }
}

fn source_receipt(host: &Path, config: &Path, state: &Path) -> Result<Value> {
    let ingress = state.join("ingress.bin");
    let submitted = state.join("source-submit.bin");
    let marker = state.join("source-submit-attempt.json");
    let ingress_hash = digest(&bounded(&ingress, transport::HOST_MAX_FRAME - 1)?);
    if marker.exists() {
        let marker_value = read_json(&marker)?;
        if marker_value.get("type").and_then(Value::as_str)
            != Some("minidregg-selected-source-submit-attempt-v1")
            || marker_value.get("ingressSha256").and_then(Value::as_str)
                != Some(ingress_hash.as_str())
        {
            return Err("selected source submit marker differs from exact ingress".into());
        }
    }
    match source_action(marker.exists(), submitted.exists())? {
        SourceAction::InspectSubmitted => {
            // Even a retained but truncated/refused/uncertain submit outcome
            // cannot prove absence. Keep it and use exact read-only lookup.
            if let Ok(result) =
                inspect_outcome(host, config, &submitted, &state.join("source-submit.json"))
            {
                if confirmed(&result).is_ok() {
                    return Ok(result);
                }
            }
        }
        SourceAction::Submit => {
            durable_json(
                &marker,
                &json!({"type":"minidregg-selected-source-submit-attempt-v1",
                "ingressSha256":ingress_hash}),
            )?;
            // This call may install even if its response is lost. A subsequent
            // entry performs only exact lookup; it never submits again on its own.
            host_route(
                host,
                config,
                "selected-source-publication-submit",
                &ingress,
                &submitted,
            )?;
            if let Ok(result) =
                inspect_outcome(host, config, &submitted, &state.join("source-submit.json"))
            {
                if confirmed(&result).is_ok() {
                    return Ok(result);
                }
            }
        }
        SourceAction::Lookup => {}
    }
    for index in 0..1000 {
        let binary = state.join(format!("source-lookup-{index:03}.bin"));
        let lookup_marker = state.join(format!("source-lookup-{index:03}.json"));
        let attempt = state.join(format!("source-lookup-{index:03}.attempt.json"));
        if attempt.exists() {
            let value = read_json(&attempt)?;
            if value.get("type").and_then(Value::as_str)
                != Some("minidregg-selected-source-lookup-v1")
                || value.get("ingressSha256").and_then(Value::as_str) != Some(ingress_hash.as_str())
            {
                return Err("selected source lookup marker differs from exact ingress".into());
            }
        } else if binary.exists() || lookup_marker.exists() {
            return Err("selected source lookup result lacks request marker".into());
        }
        if binary.exists() {
            if let Ok(result) = inspect_outcome(host, config, &binary, &lookup_marker) {
                if confirmed(&result).is_ok() {
                    return Ok(result);
                }
            }
            // A prior absent or malformed lookup does not prove a competing
            // exact submit cannot later settle. The next numbered lookup is
            // still read-only and cannot create a second source event.
            continue;
        }
        if !attempt.exists() {
            durable_json(
                &attempt,
                &json!({"type":"minidregg-selected-source-lookup-v1",
                    "ingressSha256":ingress_hash}),
            )?;
        }
        host_route(
            host,
            config,
            "selected-source-publication-lookup",
            &ingress,
            &binary,
        )?;
        let result = inspect_outcome(host, config, &binary, &lookup_marker)?;
        confirmed(&result).map_err(|_| {
            "selected source lookup did not confirm; exact ingress retained without resubmit"
                .to_owned()
        })?;
        return Ok(result);
    }
    Err("selected source lookup history exhausted".into())
}

fn verify_source_lookup(
    host: &Path,
    config: &Path,
    state: &Path,
    submitted_receipt: &Value,
) -> Result<()> {
    let ingress = state.join("ingress.bin");
    let expected_hash = digest(&bounded(&ingress, transport::HOST_MAX_FRAME - 1)?);
    for index in 0..1000 {
        let marker = state.join(format!("source-proof-lookup-{index:03}.attempt.json"));
        let binary = state.join(format!("source-proof-lookup-{index:03}.bin"));
        let presentation = state.join(format!("source-proof-lookup-{index:03}.json"));
        if marker.exists() {
            let value = read_json(&marker)?;
            if value.get("type").and_then(Value::as_str)
                != Some("minidregg-selected-source-proof-lookup-v1")
                || value.get("ingressSha256").and_then(Value::as_str)
                    != Some(expected_hash.as_str())
            {
                return Err("source proof lookup marker differs from exact ingress".into());
            }
        } else if binary.exists() || presentation.exists() {
            return Err("source proof lookup result lacks preceding marker".into());
        }
        let existing = binary.exists();
        if !existing {
            if !marker.exists() {
                durable_json(
                    &marker,
                    &json!({"type":"minidregg-selected-source-proof-lookup-v1",
                    "ingressSha256":expected_hash}),
                )?;
            }
            host_route(
                host,
                config,
                "selected-source-publication-lookup",
                &ingress,
                &binary,
            )?;
        }
        if let Ok(retained) = inspect_outcome(host, config, &binary, &presentation) {
            if confirmed(&retained).is_ok() {
                for field in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
                    if retained.get(field) != submitted_receipt.get(field) {
                        return Err(format!("exact source lookup changed {field}"));
                    }
                }
                return Ok(());
            }
        }
        if !existing {
            return Err("source proof lookup did not confirm; no fn POST attempted".into());
        }
    }
    Err("selected source proof lookup history exhausted".into())
}

fn accepted_post(value: &Value, receipt: &Value, article_hash: &str) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("minidregg-selected-fn-post-v1")
        || value.get("sourceReceipt") != Some(receipt)
        || value.get("articleSha256").and_then(Value::as_str) != Some(article_hash)
    {
        return Err("retained selected fn POST result differs from source receipt".into());
    }
    let status = value.get("status").and_then(Value::as_str);
    let detail = value.get("detail").and_then(Value::as_str);
    if !matches!(
        (status, detail),
        (Some("accepted"), Some("240 article received OK"))
            | (
                Some("already-stored"),
                Some("441 posting failed; this article is already stored here")
            )
    ) {
        return Err("selected fn POST has no exact accepted status line".into());
    }
    Ok(())
}

#[derive(Debug, Eq, PartialEq)]
enum PostAction {
    First,
    Accepted,
    Hold,
}

fn post_action(
    attempt: bool,
    result: Option<&Value>,
    receipt: &Value,
    article_hash: &str,
) -> Result<PostAction> {
    match (attempt, result) {
        (false, None) => Ok(PostAction::First),
        (true, None) => Ok(PostAction::Hold),
        (true, Some(value)) => {
            if accepted_post(value, receipt, article_hash).is_ok() {
                Ok(PostAction::Accepted)
            } else {
                Ok(PostAction::Hold)
            }
        }
        (false, Some(_)) => Err("selected fn POST result lacks preceding attempt marker".into()),
    }
}

fn validate_post_attempt(value: &Value, receipt: &Value, article_hash: &str) -> Result<()> {
    if value.get("type").and_then(Value::as_str) != Some("minidregg-selected-fn-post-attempt-v1")
        || value.get("sourceReceipt") != Some(receipt)
        || value.get("articleSha256").and_then(Value::as_str) != Some(article_hash)
    {
        return Err("retained selected fn POST attempt differs from source receipt".into());
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub(super) fn publish(
    host: &Path,
    config: &Path,
    ingress_path: &Path,
    article_path: &Path,
    state: &Path,
    post_config_path: &Path,
) -> Result<()> {
    if SOCKET.get().is_some() {
        return Err("selected publisher requires pinned direct source Host commands".into());
    }
    drain::private_dir(state)?;
    let _owner = transport::service_lock(&state.join("selected-publisher.lock"))?;
    let host = absolute(host)?;
    let config = absolute(config)?;
    let post = worker::post_config(post_config_path)?;
    let config_bytes = bounded(&config, 65_536)?;
    let post_bytes = bounded(post_config_path, 16_384)?;
    let ingress = bounded(ingress_path, transport::HOST_MAX_FRAME - 1)?;
    let article = bounded(article_path, 1_500_000)?;
    let pin = json!({"type":"minidregg-selected-publisher-pin-v1",
        "host":utf8_path(&host)?,"hostSha256":host_image_sha256(&host)?,
        "configPath":utf8_path(&config)?,"configSha256":digest(&config_bytes),
        "ingressSha256":digest(&ingress),"articleSha256":digest(&article),
        "postConfigPath":utf8_path(&absolute(post_config_path)?)?,
        "postConfigSha256":digest(&post_bytes),"fnPort":post.port,
        "fnCertificateSha256":digest(&post.cert_pem)});
    let pin_path = state.join("pin.json");
    if pin_path.exists() {
        if read_json(&pin_path)? != pin {
            return Err("selected publisher identity changed; retain state for review".into());
        }
    } else {
        durable_json(&pin_path, &pin)?;
    }
    for (name, bytes) in [("ingress.bin", &ingress), ("article.eml", &article)] {
        let path = state.join(name);
        if path.exists() {
            if fs::read(&path).map_err(|e| e.to_string())? != *bytes {
                return Err(format!("retained selected publisher {name} changed"));
            }
        } else {
            create_private(&path, bytes)?;
            sync_directory_ancestors(state)?;
        }
    }
    // This source-owned check binds the fn bytes to the exact signed packet
    // carried by the source ingress. It has no side effect and runs before op24.
    process(
        &host,
        &config,
        &[
            OsStr::new("selected-release-source-check"),
            state.join("ingress.bin").as_os_str(),
            state.join("article.eml").as_os_str(),
        ],
    )?;
    let receipt = source_receipt(&host, &config, state)?;
    verify_source_lookup(&host, &config, state, &receipt)?;
    let result_path = state.join("fn-post-result.json");
    let article_hash = digest(&article);
    let attempt = state.join("fn-post-attempt.json");
    if attempt.exists() {
        validate_post_attempt(&read_json(&attempt)?, &receipt, &article_hash)?;
    }
    let result = if result_path.exists() {
        Some(read_json(&result_path)?)
    } else {
        None
    };
    match post_action(attempt.exists(), result.as_ref(), &receipt, &article_hash)? {
        PostAction::Accepted => return Ok(()),
        PostAction::Hold => {
            return Err(
                "fn POST response unresolved; exact article retained, no automatic repost".into(),
            );
        }
        PostAction::First => {}
    }
    durable_json(
        &attempt,
        &json!({"type":"minidregg-selected-fn-post-attempt-v1",
        "sourceReceipt":receipt,"articleSha256":article_hash}),
    )?;
    let outcome = match worker::post_exact_carrier(&post, &article) {
        Ok(value) => value,
        Err(error) => worker::FnPostOutcome::TransportUncertain(error),
    };
    use worker::FnPostOutcome;
    let (status, detail) = match outcome {
        FnPostOutcome::Accepted(line) => ("accepted", line),
        FnPostOutcome::AlreadyStored(line) => ("already-stored", line),
        FnPostOutcome::Conflict(line) => ("conflict", line),
        FnPostOutcome::ExplicitUncertain(line) => ("explicit-uncertain", line),
        FnPostOutcome::Refused(line) => ("refused", line),
        FnPostOutcome::TransportUncertain(line) => ("transport-uncertain", line),
    };
    durable_json(
        &result_path,
        &json!({"type":"minidregg-selected-fn-post-v1",
        "sourceReceipt":receipt,"articleSha256":article_hash,
        "status":status,"detail":detail}),
    )?;
    let result = read_json(&result_path)?;
    accepted_post(&result, &receipt, &article_hash)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::PermissionsExt;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn scratch() -> PathBuf {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = PathBuf::from(format!(
            "/tmp/selected-source-recovery-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).unwrap();
        path
    }

    #[test]
    fn truncated_submit_reply_recovers_by_lookup_without_resubmit() {
        let state = scratch();
        let host = state.join("stub-host.sh");
        let config = state.join("config.json");
        fs::write(&config, b"{}\n").unwrap();
        fs::write(state.join("ingress.bin"), b"exact-source-ingress").unwrap();
        fs::write(&host, b"#!/bin/sh\nset -eu\nprintf '%s\\n' \"$2\" >> \"$1.calls\"\ncase \"$2\" in\n  selected-source-publication-submit) printf truncated > \"$4\" ;;\n  selected-source-publication-lookup) printf confirmed > \"$4\" ;;\n  inspect) case \"$4\" in *source-submit.bin) exit 1 ;; esac\n    printf '%s\\n' '{\"type\":\"confirmed\",\"transactionId\":\"1\",\"eventId\":\"2\",\"acceptedCount\":\"3\",\"worldRoot\":\"4\"}' > \"$5\" ;;\n  *) exit 9 ;;\nesac\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let first = source_receipt(&host, &config, &state).unwrap();
        confirmed(&first).unwrap();
        assert_eq!(
            fs::read(state.join("source-submit.bin")).unwrap(),
            b"truncated"
        );
        let second = source_receipt(&host, &config, &state).unwrap();
        assert_eq!(first, second);
        let calls = fs::read_to_string(state.join("config.json.calls")).unwrap();
        assert_eq!(
            calls.matches("selected-source-publication-submit").count(),
            1
        );
        assert_eq!(
            calls.matches("selected-source-publication-lookup").count(),
            1
        );
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn an_old_absent_lookup_does_not_block_later_read_only_confirmation() {
        let state = scratch();
        let host = state.join("stub-host.sh");
        let config = state.join("config.json");
        fs::write(&config, b"{}\n").unwrap();
        let ingress = b"exact-source-ingress";
        fs::write(state.join("ingress.bin"), ingress).unwrap();
        durable_json(
            &state.join("source-submit-attempt.json"),
            &json!({"type":"minidregg-selected-source-submit-attempt-v1",
                "ingressSha256":digest(ingress)}),
        )
        .unwrap();
        durable_json(
            &state.join("source-lookup-000.attempt.json"),
            &json!({"type":"minidregg-selected-source-lookup-v1",
                "ingressSha256":digest(ingress)}),
        )
        .unwrap();
        fs::write(state.join("source-lookup-000.bin"), b"absent").unwrap();
        fs::write(&host, b"#!/bin/sh\nset -eu\nprintf '%s\\n' \"$2\" >> \"$1.calls\"\ncase \"$2\" in\n  selected-source-publication-lookup) printf confirmed > \"$4\" ;;\n  inspect) case \"$4\" in *000.bin) printf '%s\\n' '{\"type\":\"absent\"}' > \"$5\" ;; *) printf '%s\\n' '{\"type\":\"confirmed\",\"transactionId\":\"1\",\"eventId\":\"2\",\"acceptedCount\":\"3\",\"worldRoot\":\"4\"}' > \"$5\" ;; esac ;;\n  *) exit 9 ;;\nesac\n").unwrap();
        fs::set_permissions(&host, fs::Permissions::from_mode(0o700)).unwrap();
        let receipt = source_receipt(&host, &config, &state).unwrap();
        confirmed(&receipt).unwrap();
        assert!(state.join("source-lookup-001.bin").exists());
        let calls = fs::read_to_string(state.join("config.json.calls")).unwrap();
        assert!(!calls.contains("selected-source-publication-submit"));
        assert_eq!(
            calls.matches("selected-source-publication-lookup").count(),
            1
        );
        fs::remove_dir_all(state).unwrap();
    }

    #[test]
    fn lost_source_or_post_reply_cannot_trigger_another_write() {
        assert_eq!(source_action(false, false).unwrap(), SourceAction::Submit);
        assert_eq!(source_action(true, false).unwrap(), SourceAction::Lookup);
        assert_eq!(
            source_action(true, true).unwrap(),
            SourceAction::InspectSubmitted
        );
        assert!(source_action(false, true).is_err());
        let receipt = json!({"type":"confirmed","transactionId":"1", "eventId":"2",
            "acceptedCount":"3","worldRoot":"4"});
        confirmed(&receipt).unwrap();
        assert_eq!(
            post_action(false, None, &receipt, "abc").unwrap(),
            PostAction::First
        );
        assert_eq!(
            post_action(true, None, &receipt, "abc").unwrap(),
            PostAction::Hold
        );
        assert!(post_action(false, Some(&json!({})), &receipt, "abc").is_err());
    }

    #[test]
    fn only_exact_accepted_result_can_finalize_without_repost() {
        let receipt = json!({"type":"confirmed","transactionId":"1", "eventId":"2",
            "acceptedCount":"3","worldRoot":"4"});
        let accepted = json!({"type":"minidregg-selected-fn-post-v1",
            "sourceReceipt":receipt,"articleSha256":"abc",
            "status":"accepted","detail":"240 article received OK"});
        assert_eq!(
            post_action(true, Some(&accepted), &receipt, "abc").unwrap(),
            PostAction::Accepted
        );
        let uncertain = json!({"type":"minidregg-selected-fn-post-v1",
            "sourceReceipt":receipt,"articleSha256":"abc",
            "status":"explicit-uncertain",
            "detail":"441 posting failed; the outcome is uncertain, do not repost"});
        assert_eq!(
            post_action(true, Some(&uncertain), &receipt, "abc").unwrap(),
            PostAction::Hold
        );
        assert_eq!(
            post_action(true, Some(&accepted), &receipt, "changed").unwrap(),
            PostAction::Hold
        );
        let marker = json!({"type":"minidregg-selected-fn-post-attempt-v1",
            "sourceReceipt":receipt,"articleSha256":"abc"});
        validate_post_attempt(&marker, &receipt, "abc").unwrap();
        assert!(validate_post_attempt(&marker, &receipt, "changed").is_err());
    }
}
