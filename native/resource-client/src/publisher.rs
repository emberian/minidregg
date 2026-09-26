//! Durable custody for one exact, already signed fn R carrier.
//! Mini Host owns the origin and outbox decisions; this module only retains
//! attempts and moves the same carrier across the protected fn POST boundary.
use super::*;
use sha2::{Digest, Sha256};

fn digest(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(&fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?)
        .map_err(|e| format!("{}: {e}", path.display()))
}

fn durable_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)?;
    sync_directory_ancestors(path.parent().ok_or("publisher state has no parent")?)
}

fn transaction(path: &Path) -> Result<Option<String>> {
    if !path.exists() {
        return Ok(None);
    }
    let value = read_json(path)?;
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Ok(None);
    }
    let txn = value
        .get("transactionId")
        .and_then(Value::as_str)
        .ok_or("confirmed outbox outcome lacks transactionId")?;
    if txn.is_empty()
        || txn.len() > 80
        || !txn.bytes().all(|b| b.is_ascii_digit())
        || (txn.len() > 1 && txn.starts_with('0'))
    {
        return Err("outbox transaction ID is not canonical decimal".into());
    }
    Ok(Some(txn.to_owned()))
}

// Each argument is an independently selected custody input; the pin records
// them separately so a restart cannot silently substitute one path or key.
#[allow(clippy::too_many_arguments)]
fn pin(
    state: &Path,
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    carrier: &[u8],
    post_config: &Path,
    post: &worker::FnPostConfig,
) -> Result<()> {
    let key_public = read_secret(key)?.verifying_key().to_bytes();
    let value = json!({
        "type":"minidregg-fn-origin-publisher-pin-v1",
        "host":utf8_path(&absolute(host)?)?,
        "configPath":utf8_path(&absolute(config)?)?,
        "configSha256":digest(&fs::read(config).map_err(|e| e.to_string())?),
        "socket":utf8_path(&absolute(socket)?)?,
        "keyPath":utf8_path(&absolute(key)?)?,
        "gatewayPublicKey":hex(&key_public),
        "carrierSha256":digest(carrier),
        "postConfigPath":utf8_path(&absolute(post_config)?)?,
        "postConfigSha256":digest(&fs::read(post_config).map_err(|e| e.to_string())?),
        "fnPort":post.port,
        "fnCertificatePath":utf8_path(&post.cert)?,
        "fnCertificateSha256":digest(&post.cert_pem)
    });
    let path = state.join("pin.json");
    if path.exists() {
        if read_json(&path)? != value {
            return Err("publisher identity changed; retain state for operator review".into());
        }
    } else {
        durable_json(&path, &value)?;
    }
    Ok(())
}

fn prepare(host: &Path, config: &Path, state: &Path) -> Result<PathBuf> {
    let directory = state.join("outbox-prepare");
    if !directory.exists() {
        origin_outbox_prepare(host, config, &state.join("carrier.bin"), &directory)?;
    }
    let decision = read_json(&directory.join("decision.json"))?;
    if decision.get("type").and_then(Value::as_str) != Some("fn-a-origin-outbox-session-v1")
        || decision.get("status").and_then(Value::as_str) != Some("prepared-decision")
        || decision.get("decision").and_then(Value::as_str) != Some("proposed-fresh")
        || !directory.join("intent.bin").exists()
    {
        return Err("outbox preparation is not a fresh exact intent; retained for review".into());
    }
    Ok(directory.join("intent.bin"))
}

fn accepted_outbox(
    host: &Path,
    config: &Path,
    key: &Path,
    intent: &Path,
    state: &Path,
) -> Result<String> {
    let directory = state.join("outbox-submit");
    if !directory.exists() {
        let _ = submit(
            host,
            config,
            intent,
            OsStr::new("binary"),
            key,
            &directory,
            false,
        );
    }
    if let Some(txn) = transaction(&directory.join("outcome.json"))? {
        return Ok(txn);
    }
    for index in 0..1000 {
        let path = directory.join(format!("retry-{index:04}.json"));
        if let Some(txn) = transaction(&path)? {
            return Ok(txn);
        }
    }
    if !directory.join("call.bin").exists() {
        return Err("outbox submit has no retained exact call; operator review required".into());
    }
    // Only the original call may be retried. A lookup that cannot establish
    // confirmation leaves the state unresolved; it never mints a new command.
    let (_, lookup_json) = next_retry(&directory)?;
    let _ = retry(&directory, "lookup", false);
    if let Some(txn) = transaction(&lookup_json)? {
        return Ok(txn);
    }
    // Store explicitly proved the retained call absent. One same-call submit
    // may settle an attempt whose original response was lost.
    if lookup_json.exists()
        && read_json(&lookup_json)?.get("type").and_then(Value::as_str) == Some("absent")
    {
        let (_, submit_json) = next_retry(&directory)?;
        let _ = retry(&directory, "submit", false);
        if let Some(txn) = transaction(&submit_json)? {
            return Ok(txn);
        }
    }
    Err("outbox submit remains uncertain; retain exact call for reconciliation".into())
}

fn export(config: &Path, socket: &Path, txn: &str, carrier: &[u8], state: &Path) -> Result<()> {
    let path = state.join("outbox-export.frame");
    let frame = if path.exists() {
        fs::read(&path).map_err(|e| e.to_string())?
    } else {
        let frame = transport::invoke(socket, config, 18, txn.as_bytes())?;
        create_private(&path, &frame)?;
        sync_directory_ancestors(state)?;
        frame
    };
    if frame.first() != Some(&18) {
        return Err("Host refused accepted outbox export; exact frame retained".into());
    }
    let value: Value = serde_json::from_slice(&frame[1..]).map_err(|e| e.to_string())?;
    if value.get("type").and_then(Value::as_str) != Some("fn-a-origin-outbox-export-v1")
        || value.get("status").and_then(Value::as_str) != Some("accepted")
        || value.get("transactionId").and_then(Value::as_str) != Some(txn)
    {
        return Err("accepted outbox export identity differs".into());
    }
    let carrier_hex = value
        .get("carrierHex")
        .and_then(Value::as_str)
        .ok_or("outbox export lacks exact carrier")?;
    let exported = decode_hex(carrier_hex)?;
    if exported != carrier || hex(&exported) != carrier_hex {
        return Err("accepted Mini outbox carrier differs from retained signed R".into());
    }
    for field in [
        "messageId",
        "sourceIdentity",
        "packageIdentity",
        "originCallIdentity",
        "miniOrigin",
        "miniOutbox",
    ] {
        if value.get(field).is_none() {
            return Err(format!("outbox export lacks {field}"));
        }
    }
    Ok(())
}

#[derive(Debug, Eq, PartialEq)]
enum PostAction {
    First,
    Second,
    Accepted(String),
    Hold,
}

fn accepted_status_line(status: &str, line: &str) -> bool {
    match status {
        "accepted" => line == "240 article received OK",
        "already-stored" => line == "441 posting failed; this article is already stored here",
        _ => false,
    }
}

fn post_action(
    first_exists: bool,
    first_result: Option<&Value>,
    second_exists: bool,
    second_result: Option<&Value>,
    txn: &str,
    carrier_digest: &str,
) -> Result<PostAction> {
    if (first_result.is_some() && !first_exists)
        || (second_exists && !first_exists)
        || (second_result.is_some() && !second_exists)
    {
        return Err("fn POST attempts have an impossible durable order".into());
    }
    if second_exists
        && first_result
            .and_then(|v| v.get("status"))
            .and_then(Value::as_str)
            != Some("transport-uncertain")
    {
        return Err("second fn POST attempt lacks a settled transport loss".into());
    }
    for (number, result) in [(1, first_result), (2, second_result)] {
        if let Some(value) = result {
            if value.get("type").and_then(Value::as_str) != Some("fn-exact-post-result-v1")
                || value.get("number").and_then(Value::as_u64) != Some(number)
                || value.get("outboxTransactionId").and_then(Value::as_str) != Some(txn)
                || value.get("carrierSha256").and_then(Value::as_str) != Some(carrier_digest)
            {
                return Err("retained fn POST result differs from pinned attempt".into());
            }
            let status = value
                .get("status")
                .and_then(Value::as_str)
                .ok_or("retained fn POST result lacks status")?;
            let detail = value
                .get("detail")
                .and_then(Value::as_str)
                .ok_or("retained fn POST result lacks exact detail")?;
            if detail.is_empty() {
                return Err("retained fn POST result has empty detail".into());
            }
            if matches!(status, "accepted" | "already-stored") {
                if !accepted_status_line(status, detail) {
                    return Err("retained fn POST success has unexpected status line".into());
                }
                return Ok(PostAction::Accepted(detail.to_owned()));
            }
            if !matches!(
                status,
                "transport-uncertain" | "explicit-uncertain" | "conflict" | "refused"
            ) {
                return Err("retained fn POST result has unknown status".into());
            }
        }
    }
    if !first_exists {
        return if first_result.is_none() && !second_exists && second_result.is_none() {
            Ok(PostAction::First)
        } else {
            Err("fn POST attempts have an impossible durable order".into())
        };
    }
    let Some(first_value) = first_result else {
        return Ok(PostAction::Hold);
    };
    if first_value.get("status").and_then(Value::as_str) != Some("transport-uncertain") {
        return Ok(PostAction::Hold);
    }
    if second_exists || second_result.is_some() {
        Ok(PostAction::Hold)
    } else {
        Ok(PostAction::Second)
    }
}

pub(super) fn publish(
    host: &Path,
    config: &Path,
    socket: &Path,
    gateway_key: &Path,
    signed_carrier: &Path,
    state_dir: &Path,
    post_config_path: &Path,
) -> Result<()> {
    drain::private_dir(state_dir)?;
    let _owner = transport::service_lock(&state_dir.join("publisher.lock"))?;
    let post = worker::post_config(post_config_path)?;
    let carrier =
        fs::read(signed_carrier).map_err(|e| format!("cannot read signed R carrier: {e}"))?;
    if carrier.is_empty() || carrier.len() > 1_516_384 {
        return Err("signed R carrier exceeds selected profile".into());
    }
    pin(
        state_dir,
        host,
        config,
        socket,
        gateway_key,
        &carrier,
        post_config_path,
        &post,
    )?;
    let retained = state_dir.join("carrier.bin");
    if !retained.exists() {
        create_private(&retained, &carrier)?;
        sync_directory_ancestors(state_dir)?;
    } else if fs::read(&retained).map_err(|e| e.to_string())? != carrier {
        return Err("retained signed R carrier changed".into());
    }
    let intent = prepare(host, config, state_dir)?;
    let txn = accepted_outbox(host, config, gateway_key, &intent, state_dir)?;
    export(config, socket, &txn, &carrier, state_dir)?;
    let accepted = state_dir.join("fn-post-accepted.json");
    if accepted.exists() {
        let result = read_json(&accepted)?;
        if result.get("type").and_then(Value::as_str) == Some("fn-exact-post-accepted-v1")
            && result.get("outboxTransactionId").and_then(Value::as_str) == Some(txn.as_str())
            && result.get("carrierSha256").and_then(Value::as_str)
                == Some(digest(&carrier).as_str())
            && matches!(
                result.get("statusLine").and_then(Value::as_str),
                Some(
                    "240 article received OK"
                        | "441 posting failed; this article is already stored here"
                )
            )
        {
            return Ok(());
        }
        return Err("retained fn POST result differs from accepted outbox".into());
    }
    let first = state_dir.join("fn-post-attempt-1.json");
    let first_result = state_dir.join("fn-post-result-1.json");
    let second = state_dir.join("fn-post-attempt-2.json");
    let second_result = state_dir.join("fn-post-result-2.json");
    let first_value = if first_result.exists() {
        Some(read_json(&first_result)?)
    } else {
        None
    };
    let second_value = if second_result.exists() {
        Some(read_json(&second_result)?)
    } else {
        None
    };
    let action = post_action(
        first.exists(),
        first_value.as_ref(),
        second.exists(),
        second_value.as_ref(),
        &txn,
        &digest(&carrier),
    )?;
    if let PostAction::Accepted(line) = action {
        durable_json(
            &accepted,
            &json!({"type":"fn-exact-post-accepted-v1",
            "outboxTransactionId":txn,"statusLine":line,
            "carrierSha256":digest(&carrier)}),
        )?;
        return Ok(());
    }
    let number = match action {
        PostAction::First => 1,
        PostAction::Second => 2,
        PostAction::Hold => {
            return Err("fn POST outcome unresolved; operator review required".into())
        }
        PostAction::Accepted(_) => unreachable!(),
    };
    let (attempt, result_path) = if number == 1 {
        (first, first_result)
    } else {
        (second, second_result)
    };
    // create_new is the atomic claim. A concurrent publisher that observed
    // the same absent pathname loses here and cannot also send a POST.
    durable_json(
        &attempt,
        &json!({"type":"fn-exact-post-attempt-v1",
        "number":number,"outboxTransactionId":txn,"carrierSha256":digest(&carrier)}),
    )?;
    let outcome = match worker::post_exact_carrier(&post, &carrier) {
        Ok(value) => value,
        Err(error) => worker::FnPostOutcome::TransportUncertain(error),
    };
    use worker::FnPostOutcome;
    let (status, detail) = match &outcome {
        FnPostOutcome::Accepted(line) => ("accepted", line),
        FnPostOutcome::AlreadyStored(line) => ("already-stored", line),
        FnPostOutcome::Conflict(line) => ("conflict", line),
        FnPostOutcome::ExplicitUncertain(line) => ("explicit-uncertain", line),
        FnPostOutcome::Refused(line) => ("refused", line),
        FnPostOutcome::TransportUncertain(detail) => ("transport-uncertain", detail),
    };
    durable_json(
        &result_path,
        &json!({"type":"fn-exact-post-result-v1",
        "number":number,"status":status,"detail":detail,
        "outboxTransactionId":txn,"carrierSha256":digest(&carrier)}),
    )?;
    match outcome {
        FnPostOutcome::Accepted(line) | FnPostOutcome::AlreadyStored(line) => durable_json(
            &accepted,
            &json!({"type":"fn-exact-post-accepted-v1",
                "outboxTransactionId":txn,"statusLine":line,"carrierSha256":digest(&carrier)}),
        ),
        FnPostOutcome::Conflict(line) => Err(format!("fn Message-ID conflict: {line}")),
        FnPostOutcome::ExplicitUncertain(line) => Err(format!(
            "fn explicitly reported uncertain; do not repost: {line}"
        )),
        FnPostOutcome::Refused(line) => Err(format!("fn refused exact carrier: {line}")),
        FnPostOutcome::TransportUncertain(detail) => Err(format!(
            "fn POST outcome uncertain; retained exact carrier: {detail}"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn result(number: u64, status: &str) -> Value {
        let detail = match status {
            "accepted" => "240 article received OK",
            "already-stored" => "441 posting failed; this article is already stored here",
            _ => "fn response",
        };
        json!({"type":"fn-exact-post-result-v1","number":number,
            "status":status,"detail":detail,"outboxTransactionId":"123",
            "carrierSha256":"abc"})
    }

    #[test]
    fn accepted_result_survives_crash_before_final_marker() {
        assert_eq!(
            post_action(
                true,
                Some(&result(1, "accepted")),
                false,
                None,
                "123",
                "abc"
            )
            .unwrap(),
            PostAction::Accepted("240 article received OK".into())
        );
        assert_eq!(
            post_action(
                true,
                Some(&result(1, "transport-uncertain")),
                true,
                Some(&result(2, "already-stored")),
                "123",
                "abc"
            )
            .unwrap(),
            PostAction::Accepted("441 posting failed; this article is already stored here".into())
        );
    }

    #[test]
    fn explicit_uncertainty_and_unrecorded_attempt_never_auto_repost() {
        assert_eq!(
            post_action(
                true,
                Some(&result(1, "explicit-uncertain")),
                false,
                None,
                "123",
                "abc"
            )
            .unwrap(),
            PostAction::Hold
        );
        assert_eq!(
            post_action(true, None, false, None, "123", "abc").unwrap(),
            PostAction::Hold
        );
    }

    #[test]
    fn transport_loss_allows_one_exact_retry_only() {
        let uncertain = result(1, "transport-uncertain");
        assert_eq!(
            post_action(false, None, false, None, "123", "abc").unwrap(),
            PostAction::First
        );
        assert_eq!(
            post_action(true, Some(&uncertain), false, None, "123", "abc").unwrap(),
            PostAction::Second
        );
        assert_eq!(
            post_action(true, Some(&uncertain), true, None, "123", "abc").unwrap(),
            PostAction::Hold
        );
        assert_eq!(
            post_action(
                true,
                Some(&uncertain),
                true,
                Some(&result(2, "transport-uncertain")),
                "123",
                "abc"
            )
            .unwrap(),
            PostAction::Hold
        );
        assert!(post_action(true, Some(&uncertain), false, None, "124", "abc").is_err());
    }

    #[test]
    fn concurrent_post_claim_is_create_new() {
        let dir = std::env::temp_dir().join(format!(
            "mini-publisher-claim-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        drain::private_dir(&dir).unwrap();
        let claim = dir.join("attempt.json");
        assert!(durable_json(&claim, &json!({"number":1})).is_ok());
        assert!(durable_json(&claim, &json!({"number":1})).is_err());
        fs::remove_dir_all(dir).unwrap();
    }
}
