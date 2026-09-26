//! One bounded B consumer wake. All policy decisions and calls come from Host/Main.
use super::*;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};

pub(super) fn private_dir(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => sync_directory_ancestors(path)?,
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(format!("cannot create {}: {error}", path.display())),
    }
    let meta = fs::symlink_metadata(path)
        .map_err(|error| format!("cannot inspect {}: {error}", path.display()))?;
    if !meta.is_dir()
        || meta.uid() != unsafe { geteuid() }
        || meta.permissions().mode() & 0o077 != 0
    {
        return Err(format!(
            "{} must be an owner-private directory",
            path.display()
        ));
    }
    Ok(())
}

unsafe extern "C" {
    fn geteuid() -> u32;
}

fn read_json(path: &Path) -> Result<Value> {
    serde_json::from_slice(
        &fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?,
    )
    .map_err(|error| format!("invalid {}: {error}", path.display()))
}

fn save_state(pending: &Path, state: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(state).map_err(|e| e.to_string())?;
    bytes.push(b'\n');
    let mut temp = None;
    for number in 0..1000 {
        let path = pending.join(format!("state-{number:03}.tmp"));
        if !path.exists() {
            temp = Some(path);
            break;
        }
    }
    let temp = temp.ok_or("exhausted durable state temporary names")?;
    create_private(&temp, &bytes)?;
    fs::rename(&temp, pending.join("state.json"))
        .map_err(|e| format!("cannot replace durable worker state: {e}"))?;
    sync_directory_ancestors(pending)
}

fn field<'a>(state: &'a Value, name: &str) -> Result<&'a str> {
    state
        .get(name)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("worker state lacks {name}"))
}

fn number(state: &Value, name: &str) -> Result<u64> {
    state
        .get(name)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("worker state lacks {name}"))
}

fn set(state: &mut Value, name: &str, value: Value) {
    state[name] = value;
}

fn attempt(pending: &Path, state: &mut Value, label: &str) -> Result<PathBuf> {
    let serial = number(state, "serial")?
        .checked_add(1)
        .ok_or("worker serial overflow")?;
    set(state, "serial", json!(serial));
    let name = format!("{label}-{serial:08}");
    set(state, label, json!(name));
    save_state(pending, state)?;
    Ok(pending.join(name))
}

pub(super) fn pin(
    state_dir: &Path,
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
) -> Result<()> {
    let config_bytes =
        fs::read(config).map_err(|e| format!("cannot read fn operator config: {e}"))?;
    let public_key = read_secret(key)?.verifying_key().to_bytes();
    let value = json!({
        "type":"minidregg-b-consumer-worker-pin-v1",
        "host":utf8_path(&absolute(host)?)?, "configPath":utf8_path(&absolute(config)?)?,
        "configHex":hex(&config_bytes), "socket":utf8_path(&absolute(socket)?)?,
        "keyPath":utf8_path(&absolute(key)?)?, "publicKey":hex(&public_key)
    });
    let path = state_dir.join("pin.json");
    if path.exists() {
        if read_json(&path)? != value {
            return Err(
                "consumer worker pin changed; retain old state for operator review".to_owned(),
            );
        }
    } else {
        write_json_new(&path, &value)?;
        sync_directory_ancestors(state_dir)?;
    }
    Ok(())
}

fn outcome_transaction(path: &Path) -> Result<Option<String>> {
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
        .ok_or("confirmed outcome lacks transactionId")?;
    if txn.is_empty()
        || txn.len() > 80
        || !txn.bytes().all(|c| c.is_ascii_digit())
        || (txn.len() > 1 && txn.starts_with('0'))
    {
        return Err("confirmed outcome has noncanonical transactionId".to_owned());
    }
    Ok(Some(txn.to_owned()))
}

fn latest_retry_path(prepare: &Path) -> Result<PathBuf> {
    let (_, json) = next_retry(prepare)?;
    Ok(json)
}

fn retry_outcome(prepare: &Path, mode: &str) -> Result<Value> {
    let json = latest_retry_path(prepare)?;
    let result = retry(prepare, mode, false);
    if json.exists() {
        sync_directory_ancestors(prepare)?;
        read_json(&json)
    } else {
        Err(result
            .err()
            .unwrap_or_else(|| "retry returned no outcome evidence".to_owned()))
    }
}

fn confirmed_after_retry(prepare: &Path, mode: &str) -> Result<Option<String>> {
    let json = latest_retry_path(prepare)?;
    let value = retry_outcome(prepare, mode)?;
    if value.get("type").and_then(Value::as_str) != Some("confirmed") {
        return Ok(None);
    }
    outcome_transaction(&json)
}

fn classify_poll(value: &Value) -> Result<(String, bool)> {
    if value.get("type").and_then(Value::as_str) != Some(B_CONSUMER.poll_type) {
        return Err("unexpected B poll response type".to_owned());
    }
    let status = value
        .get("status")
        .and_then(Value::as_str)
        .ok_or("B poll lacks status")?;
    match status {
        "idle"
            if value.pointer("/decision/type").and_then(Value::as_str)
                == Some("fn-empty-page-idle-v1")
                && value.get("intentHex").and_then(Value::as_str) == Some("") =>
        {
            Ok(("idle".into(), true))
        }
        "skip-decision"
            if value.pointer("/decision/type").and_then(Value::as_str)
                == Some("fn-empty-page-progress-decision-v1") =>
        {
            if value.pointer("/decision/decision").and_then(Value::as_str) != Some("proposed-fresh")
            {
                return Err("historical skip has no transaction ID in poll response; operator reconciliation required".into());
            }
            let from = value
                .pointer("/decision/fromPosition")
                .and_then(Value::as_str)
                .ok_or("skip lacks fromPosition")?
                .parse::<u128>()
                .map_err(|_| "invalid skip fromPosition")?;
            let to = value
                .pointer("/decision/toPosition")
                .and_then(Value::as_str)
                .ok_or("skip lacks toPosition")?
                .parse::<u128>()
                .map_err(|_| "invalid skip toPosition")?;
            let distance = to.checked_sub(from).ok_or("skip position reversed")?;
            if !(1..=16).contains(&distance) {
                return Err("skip page exceeds source poll scan bound".into());
            }
            Ok(("skip".into(), distance < 16))
        }
        "accepted-decision"
            if value
                .get("intentHex")
                .and_then(Value::as_str)
                .is_some_and(|s| !s.is_empty()) =>
        {
            Ok(("publication".into(), true))
        }
        "refused" => Err("B poll refused; retained evidence requires operator review".into()),
        _ => Err(
            "B poll cannot be advanced safely; retained evidence requires operator review".into(),
        ),
    }
}

fn finish(state_dir: &Path, pending: &Path, state: &Value) -> Result<()> {
    let completed = state_dir.join("completed");
    private_dir(&completed)?;
    let target = completed.join(field(state, "txn")?);
    if target.exists() {
        return Err("completed transaction archive already exists".into());
    }
    fs::rename(pending, &target)
        .map_err(|e| format!("cannot archive completed consumer operation: {e}"))?;
    sync_directory_ancestors(&completed)?;
    sync_directory_ancestors(state_dir)
}

fn ack_newly_confirmed(
    host: &Path,
    config: &Path,
    pending: &Path,
    state: &mut Value,
) -> Result<()> {
    let ack = attempt(pending, state, "ack")?;
    match consumer_ack(host, config, field(state, "txn")?, &ack, B_CONSUMER) {
        Ok(()) => sync_directory_ancestors(&ack),
        Err(_) => recover_acking(host, config, pending, state),
    }
}

// A retained op13 frame is sufficient evidence even if the process died before
// it wrote ack.json or archived the pending operation. Never infer an ACK from
// an absent reply, and never conflate prefix coverage with an exact ACK.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AckEvidence {
    Exact,
    Covered,
    Refused,
    Uncertain,
    TransportFault,
}

fn retained_ack(pending: &Path, state: &Value) -> Result<Option<AckEvidence>> {
    let Some(name) = state.get("ack").and_then(Value::as_str) else {
        return Ok(None);
    };
    if name.len() != 12
        || !name.starts_with("ack-")
        || !name[4..].bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err("durable ACK attempt name is invalid".into());
    }
    let directory = pending.join(name);
    let frame_path = directory.join("reply.frame");
    let json_path = directory.join("ack.json");
    if !frame_path.exists() {
        if json_path.exists() {
            return Err("ACK JSON exists without its complete retained frame".into());
        }
        return Ok(None);
    }
    let frame = fs::read(&frame_path)
        .map_err(|error| format!("cannot read retained ACK frame: {error}"))?;
    if frame.first() != Some(&B_CONSUMER.ack_opcode) {
        return Err("retained ACK frame is not a successful B ACK reply".into());
    }
    if json_path.exists()
        && fs::read(&json_path)
            .map_err(|error| format!("cannot read retained ACK JSON: {error}"))?
            != frame[1..]
    {
        return Err("retained ACK JSON differs from the complete frame".into());
    }
    let value: Value = serde_json::from_slice(&frame[1..])
        .map_err(|error| format!("retained ACK frame has invalid JSON: {error}"))?;
    match value.get("fnAck").and_then(Value::as_str) {
        Some("durable-accepted") => {
            parse_ack_result(&value, B_CONSUMER, field(state, "txn")?)?;
            Ok(Some(AckEvidence::Exact))
        }
        Some("covered-by-durable-frontier") => {
            parse_ack_result(&value, B_CONSUMER, field(state, "txn")?)?;
            Ok(Some(AckEvidence::Covered))
        }
        Some(status @ ("refused" | "uncertain" | "transport-fault")) => {
            if value.get("type").and_then(Value::as_str) != Some(B_CONSUMER.ack_type)
                || value.get("miniTransactionId").and_then(Value::as_str)
                    != Some(field(state, "txn")?)
            {
                return Err("retained ACK reply identity mismatch".into());
            }
            Ok(Some(match status {
                "refused" => AckEvidence::Refused,
                "uncertain" => AckEvidence::Uncertain,
                _ => AckEvidence::TransportFault,
            }))
        }
        _ => Err("retained ACK reply lacks a supported outcome".into()),
    }
}

fn recover_acking(host: &Path, config: &Path, pending: &Path, state: &mut Value) -> Result<()> {
    match retained_ack(pending, state) {
        Ok(Some(AckEvidence::Exact)) => return Ok(()),
        Ok(Some(AckEvidence::Covered)) => return hold(
            pending,
            state,
            "retained ACK proves only durable cursor-prefix coverage, not the exact old ACK event",
        ),
        Ok(Some(AckEvidence::Refused)) => {
            return hold(
                pending,
                state,
                "fn definitively refused the retained exact ACK; operator review required",
            )
        }
        Ok(Some(AckEvidence::Uncertain | AckEvidence::TransportFault)) => {}
        Err(error) => {
            return hold(
                pending,
                state,
                &format!("retained ACK reply requires operator review: {error}"),
            )
        }
        Ok(None) => {}
    }
    // A fresh native equal-current skip repeat returned durable-accepted with
    // unchanged ACK and journal frontiers. Retry only this retained transaction,
    // and persist the retry marker before sending so a second restart cannot
    // turn a lost reply into an unbounded stream of ACK attempts.
    if state.get("ackRetryStarted").and_then(Value::as_bool) == Some(true) {
        return hold(pending, state,
            "one exact ACK retry was already started without a complete reply; operator review required");
    }
    set(state, "ackRetryStarted", json!(true));
    save_state(pending, state)?;
    let ack = attempt(pending, state, "ack")?;
    match consumer_ack(host, config, field(state, "txn")?, &ack, B_CONSUMER) {
        Ok(()) => {
            sync_directory_ancestors(&ack)?;
            Ok(())
        }
        Err(error) => {
            let reason = match retained_ack(pending, state) {
                Ok(Some(AckEvidence::Exact)) => {
                    return hold(pending, state,
                        "exact ACK reply exists but client reported an error; operator review required")
                }
                Ok(Some(AckEvidence::Covered)) =>
                    "ACK retry proves only durable cursor-prefix coverage, not the exact old ACK event".to_owned(),
                Ok(Some(AckEvidence::Refused)) =>
                    "fn definitively refused the exact ACK retry; operator review required".to_owned(),
                Ok(Some(AckEvidence::Uncertain)) =>
                    "fn reported uncertain ACK retry; one retry exhausted".to_owned(),
                Ok(Some(AckEvidence::TransportFault)) =>
                    "fn reported ACK retry transport fault; one retry exhausted".to_owned(),
                Ok(None) => format!("ACK retry reply missing; one retry exhausted: {error}"),
                Err(inspect_error) => format!(
                    "ACK retry reply cannot be validated: {inspect_error}; client error: {error}"
                ),
            };
            hold(pending, state, &reason)
        }
    }
}

fn hold<T>(pending: &Path, state: &mut Value, reason: &str) -> Result<T> {
    set(state, "phase", json!("Held"));
    set(state, "reason", json!(reason));
    save_state(pending, state)?;
    Err(reason.to_owned())
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Stop {
    Idle,
    ShortPage,
    Publication,
    PageCap,
}

pub(super) fn run(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
) -> Result<()> {
    private_dir(state_dir)?;
    let socket_dir = socket.parent().ok_or("socket lacks parent")?;
    private_dir(socket_dir)?;
    let _global = transport::service_lock(&socket_dir.join("consumer-worker.lock"))?;
    let _lock = transport::service_lock(&state_dir.join("worker.lock"))?;
    let stop = run_locked(host, config, socket, key, state_dir, max_pages)?;
    println!("consumer wake stopped: {stop:?}");
    Ok(())
}

pub(super) fn run_locked(
    host: &Path,
    config: &Path,
    socket: &Path,
    key: &Path,
    state_dir: &Path,
    max_pages: u32,
) -> Result<Stop> {
    pin(state_dir, host, config, socket, key)?;
    let pending = state_dir.join("pending");
    let mut pages = 0;
    loop {
        if pages >= max_pages {
            return Ok(Stop::PageCap);
        }
        if !pending.exists() {
            private_dir(&pending)?;
            save_state(&pending, &json!({"phase":"Polling", "serial":0}))?;
        }
        private_dir(&pending)?;
        let state_file = pending.join("state.json");
        if !state_file.exists() {
            let only_state_temps = fs::read_dir(&pending)
                .map_err(|e| format!("cannot inspect new worker slot: {e}"))?
                .all(|entry| {
                    entry
                        .ok()
                        .and_then(|e| e.file_name().into_string().ok())
                        .is_some_and(|name| name.starts_with("state-") && name.ends_with(".tmp"))
                });
            if !only_state_temps {
                return Err(
                    "pending worker slot lacks durable state; operator review required".into(),
                );
            }
            save_state(&pending, &json!({"phase":"Polling", "serial":0}))?;
        }
        let mut state = read_json(&state_file)?;
        match field(&state, "phase")? {
            "Polling" => {
                let path = attempt(&pending, &mut state, "poll")?;
                if let Err(error) = consumer_poll(host, config, &path, B_CONSUMER) {
                    if path.join("reply.frame").exists() {
                        return hold(
                            &pending,
                            &mut state,
                            &format!("poll reply retained but unusable: {error}"),
                        );
                    }
                    return Err(error);
                }
                let value = read_json(&path.join("decision.json"))?;
                let (kind, short) = match classify_poll(&value) {
                    Ok(classification) => classification,
                    Err(error) => return hold(&pending, &mut state, &error),
                };
                if kind == "idle" {
                    fs::remove_dir_all(&pending)
                        .map_err(|e| format!("cannot clean idle poll: {e}"))?;
                    sync_directory_ancestors(state_dir)?;
                    return Ok(Stop::Idle);
                }
                if !path.join("intent.bin").is_file() {
                    return Err("poll did not retain canonical intent".into());
                }
                sync_directory_ancestors(&path)?;
                set(&mut state, "phase", json!("Preparing"));
                set(&mut state, "kind", json!(kind));
                set(&mut state, "short", json!(short));
                save_state(&pending, &state)?;
            }
            "Preparing" => {
                let poll = pending.join(field(&state, "poll")?);
                let path = attempt(&pending, &mut state, "prepare")?;
                submit(
                    host,
                    config,
                    &poll.join("intent.bin"),
                    OsStr::new("binary"),
                    key,
                    &path,
                    true,
                )?;
                sync_retained_call(&path, &path.join("call.bin"))?;
                set(&mut state, "phase", json!("Ready"));
                save_state(&pending, &state)?;
            }
            "Ready" => {
                let path = pending.join(field(&state, "prepare")?);
                sync_retained_call(&path, &path.join("call.bin"))?;
                set(&mut state, "phase", json!("Sending"));
                save_state(&pending, &state)?;
                let outcome_path = latest_retry_path(&path)?;
                let outcome = retry_outcome(&path, "submit")?;
                let txn = match outcome.get("type").and_then(Value::as_str) {
                    Some("confirmed") => outcome_transaction(&outcome_path)?
                        .ok_or("confirmed submit lacks transaction ID")?,
                    Some("refused") => {
                        return hold(
                            &pending,
                            &mut state,
                            "Mini definitively refused the exact call; operator review required",
                        )
                    }
                    _ => {
                        return Err(
                            "submit did not confirm; exact call retained, lookup required".into(),
                        )
                    }
                };
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" {
                    return Ok(Stop::Publication);
                }
                if state.get("short").and_then(Value::as_bool) == Some(true) {
                    return Ok(Stop::ShortPage);
                }
            }
            "Sending" => {
                let path = pending.join(field(&state, "prepare")?);
                sync_retained_call(&path, &path.join("call.bin"))?;
                let lookup_path = latest_retry_path(&path)?;
                let lookup = match retry_outcome(&path, "lookup") {
                    Ok(value) => value,
                    Err(error) => return hold(&pending, &mut state,
                        &format!("exact lookup unresolved; retained call requires operator reconciliation: {error}")),
                };
                let txn = match lookup.get("type").and_then(Value::as_str) {
                    Some("confirmed") => outcome_transaction(&lookup_path)?
                        .ok_or("confirmed exact lookup lacks transaction ID")?,
                    Some("absent") => match confirmed_after_retry(&path, "submit") {
                        Ok(Some(txn)) => txn,
                        Ok(None) => return hold(&pending, &mut state,
                            "same-call resubmit did not confirm; exact call retained"),
                        Err(error) => return hold(&pending, &mut state,
                            &format!("same-call resubmit uncertain; exact call retained: {error}")),
                    },
                    _ => return hold(&pending, &mut state,
                        "exact lookup did not confirm or prove absence; retained call requires operator reconciliation"),
                };
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" {
                    return Ok(Stop::Publication);
                }
                if state.get("short").and_then(Value::as_bool) == Some(true) {
                    return Ok(Stop::ShortPage);
                }
            }
            "Acking" => {
                recover_acking(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" {
                    return Ok(Stop::Publication);
                }
                if state.get("short").and_then(Value::as_bool) == Some(true) {
                    return Ok(Stop::ShortPage);
                }
            }
            "Held" => {
                return Err(format!(
                    "consumer worker held for operator review: {}",
                    field(&state, "reason")?
                ))
            }
            other => return Err(format!("unknown durable consumer phase {other}")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_skip_page_bound_stops_short_page_and_rejects_history_without_txn() {
        let fresh = json!({"type":"fn-consumer-poll-session-v1", "status":"skip-decision",
            "decision":{"type":"fn-empty-page-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"16", "toPosition":"21"},
            "intentHex":"00"});
        assert_eq!(classify_poll(&fresh).unwrap(), ("skip".to_owned(), true));
        let full = json!({"type":"fn-consumer-poll-session-v1", "status":"skip-decision",
            "decision":{"type":"fn-empty-page-progress-decision-v1",
                "decision":"proposed-fresh", "fromPosition":"0", "toPosition":"16"},
            "intentHex":"00"});
        assert_eq!(classify_poll(&full).unwrap(), ("skip".to_owned(), false));
        let mut repeated = fresh;
        repeated["decision"]["decision"] = json!("repeated");
        repeated["intentHex"] = json!("");
        assert!(classify_poll(&repeated).is_err());
    }

    #[test]
    fn durable_preparing_reserves_new_path_after_an_orphan() {
        let root = env::temp_dir().join(format!(
            "mini-drain-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        private_dir(&pending).unwrap();
        let mut state = json!({"phase":"Preparing", "serial":0});
        save_state(&pending, &state).unwrap();
        let old = attempt(&pending, &mut state, "prepare").unwrap();
        private_dir(&old).unwrap();
        let recovered = read_json(&pending.join("state.json")).unwrap();
        let mut recovered = recovered;
        let next = attempt(&pending, &mut recovered, "prepare").unwrap();
        assert_ne!(old, next);
        assert!(old.is_dir());
        assert_eq!(
            field(&read_json(&pending.join("state.json")).unwrap(), "phase").unwrap(),
            "Preparing"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_ack_distinguishes_exact_coverage_and_missing_reply() {
        let root = env::temp_dir().join(format!(
            "mini-ack-recovery-test-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        private_dir(&root).unwrap();
        let pending = root.join("pending");
        private_dir(&pending).unwrap();
        let mut state = json!({"phase":"Acking", "serial":0, "txn":"123"});
        assert_eq!(retained_ack(&pending, &state).unwrap(), None);
        let ack = attempt(&pending, &mut state, "ack").unwrap();
        private_dir(&ack).unwrap();
        assert_eq!(retained_ack(&pending, &state).unwrap(), None);

        let exact = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"durable-accepted"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&exact).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Exact)
        );

        fs::remove_file(ack.join("reply.frame")).unwrap();
        let covered = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"covered-by-durable-frontier",
            "kind":"empty-page-skip", "fnCursorPosition":"16", "fnCommittedAck":"21"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&covered).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Covered)
        );
        create_private(&ack.join("ack.json"), b"different").unwrap();
        assert!(retained_ack(&pending, &state).is_err());
        fs::remove_file(ack.join("ack.json")).unwrap();
        fs::remove_file(ack.join("reply.frame")).unwrap();
        let uncertain = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"uncertain"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&uncertain).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Uncertain)
        );
        fs::remove_file(ack.join("reply.frame")).unwrap();
        let refused = json!({"type":B_CONSUMER.ack_type,
            "miniTransactionId":"123", "fnAck":"refused"});
        let mut frame = vec![B_CONSUMER.ack_opcode];
        frame.extend(serde_json::to_vec(&refused).unwrap());
        create_private(&ack.join("reply.frame"), &frame).unwrap();
        assert_eq!(
            retained_ack(&pending, &state).unwrap(),
            Some(AckEvidence::Refused)
        );
        fs::remove_dir_all(root).unwrap();
    }
}
