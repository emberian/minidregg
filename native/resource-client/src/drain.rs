//! One bounded B consumer wake. All policy decisions and calls come from Host/Main.
use super::*;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};

fn private_dir(path: &Path) -> Result<()> {
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

fn pin(state_dir: &Path, host: &Path, config: &Path, socket: &Path, key: &Path) -> Result<()> {
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

fn confirmed_after_retry(prepare: &Path, mode: &str) -> Result<Option<String>> {
    let json = latest_retry_path(prepare)?;
    let result = retry(prepare, mode, false);
    match (result, outcome_transaction(&json)?) {
        (_, Some(txn)) => {
            sync_directory_ancestors(prepare)?;
            Ok(Some(txn))
        }
        (Err(error), None) => Err(error),
        (Ok(()), None) => Err("retry completed without confirmed transaction evidence".to_owned()),
    }
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
    consumer_ack(host, config, field(state, "txn")?, &ack, B_CONSUMER)?;
    sync_directory_ancestors(&ack)
}

fn hold(pending: &Path, state: &mut Value, reason: &str) -> Result<()> {
    set(state, "phase", json!("Held"));
    set(state, "reason", json!(reason));
    save_state(pending, state)?;
    Err(reason.to_owned())
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
    let _lock = transport::service_lock(&state_dir.join("worker.lock"))?;
    pin(state_dir, host, config, socket, key)?;
    let pending = state_dir.join("pending");
    let mut pages = 0;
    loop {
        if pages >= max_pages {
            println!("consumer wake reached {max_pages} page limit");
            return Ok(());
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
                        return hold(&pending, &mut state, &format!("poll reply retained but unusable: {error}"));
                    }
                    return Err(error);
                }
                let value = read_json(&path.join("decision.json"))?;
                let (kind, short) = match classify_poll(&value) {
                    Ok(classification) => classification,
                    Err(error) => return hold(&pending, &mut state, &error),
                };
                if kind == "idle" {
                    fs::remove_dir_all(&pending).map_err(|e| format!("cannot clean idle poll: {e}"))?;
                    sync_directory_ancestors(state_dir)?;
                    println!("consumer idle");
                    return Ok(());
                }
                if !path.join("intent.bin").is_file() { return Err("poll did not retain canonical intent".into()); }
                sync_directory_ancestors(&path)?;
                set(&mut state, "phase", json!("Preparing"));
                set(&mut state, "kind", json!(kind));
                set(&mut state, "short", json!(short));
                save_state(&pending, &state)?;
            }
            "Preparing" => {
                let poll = pending.join(field(&state, "poll")?);
                let path = attempt(&pending, &mut state, "prepare")?;
                submit(host, config, &poll.join("intent.bin"), OsStr::new("binary"), key, &path, true)?;
                sync_retained_call(&path, &path.join("call.bin"))?;
                set(&mut state, "phase", json!("Ready"));
                save_state(&pending, &state)?;
            }
            "Ready" => {
                let path = pending.join(field(&state, "prepare")?);
                sync_retained_call(&path, &path.join("call.bin"))?;
                set(&mut state, "phase", json!("Sending"));
                save_state(&pending, &state)?;
                let txn = confirmed_after_retry(&path, "submit")?
                    .ok_or("submit did not confirm; exact call retained, lookup required")?;
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication" || state.get("short").and_then(Value::as_bool) == Some(true) {
                    println!("consumer wake completed {pages} operation(s)"); return Ok(());
                }
            }
            "Sending" => {
                let path = pending.join(field(&state, "prepare")?);
                sync_retained_call(&path, &path.join("call.bin"))?;
                let txn = match confirmed_after_retry(&path, "lookup") {
                    Ok(Some(txn)) => txn,
                    Ok(None) => return hold(&pending, &mut state,
                        "exact lookup did not confirm; retained call requires operator reconciliation"),
                    Err(error) => return hold(&pending, &mut state,
                        &format!("exact lookup unresolved; retained call requires operator reconciliation: {error}")),
                };
                set(&mut state, "txn", json!(txn));
                set(&mut state, "phase", json!("Acking"));
                save_state(&pending, &state)?;
                ack_newly_confirmed(host, config, &pending, &mut state)?;
                finish(state_dir, &pending, &state)?;
                pages += 1;
                if field(&state, "kind")? == "publication"
                    || state.get("short").and_then(Value::as_bool) == Some(true)
                {
                    println!("consumer wake completed {pages} operation(s)");
                    return Ok(());
                }
            }
            "Acking" => return Err("ACK outcome may have been lost; retained transaction requires operator reconciliation".into()),
            "Held" => return Err(format!("consumer worker held for operator review: {}", field(&state, "reason")?)),
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
}
