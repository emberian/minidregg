//! Explicit stopped-controller enrollment. The installer publishes a target
//! config first; until this command commits, ordinary startup fails closed on
//! the old journal binding. No startup recovery or general migration hook.
use super::*;
use std::os::unix::fs::DirBuilderExt;

const PROTOCOL: &str = "mini-controller-application-enrollment-v1";
const JOURNAL_LIMIT: usize = 32 * 1024 * 1024;

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    protocol: String,
    mode: String,
    expected_binding_sha256: String,
    target_config_sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    resident_state: Option<PathBuf>,
}

fn bytes(value: &impl Serialize) -> Result<Vec<u8>> {
    serde_json::to_vec(value).map_err(|e| e.to_string())
}
fn digest(value: &impl Serialize) -> Result<String> {
    sha256_bytes(&bytes(value)?)
}
fn private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
        || meta.nlink() != 1
        || meta.len() > limit as u64
    {
        return Err("enrollment input is not a bounded private owned file".into());
    }
    bounded_regular_file(path, limit)
}
fn directory(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {}
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {}
        Err(e) => return Err(e.to_string()),
    }
    let meta = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } || meta.mode() & 0o077 != 0 {
        return Err("enrollment directory is not private and owned".into());
    }
    // A prior process may have died after mkdir but before its parent sync.
    // Re-entry must durably retain that directory entry before a journal commit.
    File::open(path)
        .map_err(|e| e.to_string())?;
    Ok(())
}
fn retain(path: &Path, data: &[u8]) -> Result<()> {
    if path.exists() {
        if private(path, JOURNAL_LIMIT)? != data {
            return Err("retained enrollment bytes differ".into());
        }
    } else {
        journal_io::write(path, data)
            .map_err(|error| format!("enrollment archive publication: {error}"))?;
    }
    Ok(())
}

struct ConsumedOriginProof(Value);

/// The origin is historical only after the native resident consumed its exact
/// typed terminal outcome. An idle controller alone is insufficient. Read the
/// two resident journals through their already-held guard and retain their
/// hashes with the native outcome evidence; never clear the origin.
fn consumed_origin(
    j: &Journal,
    config: &Config,
    resident: &quiescence::ResidentGuard,
) -> Result<Option<ConsumedOriginProof>> {
    let Some(origin) = &j.resident_prompt_origin else {
        return Ok(None);
    };
    if !matches!(
        resident.evidence(),
        quiescence::ResidentEvidence::Stopped {
            prompt_pending: false,
            return_pending: false,
            queued_requests: false,
            started_request: false,
            maintenance_pending: false
        }
    ) {
        return Err("retained resident origin requires stopped, drained resident custody".into());
    }
    let requests = resident
        .request_bytes()
        .ok_or("consumed resident origin requires retained request custody")?;
    let outcome = prompt_outcome::read_bound(
        &config.state_dir,
        origin.prompt_operation_id,
        &origin.resident_prompt_id,
        &origin.prompt_sha256,
    )?;
    validate_consumed_frame(origin, resident.bytes()?, &outcome)?;
    let mut proof = json!({"type":"mini-enrollment-consumed-resident-origin-v1",
        "origin":origin,"residentState":resident.path()?,"residentStateSha256":sha256_bytes(resident.bytes()?)?,
        "requestsSha256":sha256_bytes(requests)?,
        "promptEvidence":prompt_outcome::evidence(&config.state_dir,origin.prompt_operation_id)?});
    if matches!(outcome.outcome, prompt_outcome::Outcome::Admitted { .. }) {
        proof["completedTurn"] = resident_completion::consumed_turn(config, j, resident)?;
    }
    Ok(Some(ConsumedOriginProof(proof)))
}

fn validate_consumed_frame(
    origin: &resident_origin::ResidentPromptOrigin,
    resident: &[u8],
    outcome: &prompt_outcome::Record,
) -> Result<()> {
    let state: Value = serde_json::from_slice(resident).map_err(|e| e.to_string())?;
    let frame = &state["lastCompletion"];
    let completed: resident_origin::ResidentPromptOrigin =
        serde_json::from_value(frame["residentOrigin"].clone())
            .map_err(|e| format!("resident drain lacks exact terminal origin: {e}"))?;
    let terminal = match &outcome.outcome {
        prompt_outcome::Outcome::Refused { .. } => {
            frame["outcome"].as_str().is_some_and(|v| v != "completed")
        }
        prompt_outcome::Outcome::Admitted { stop_reason, .. } => {
            stop_reason == "end_turn"
                && frame["outcome"] == "completed"
                && frame["reviewNeeded"] == false
                && frame["retainedSession"] == true
        }
        _ => false,
    };
    if state["completed"].as_u64().is_none_or(|n| n == 0)
        || frame["type"] != "prompt-complete"
        || !terminal
        || bytes(&completed)? != bytes(origin)?
        || outcome.session_id != origin.session_id
        || outcome.prompt_operation_id != origin.prompt_operation_id
        || outcome.resident_prompt_id.as_deref() != Some(&origin.resident_prompt_id)
        || outcome.prompt_sha256.as_deref() != Some(&origin.prompt_sha256)
    {
        return Err("resident origin has not consumed its exact native terminal outcome".into());
    }
    Ok(())
}

#[cfg(test)]
fn quiescent(j: &Journal, resident: quiescence::ResidentEvidence) -> Result<()> {
    quiescent_with_origin(j, resident, None)
}

fn quiescent_with_origin(
    j: &Journal,
    resident: quiescence::ResidentEvidence,
    consumed: Option<&ConsumedOriginProof>,
) -> Result<()> {
    // Reuse the retained-work census, including unresolved historical rows.
    // A failed initial read may leave the connection fenced with no work; this
    // command preserves that fence. Soft alone is not a held allowance.
    let retained = quiescence::retained(j, resident);
    // Older qualified controllers predate the optional retry-gate field.
    // Inspect the serialized field when present without requiring that old
    // controller to acquire a new provider state machine for app enrollment.
    let provider_retry = serde_json::to_value(j)
        .map_err(|e| e.to_string())?
        .get("providerRetryGate")
        .is_some_and(|value| !value.is_null());
    let completed = consumed
        .is_some_and(|proof| proof.0["completedTurn"]["type"] == "mini-consumed-completed-turn-v1");
    if matches!(resident, quiescence::ResidentEvidence::Unknown)
        || retained.iter().any(|field| *field != "connection_fenced")
        || j.connection == Connection::Hard
        || (j.provider_settlement.is_some() && !completed)
        || provider_retry
        || j.resident_prompt_origin
            .as_ref()
            .is_some_and(|origin| consumed.is_none_or(|proof| proof.0["origin"] != json!(origin)))
        || (j.hermes_session.is_some() && !completed)
    {
        return Err(
            "enrollment requires stopped, settled controller custody; resolve retained work first"
                .into(),
        );
    }
    Ok(())
}


fn array<'a>(value: &'a Value, field: &str) -> Result<&'a [Value]> {
    match value.get(field) {
        Some(Value::Array(values)) => Ok(values),
        None if matches!(
            field,
            "registeredSharedApplications"
                | "typedApplications"
                | "applicationServices"
                | "allowedApplicationLifetimeRoutes"
        ) =>
        {
            Ok(&[])
        }
        _ => Err(format!("enrollment {field} array invalid")),
    }
}
fn append<'a>(old: &'a Value, new: &'a Value, field: &str) -> Result<&'a [Value]> {
    let a = array(old, field)?;
    let b = array(new, field)?;
    if b.len() < a.len() || b.len() > a.len() + 1 || b[..a.len()] != a[..] {
        return Err(format!(
            "enrollment may append one {field}; retained entries are immutable"
        ));
    }
    Ok(&b[a.len()..])
}

/// All authority, custody, budgets and transport outside these exact additions
/// remain byte-equivalent after typed Config normalization.
fn permitted(old: &Config, new: &Config, j: &Journal, mode: &str) -> Result<()> {
    let mut a = serde_json::to_value(old).map_err(|e| e.to_string())?;
    let mut b = serde_json::to_value(new).map_err(|e| e.to_string())?;
    match mode {
        "bootstrap-dispatch" => {
            if old.dispatch_task.is_some()
                || new.dispatch_task.is_none()
                || old.provider_task.is_some()
                || !j.foreground_history.is_empty()
                || !j.born_resources.is_empty()
                || !j.birth_next_ordinal.is_empty()
                || !j.application_api_history.is_empty()
                || !j.publication_receipts.is_empty()
                || j.managed_law_generation.is_some()
                || !j.reconciliation_log.is_empty()
                || j.hermes_session.is_some()
                || !j.prior_hermes_sessions.is_empty()
                || !j.workspace_resolutions.is_empty()
                || !j.workspace_proposals.is_empty()
                || !j.room_resolutions.is_empty()
            {
                return Err("dispatch enrollment is only permitted before the first admitted controller operation".into());
            }
            a.as_object_mut().unwrap().remove("dispatchTask");
            b.as_object_mut().unwrap().remove("dispatchTask");
        }
        "application" => {
            if old.dispatch_task.is_none() {
                return Err("application enrollment requires existing dispatch custody".into());
            }
            let at = a
                .get_mut("toolTask")
                .and_then(Value::as_object_mut)
                .ok_or("tool task absent")?;
            let bt = b
                .get_mut("toolTask")
                .and_then(Value::as_object_mut)
                .ok_or("tool task absent")?;
            let av = Value::Object(at.clone());
            let bv = Value::Object(bt.clone());
            let refs = append(&av, &bv, "registeredSharedApplications")?;
            let profiles = append(&av, &bv, "applicationServices")?;
            let typed = append(&av, &bv, "typedApplications")?;
            let old_routes = array(&av, "allowedApplicationLifetimeRoutes")?;
            let new_routes = array(&bv, "allowedApplicationLifetimeRoutes")?;
            if new_routes.len() < old_routes.len() || new_routes.len() > old_routes.len() + 1 {
                return Err("enrollment may append one lifetime route".into());
            }
            let mut refreshed = 0;
            for (before, after) in old_routes.iter().zip(new_routes.iter()) {
                let mut x = before.clone();
                let mut y = after.clone();
                if x["hostUnit"] != y["hostUnit"] {
                    refreshed += 1;
                }
                x.as_object_mut()
                    .ok_or("route object absent")?
                    .remove("hostUnit");
                y.as_object_mut()
                    .ok_or("route object absent")?
                    .remove("hostUnit");
                if x != y {
                    return Err("enrollment cannot change retained route lineage or custody".into());
                }
            }
            if new_routes.len() == old_routes.len() + 1 {
                if refs.len() != 1 || profiles.len() + typed.len() != 1 || refreshed != 0 {
                    return Err(
                        "new route requires one matching application reference and service or typed attachment".into(),
                    );
                }
                let route = new_routes.last().unwrap();
                let reference = &refs[0];
                if route["name"] != reference["name"]
                    || profiles.first().is_some_and(|profile| profile["application"] != route["name"])
                    || typed.first().is_some_and(|attachment| attachment["routeName"] != route["name"])
                    || route["appResource"] != reference["appTarget"]
                    || route["ticketResource"] != reference["ticketTarget"]
                    || route["dispatchSelectors"]["packageManifest"] != reference["manifestTarget"]
                    || route["dispatchSelectors"]["snapshotManifest"] != reference["snapshotTarget"]
                    || route["originalIssueReceipt"]["transactionId"]
                        != reference["issue"]["transactionId"]
                    || route["originalIssueReceipt"]["eventId"] != reference["issue"]["eventId"]
                    || route["originalIssueReceipt"]["acceptedCount"]
                        != reference["issue"]["acceptedCount"]
                    || route["originalIssueReceipt"]["worldRoot"] != reference["issue"]["worldRoot"]
                {
                    return Err("enrollment application reference, route and service do not share exact lineage".into());
                }
            } else if !refs.is_empty() || !profiles.is_empty() || !typed.is_empty() || refreshed != 1 {
                return Err("existing enrollment may refresh exactly one host unit only".into());
            }
            if av["lifetimeApiHostSha256"] != bv["lifetimeApiHostSha256"]
                && !(old_routes.is_empty() && av["lifetimeApiHostSha256"].is_null())
            {
                return Err("enrollment cannot replace source Host pin".into());
            }
            for field in [
                "registeredSharedApplications",
                "allowedApplicationLifetimeRoutes",
                "applicationServices",
                "typedApplications",
                "lifetimeApiHostSha256",
            ] {
                at.remove(field);
                bt.remove(field);
            }
        }
        _ => return Err("unknown application enrollment mode".into()),
    }
    if a != b {
        return Err("enrollment changes immutable controller authority or configuration".into());
    }
    Ok(())
}

fn command(config: &Config, args: &[String], directory: &Path, label: &str) -> Result<()> {
    let out = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(directory.join(format!("{label}.stdout")))
        .map_err(|e| e.to_string())?;
    let err = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .open(directory.join(format!("{label}.stderr")))
        .map_err(|e| e.to_string())?;
    let status = Command::new(&config.mini)
        .args(args)
        .stdout(out)
        .stderr(err)
        .status()
        .map_err(|e| e.to_string())?;
    if !status.success() {
        return Err(format!(
            "native enrollment {label} failed; retained read-only evidence"
        ));
    }
    Ok(())
}
fn native_args(config: &Config, verb: &str) -> Result<Vec<String>> {
    Ok(vec![
        verb.into(),
        "--host".into(),
        config.host.to_str().ok_or("Host path UTF-8")?.into(),
        "--config".into(),
        config
            .host_config
            .to_str()
            .ok_or("Host config path UTF-8")?
            .into(),
        "--socket".into(),
        config
            .host_socket
            .as_ref()
            .ok_or("Host socket absent")?
            .to_str()
            .ok_or("socket UTF-8")?
            .into(),
    ])
}
fn native_query(
    config: &Config,
    dir: &Path,
    label: &str,
    subject: &str,
    task: &str,
    capability: &str,
    key: &Path,
    view: &str,
) -> Result<(Value, Value)> {
    let nonce = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos()
        .to_string();
    let intent = dir.join(format!("{label}.json"));
    let attempt = dir.join(label);
    write_new(
        &intent,
        &bytes(
            &json!({"subject":subject,"nonce":nonce,"purpose":{"type":"query","kind":"object","target":task,"view":view},"grants":[{"kind":"object","target":task,"capability":capability}]}),
        )?,
    )?;
    let mut args = native_args(config, "query")?;
    for (flag, value) in [
        ("--intent", intent.as_path()),
        ("--key", key),
        ("--dir", attempt.as_path()),
    ] {
        args.extend([
            flag.into(),
            value.to_str().ok_or("native query path UTF-8")?.into(),
        ]);
    }
    args.extend(["--view".into(), view.into()]);
    command(config, &args, dir, label)?;
    Ok((
        serde_json::from_slice(&private(&attempt.join("view.json"), 1_048_576)?)
            .map_err(|e| e.to_string())?,
        serde_json::from_slice(&private(&attempt.join("challenge.json"), 1_048_576)?)
            .map_err(|e| e.to_string())?,
    ))
}
fn native_author(
    config: &Config,
    dir: &Path,
    label: &str,
    kind: &str,
    value: &Value,
) -> Result<Vec<u8>> {
    let input = dir.join(format!("{label}.json"));
    let output = dir.join(format!("{label}.bin"));
    write_new(&input, &bytes(value)?)?;
    let mut args = native_args(config, "author")?;
    args.extend([
        "--kind".into(),
        kind.into(),
        "--input".into(),
        input.to_str().ok_or("source UTF-8")?.into(),
        "--output".into(),
        output.to_str().ok_or("output UTF-8")?.into(),
    ]);
    command(config, &args, dir, label)?;
    private(&output, 131_072)
}
fn source_dispatch(config: &Config, dir: &Path) -> Result<()> {
    let dispatch = config.dispatch_task.as_ref().ok_or("dispatch absent")?;
    let tool = config.tool_task.as_ref().ok_or("tool absent")?;
    let (parent, _) = native_query(
        config,
        dir,
        "parent-current",
        &config.subject,
        &config.task,
        &config.query_capability,
        &config.custody_key,
        "resource",
    )?;
    let (purse, _) = native_query(
        config,
        dir,
        "dispatch-current",
        &dispatch.subject,
        &dispatch.task,
        &dispatch.query_capability,
        &dispatch.custody_key,
        "resource",
    )?;
    for (view, task) in [(&parent, &config.task), (&purse, &dispatch.task)] {
        let grain = &view["cell"]["grain"];
        if grain["task"] != *task
            || grain["generation"] != "0"
            || grain["status"] != "0"
            || grain["reserved"] != "0"
        {
            return Err(
                "bootstrap dispatch requires source-owned paused generation-zero tasks".into(),
            );
        }
    }
    let (policy, _) = native_query(
        config,
        dir,
        "parent-policy",
        &config.subject,
        &config.task,
        &config.query_capability,
        &config.custody_key,
        "policy",
    )?;
    if policy["policyId"] != config.task {
        return Err("source parent policy task differs".into());
    }
    let observed = native_author(
        config,
        dir,
        "observed-law",
        "predicate",
        &policy["predicate"],
    )?;
    let wanted = native_author(
        config,
        dir,
        "configured-law",
        "grain-policy",
        &json!({"owner":config.subject,"workerSubjects":[tool.subject,dispatch.subject],"workerGeneration":"1"}),
    )?;
    if observed != wanted {
        return Err(
            "source parent policy does not authorize exactly configured bootstrap workers".into(),
        );
    }
    Ok(())
}

fn live_routes(old: &Config, new: &Config, dir: &Path) -> Result<()> {
    let previous = &old
        .tool_task
        .as_ref()
        .ok_or("old tool absent")?
        .allowed_application_lifetime_routes;
    for route in &new
        .tool_task
        .as_ref()
        .ok_or("new tool absent")?
        .allowed_application_lifetime_routes
    {
        if previous
            .iter()
            .any(|prior| prior.name == route.name && prior.host_unit == route.host_unit)
        {
            continue;
        }
        let reply = application_api_tools::exchange_once(
            &route.socket_path,
            route.host_uid,
            &application_api_tools::lifetime_hello_request(),
            Instant::now() + Duration::from_secs(10),
        )
        .map_err(|e| format!("enrollment current lifetime endpoint: {e:?}"))?;
        application_api_tools::verify_lifetime_binding_reply(reply.clone(), route)?;
        write_new(
            &dir.join(format!("{}-binding.json", route.name)),
            &bytes(&reply)?,
        )?;
    }
    Ok(())
}

fn retained_state(
    record: &Value,
    id: &str,
    before: &[u8],
    after: &[u8],
    current: &[u8],
) -> Result<bool> {
    if record["protocol"] != PROTOCOL
        || record["requestSha256"] != id
        || record["beforeSha256"] != sha256_bytes(before)?
        || record["afterSha256"] != sha256_bytes(after)?
    {
        return Err("retained enrollment record differs from exact artifacts".into());
    }
    if current == after {
        Ok(true)
    } else if current == before {
        Ok(false)
    } else {
        Err("journal differs from both retained enrollment states".into())
    }
}

fn successor(current: &Value, target: &Config, config_path: &Path) -> Result<(Value, Vec<u8>)> {
    let mut after = current.clone();
    after["binding"] = json!({"config":target,"configPath":config_path});
    let encoded = serde_json::to_vec_pretty(&after).map_err(|e| e.to_string())?;
    Ok((after, encoded))
}

pub(crate) fn run(config_path: &Path, request_path: &Path) -> Result<Value> {
    let request_bytes = private(request_path, 8192)?;
    let request: Request = serde_json::from_slice(&request_bytes).map_err(|e| e.to_string())?;
    if request.protocol != PROTOCOL
        || [
            &request.expected_binding_sha256,
            &request.target_config_sha256,
        ]
        .iter()
        .any(|x| {
            x.len() != 64
                || !x
                    .bytes()
                    .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
        })
    {
        return Err("enrollment request protocol or exact digests invalid".into());
    }
    let target_bytes = private(config_path, 1_048_576)?;
    if sha256_bytes(&target_bytes)? != request.target_config_sha256 {
        return Err("installed target configuration digest differs".into());
    }
    let target: Config = serde_json::from_slice(&target_bytes).map_err(|e| e.to_string())?;
    if !config_path.is_absolute() || !target.state_dir.is_absolute() {
        return Err("enrollment requires absolute config and state paths".into());
    }
    directory(&target.state_dir)?;
    let lock_path = target.state_dir.join("controller.lock");
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&lock_path)
        .map_err(|e| e.to_string())?;
    let lock_meta = lock.metadata().map_err(|e| e.to_string())?;
    if !lock_meta.is_file()
        || lock_meta.uid() != unsafe { libc::geteuid() }
        || lock_meta.mode() & 0o077 != 0
        || lock_meta.nlink() != 1
    {
        return Err("controller lock is not private owned custody".into());
    }
    if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err("another controller owns this task".into());
    }
    let journal_path = target.state_dir.join("journal.json");
    let current_bytes = private(&journal_path, JOURNAL_LIMIT)?;
    let archive = target.state_dir.join("application-enrollments");
    directory(&archive)?;
    let id = sha256_bytes(&request_bytes)?;
    let record_dir = archive.join(&id);
    directory(&record_dir)?;
    retain(&record_dir.join("request.json"), &request_bytes)?;
    let record_path = record_dir.join("record.json");
    let mut source_bytes = current_bytes.clone();
    let mut retained_after = None;
    let mut replayed = false;
    if record_path.exists() {
        let record: Value =
            serde_json::from_slice(&private(&record_path, JOURNAL_LIMIT)?).map_err(|e| e.to_string())?;
        let before = private(&record_dir.join("before.json"), JOURNAL_LIMIT)?;
        let after = private(&record_dir.join("after.json"), JOURNAL_LIMIT)?;
        replayed = retained_state(&record, &id, &before, &after, &current_bytes)?;
        source_bytes = before;
        retained_after = Some(after);
    }
    let current: Value = serde_json::from_slice(&source_bytes).map_err(|e| e.to_string())?;
    // Preserve and inspect the raw field too: an older typed Journal does not
    // know it, so serializing that older type would otherwise erase the gate.
    if current
        .get("providerRetryGate")
        .is_some_and(|value| !value.is_null())
    {
        return Err("enrollment refuses retained provider retry work".into());
    }
    if digest(&current["binding"])? != request.expected_binding_sha256
        || current["binding"]["configPath"] != config_path.to_str().ok_or("config path UTF-8")?
    {
        return Err("source journal binding differs from expected enrollment".into());
    }
    let old: Config =
        serde_json::from_value(current["binding"]["config"].clone()).map_err(|e| e.to_string())?;
    if old.state_dir != target.state_dir {
        return Err("enrollment cannot move controller state".into());
    }
    let journal: Journal = serde_json::from_value(current.clone()).map_err(|e| e.to_string())?;
    if journal.format != "minidregg-grain-runtime-v1" {
        return Err("journal format differs".into());
    }
    let resident = quiescence::ResidentGuard::acquire(&target, request.resident_state.as_deref())?;
    let consumed = consumed_origin(&journal, &target, &resident)?;
    quiescent_with_origin(&journal, resident.evidence(), consumed.as_ref())?;
    if record_path.exists() {
        let record: Value = serde_json::from_slice(&private(&record_path,JOURNAL_LIMIT)?).map_err(|e|e.to_string())?;
        if record.get("consumedResidentOrigin") != consumed.as_ref().map(|proof| &proof.0) {
            return Err("retained enrollment resident consumption proof differs".into());
        }
    }
    permitted(&old, &target, &journal, &request.mode)?;
    validate(&target)?;
    journal.validate_birth_registry()?;
    journal.validate_application_api(&target.state_dir)?;
    journal.validate_foreground(&target.state_dir)?;
    journal.validate_workspace(&target)?;
    if !replayed {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|e| e.to_string())?
            .as_nanos();
        let proof = record_dir.join(format!("source-{nonce}"));
        directory(&proof)?;
        if request.mode == "bootstrap-dispatch" {
            source_dispatch(&target, &proof)?;
        } else {
            live_routes(&old, &target, &proof)?;
        }
    }
    let (after, after_bytes) = successor(&current, &target, config_path)?;
    if retained_after
        .as_ref()
        .is_some_and(|saved| saved != &after_bytes)
    {
        return Err("retained enrollment changed more than exact target binding".into());
    }
    if replayed {
        resident.assert_unchanged()?;
        if consumed_origin(&journal,&target,&resident)?.map(|p|p.0) != consumed.as_ref().map(|p|p.0.clone()) {
            return Err("resident terminal evidence changed during enrollment".into());
        }
        return Ok(
            json!({"protocol":PROTOCOL,"status":"enrolled","replayed":true,"requestSha256":id,"record":record_path,"bindingSha256":digest(&after["binding"])?}),
        );
    }
    retain(&record_dir.join("before.json"), &source_bytes)?;
    retain(&record_dir.join("after.json"), &after_bytes)?;
    let mut record = json!({"protocol":PROTOCOL,"requestSha256":id,"beforeSha256":sha256_bytes(&source_bytes)?,"afterSha256":sha256_bytes(&after_bytes)?});
    if let Some(proof)=&consumed { record["consumedResidentOrigin"]=proof.0.clone(); }
    retain(&record_path, &bytes(&record)?)?;
    // Re-read both public coordinates immediately before the sole atomic commit.
    if private(config_path, 1_048_576)? != target_bytes
        || private(&journal_path, JOURNAL_LIMIT)? != current_bytes
    {
        return Err("enrollment inputs changed before commit".into());
    }
    resident.assert_unchanged()?;
    if consumed_origin(&journal,&target,&resident)?.map(|p|p.0) != consumed.as_ref().map(|p|p.0.clone()) {
        return Err("resident terminal evidence changed during enrollment".into());
    }
    journal_io::write(&journal_path, &after_bytes)
        .map_err(|e| format!("enrollment journal publication: {e}"))?;
    Ok(
        json!({"protocol":PROTOCOL,"status":"enrolled","replayed":false,"requestSha256":id,"record":record_path,"bindingSha256":digest(&after["binding"])?}),
    )
}

#[cfg(test)]
#[path = "application_enrollment_adversary_tests.rs"]
mod adversary_tests;

#[cfg(test)]
mod publication_tests {
    use super::*;

    #[test]
    fn every_durable_archive_prefix_reenters_without_changing_prior_bytes() {
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "mini-enrollment-publication-{}-{nonce}",
            std::process::id()
        ));
        directory(&root).unwrap();
        let entries = [
            ("request.json", b"request".as_slice()),
            ("before.json", b"before".as_slice()),
            ("after.json", b"after".as_slice()),
            ("record.json", b"record".as_slice()),
        ];
        for prefix in 0..=entries.len() {
            let dir = root.join(prefix.to_string());
            directory(&dir).unwrap();
            for (name, data) in &entries[..prefix] {
                retain(&dir.join(name), data).unwrap();
            }
            // Re-enter at each durable boundary. journal_io's separately tested
            // atomic staging handles deaths within an individual publication.
            for (name, data) in &entries {
                retain(&dir.join(name), data).unwrap();
            }
            for (name, data) in &entries {
                assert_eq!(private(&dir.join(name), 100).unwrap(), *data);
            }
            assert!(retain(&dir.join("before.json"), b"different").is_err());
            assert_eq!(private(&dir.join("before.json"), 100).unwrap(), b"before");
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_before_and_after_recover_only_exact_commit_states() {
        let before = br#"{"binding":"old","nextOperationId":2}"#;
        let after = br#"{"binding":"new","nextOperationId":2}"#;
        let record = json!({"protocol":PROTOCOL,"requestSha256":"request",
            "beforeSha256":sha256_bytes(before).unwrap(),"afterSha256":sha256_bytes(after).unwrap()});
        assert!(!retained_state(&record, "request", before, after, before).unwrap());
        assert!(retained_state(&record, "request", before, after, after).unwrap());
        assert!(retained_state(&record, "other-request", before, after, after).is_err());
        assert!(
            retained_state(&record, "request", before, after, &after[..after.len() - 1]).is_err()
        );
        let mut changed = record.clone();
        changed["afterSha256"] = json!("wrong");
        assert!(retained_state(&changed, "request", before, after, after).is_err());
    }

    #[test]
    fn successor_preserves_every_nonbinding_field_and_unknown_retained_data() {
        let config: Config = serde_json::from_value(
            json!({"mini":"/mini","host":"/host","hostConfig":"/host.json",
            "controlSocket":"/control","custodyKey":"/key","stateDir":"/state","cwd":"/work",
            "task":"1","subject":"2","capability":"3","queryCapability":"4","commands":[]}),
        )
        .unwrap();
        let before = json!({"binding":{"old":true},"nextOperationId":45,"connection":"fenced",
            "bornResources":[{"nativeReceipt":"exact"}],"foregroundHistory":[{"requestId":"retained"}],
            "futureRetainedField":{"unknown":"preserved"}});
        let (mut after, encoded) =
            successor(&before, &config, Path::new("/controller.json")).unwrap();
        assert_eq!(serde_json::from_slice::<Value>(&encoded).unwrap(), after);
        assert_eq!(after["binding"]["configPath"], "/controller.json");
        after["binding"] = before["binding"].clone();
        assert_eq!(after, before);
    }
}
