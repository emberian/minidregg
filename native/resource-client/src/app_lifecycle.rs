//! Owner-signed lifecycle hosting delegation over ordinary current proposals.
//! Discovery and retained local phases are not authority. Source admission
//! checks each installed law and manager child capability at physical BEGIN.
use super::*;
use mini_sdk::lock::{Create, Lease, LockError, Wait};

struct QuietReplies(bool);
impl Drop for QuietReplies {
    fn drop(&mut self) {
        crate::QUIET_WORKER.store(self.0, std::sync::atomic::Ordering::Relaxed);
    }
}

const PROTOCOL: &str = "mini-member-app-lifecycle-v1";
const PHASES: [&str; 6] = [
    "app-policy",
    "package-policy",
    "snapshot-policy",
    "app-grant",
    "package-grant",
    "snapshot-grant",
];

// Complete-stage rename is serialized by the request lock. Existing final
// bytes are immutable; a crash before rename leaves no partially published plan.
fn retain(path: &Path, value: &Value) -> Result<()> {
    atomic_json(path, value, None)
}

fn directory(path: &Path) -> Result<()> {
    if path.exists() {
        private_dir(path)
    } else {
        make_private_dir(path)
    }
}

fn lock(path: &Path) -> Result<Lease> {
    request_lock(path, Create::Yes)
}

fn request_lock(path: &Path, create: Create) -> Result<Lease> {
    Lease::acquire(path, create, Wait::No).map_err(|error| match error {
        LockError::Busy => "lifecycle request busy; retain and retry the same request ID".to_owned(),
        LockError::Unsafe => "lifecycle lock has unsafe custody".to_owned(),
        LockError::Io(error) => error.to_string(),
    })
}

fn declaration(workspace: &Value, refs: &[Value; 3], manager: &str) -> Result<Value> {
    decimal(manager, "lifecycle manager")?;
    let owner = member(workspace, "subject")?;
    decimal(owner, "application owner")?;
    let mut targets = std::collections::BTreeSet::new();
    for r in refs {
        if member(r, "kind")? != "object" || !targets.insert(member(r, "target")?) {
            return Err(
                "lifecycle app/package/snapshot references must be distinct objects".into(),
            );
        }
        for key in [
            "target",
            "observeCapability",
            "operationCapability",
            "controlCapability",
        ] {
            let value = member(r, key)?;
            decimal(value, key)?;
            if key != "target" && value == "0" {
                return Err("lifecycle capability must be positive".into());
            }
        }
    }
    let stable: Vec<Value> = refs
        .iter()
        .map(|r| {
            json!({
        "name":r["name"],"kind":r["kind"],"target":r["target"],
        "observeCapability":r["observeCapability"],"operationCapability":r["operationCapability"],
        "controlCapability":r["controlCapability"]})
        })
        .collect();
    Ok(json!({"type":PROTOCOL,"owner":owner,"manager":manager,"references":stable}))
}

fn phase_dir(state: &Path, index: usize) -> PathBuf {
    state.join(PHASES[index])
}
fn proposal_id(id: &str, index: usize) -> String {
    format!("lifecycle-{id}-{index}")
}

fn confirmed(root: &Path, state: &Path, index: usize) -> Result<bool> {
    let phase = phase_dir(state, index);
    if !phase.join("prepared.json").exists() {
        return Ok(false);
    }
    let record = bounded_json(&phase.join("prepared.json"))?;
    let attempt = member_path(&record, "attempt")?;
    if !attempt.exists() {
        return Ok(false);
    }
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|e| e.to_string())?;
    if attempt.parent() != Some(attempts.as_path()) {
        return Err("lifecycle attempt outside workspace".into());
    }
    Ok(accepted_outcome(&attempt)?.is_some())
}

fn replace_preparation(path: &Path, prior: &Value, next: &Value) -> Result<()> {
    atomic_json(path, next, Some(prior))
}

fn prepare_phase(
    root: &Path,
    workspace: &Value,
    state: &Path,
    id: &str,
    decl: &Value,
    index: usize,
) -> Result<()> {
    let phase = phase_dir(state, index);
    directory(&phase)?;
    let saved = phase.join("prepared.json");
    let prior = if saved.exists() {
        let prior = bounded_json(&saved)?;
        let attempt = member_path(&prior, "attempt")?;
        if !attempt.exists() || attempt.join("call.bin").exists() {
            return Ok(());
        }
        if phase.join("submission-intent.json").exists() {
            return Err(
                "lifecycle submitted intent lacks retained call; exact recovery is required".into(),
            );
        }
        // This module invokes generic preparation with prepare_only=true.
        // A partial preparation without call and without our submission intent
        // has never requested an effect here. Preserve it and allocate a fresh
        // current proposal; never replace a submitted or uncertain operation.
        let archive = phase.join(format!("abandoned-preparation-{}.json", random_nonce()?));
        retain(
            &archive,
            &json!({"type":"mini-member-app-lifecycle-abandoned-preparation-v1",
            "reason":"prepare-only-interrupted","effectRequested":false,"prior":prior}),
        )?;
        Some(prior)
    } else {
        None
    };
    let refs = decl["references"]
        .as_array()
        .ok_or("lifecycle references absent")?;
    let slot = index % 3;
    let selected = &refs[slot];
    let name = member(selected, "name")?;
    let request_path = phase.join("request.json");
    let request = if request_path.exists() {
        bounded_json(&request_path)?
    } else if index < 3 {
        let input = json!({"kind":(["app","package","snapshot"][slot]),
            "app":member(&refs[0],"target")?,"packageManifest":member(&refs[1],"target")?,
            "snapshotManifest":member(&refs[2],"target")?,"owner":member(decl,"owner")?,"manager":member(decl,"manager")?});
        let input_path = phase.join("policy-input.json");
        retain(&input_path, &input)?;
        let host = member_path(workspace, "host")?;
        let config = member_path(workspace, "config")?;
        let binary = phase.join(format!("policy-{}.bin", random_nonce()?));
        author(
            &host,
            &config,
            OsStr::new("application-managed-policy"),
            &input_path,
            &binary,
        )?;
        // Always decode retained bytes through the strict source codec, including
        // exact retries after a pure authoring interruption.
        let output = phase.join(format!("policy-{}.json", random_nonce()?));
        let predicate = crate::inspect(&host, &config, "predicate", &binary, &output)?;
        json!({"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":name,"predicate":predicate})
    } else {
        let mut parent = selected.clone();
        parent["observeCapability"] = json!(member(selected, "operationCapability")?);
        let (cap, _, _) = signed_view(root, workspace, &parent, "capability")?;
        json!({"type":"minidregg-workspace-proposal-v1","action":"delegate","name":name,
            "recipient":member(decl,"manager")?,"verbs":["observe","mutate"],"maxCost":member(&cap["head"],"maxCost")?})
    };
    retain(&request_path, &request)?;
    let suffix = random_nonce()?;
    let proposal = format!("{}-{}", proposal_id(id, index), &suffix[..8]);
    let proposal_path = root.join("proposals").join(&proposal).join("proposal.json");
    let summary = if proposal_path.exists() {
        bounded_json(&proposal_path)?
    } else {
        propose_summary(root, workspace, &request_path, &proposal, None, false)?
    };
    // Persist the exact attempt identity before preparing any call. No phase
    // advances based on marker absence or merely successful client transport.
    let attempts = fs::canonicalize(root.join("attempts")).map_err(|e| e.to_string())?;
    let attempt = attempts.join(&proposal);
    let record = json!({"type":"mini-member-app-lifecycle-phase-v1","phase":PHASES[index],
        "proposal":proposal,"summary":summary,"attempt":attempt});
    if let Some(prior) = prior {
        replace_preparation(&saved, &prior, &record)?;
    } else {
        retain(&saved, &record)?;
    }
    Ok(())
}

fn publish_phase(root: &Path, phase: &Value) -> Result<()> {
    let proposal = member(phase, "proposal")?;
    let path = root
        .join("proposals")
        .join(proposal)
        .join("recipient-reference.json");
    if path.exists() {
        let reference = bounded_json(&path)?;
        let delegation = &phase["summary"]["delegation"];
        for (target, source) in [
            ("recipient", "recipient"),
            ("target", "target"),
            ("capability", "childCapability"),
        ] {
            if member(&reference, target)? != member(delegation, source)? {
                return Err("retained lifecycle recipient reference differs".into());
            }
        }
        return File::open(path.parent().ok_or("recipient reference lacks parent")?)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string());
    }
    publish_delegation(root, proposal, &member_path(phase, "attempt")?)
}

fn retain_discovery(path: &Path, workspace: &Value, refs: &[Value; 3], manager: &str) -> Result<()> {
    if path.exists() {
        let sample = bounded_json(path)?;
        let prior: [Value; 3] = sample["references"].as_array()
            .ok_or("initial lifecycle discovery references absent")?.clone().try_into()
            .map_err(|_| "initial lifecycle discovery must contain three references")?;
        if declaration(workspace, &prior, manager)?["references"] != declaration(workspace, refs, manager)?["references"] {
            return Err("initial lifecycle discovery authority changed before consent publication".into());
        }
        // Preserve the first discovery bytes, including historical metadata.
        // Exact replay fsyncs the parent if an earlier publication lost its ack.
        retain(path, &sample)
    } else {
        retain(path, &json!({"references":refs}))
    }
}

fn selectors(state: &Path, decl: &Value) -> Result<Value> {
    let mut caps = Vec::new();
    for index in 3..6 {
        let phase = bounded_json(&phase_dir(state, index).join("prepared.json"))?;
        caps.push(member(&phase["summary"]["delegation"], "childCapability")?.to_owned());
    }
    let refs = decl["references"]
        .as_array()
        .ok_or("lifecycle references absent")?;
    Ok(json!({"protocol":"mini-spk-grain-lifecycle-delegation-v1",
        "appOwner":member(decl,"owner")?,"managementSubject":member(decl,"manager")?,
        "selector":{"app":member(&refs[0],"target")?,"packageManifest":member(&refs[1],"target")?,
            "snapshotManifest":member(&refs[2],"target")?,"appCapability":caps[0],"appObserveCapability":caps[0],
            "packageCapability":caps[1],"packageObserveCapability":caps[1]},
        "snapshotCapability":caps[2],"snapshotObserveCapability":caps[2]}))
}

fn workflow_result(state: &Path, decl: &Value, id: &str, index: usize) -> Result<Value> {
    let mut result = json!({"type":"mini-member-app-lifecycle-result-v1","requestId":id,
        "complete":index == 6,"owner":member(decl,"owner")?,"manager":member(decl,"manager")?,
        "state":state,"origin":"member-retained-workflow","currentness":"retained-evidence",
        "authority":"requires-current-source-admission"});
    if index == 6 {
        let selector = state.join("management-selector.json");
        if selector.exists() {
            if bounded_json(&selector)? != selectors(state, decl)? {
                return Err("retained lifecycle selector differs from confirmed phases".into());
            }
            result["managementSelector"] = json!(selector);
        } else {
            result["selectorPublicationPending"] = json!(true);
            result["nextAction"] = json!("recover");
        }
    } else {
        result["phase"] = json!(PHASES[index]);
        let prepared = phase_dir(state,index).join("prepared.json");
        result["prepared"] = json!(prepared.exists());
        result["nextAction"] = json!("prepare");
        if prepared.exists() {
            let record = bounded_json(&prepared)?;
            let attempt = member_path(&record,"attempt")?;
            result["nextAction"] = json!(if attempt.join("call.bin").exists() {"recover"} else if attempt.exists() {"prepare"} else {"submit"});
        }
    }
    Ok(result)
}

/// Reads only this member's existing retained workflow. It never resolves a
/// live grant, advances a phase, signs a call, or publishes a manager selector.
pub(crate) fn retained_status(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    validate_name(id)?;
    if id.len() > 40 { return Err("lifecycle request ID exceeds 40 bytes".into()); }
    let base = root.join("app-lifecycle");
    private_dir(&base)?;
    let state = base.join(id);
    private_dir(&state)?;
    let _guard = request_lock(&state.join(".lock"), Create::No)?;
    let decl = bounded_json(&state.join("declaration.json"))?;
    let refs: [Value;3] = decl["references"].as_array().ok_or("lifecycle references absent")?
        .clone().try_into().map_err(|_| "lifecycle requires three references")?;
    if decl != declaration(workspace, &refs, member(&decl,"manager")?)? {
        return Err("retained lifecycle consent differs from current member".into());
    }
    let mut index = 0;
    while index < 6 {
        let phase = phase_dir(&state,index);
        if !phase.exists() { break; }
        private_dir(&phase)?;
        let prepared = phase.join("prepared.json");
        if !prepared.exists() { break; }
        let record = bounded_json(&prepared)?;
        let attempt = member_path(&record,"attempt")?;
        let attempts = fs::canonicalize(root.join("attempts")).map_err(|e|e.to_string())?;
        if attempt.parent() != Some(attempts.as_path()) {
            return Err("lifecycle attempt outside workspace".into());
        }
        if !attempt.exists() { break; }
        private_dir(&attempt)?;
        if !matches!(retained_attempt_outcome(&attempt)?, AttemptOutcome::Confirmed(_)) { break; }
        index += 1;
    }
    workflow_result(&state,&decl,id,index)
}

pub(super) fn run(root: &Path, workspace: &Value, mut args: Args) -> Result<()> {
    let _quiet = QuietReplies(crate::QUIET_WORKER.swap(true, std::sync::atomic::Ordering::Relaxed));
    let op = os_string(args.required("op")?, "lifecycle operation")?;
    if !matches!(op.as_str(), "prepare" | "submit" | "recover" | "status") {
        return Err("lifecycle op must be prepare, submit, recover, or status".into());
    }
    let id = os_string(args.required("request-id")?, "lifecycle request ID")?;
    validate_name(&id)?;
    if id.len() > 40 {
        return Err("lifecycle request ID exceeds 40 bytes".into());
    }
    let supplied = [
        args.optional("name"),
        args.optional("package-name"),
        args.optional("snapshot-name"),
        args.optional("manager"),
    ];
    args.finish()?;
    let base = root.join("app-lifecycle");
    directory(&base)?;
    let state = base.join(&id);
    directory(&state)?;
    let _guard = lock(&state.join(".lock"))?;
    let retained = state.join("declaration.json");
    let (names, manager) = if supplied.iter().all(Option::is_some) {
        let mut text = supplied
            .into_iter()
            .map(|v| os_string(v.unwrap(), "lifecycle selector"))
            .collect::<Result<Vec<_>>>()?;
        let manager = text.pop().unwrap();
        ([text[0].clone(), text[1].clone(), text[2].clone()], manager)
    } else if supplied.iter().any(Option::is_some) {
        return Err(
            "initial lifecycle selectors require all of name, package-name, snapshot-name, manager"
                .into(),
        );
    } else {
        let prior = bounded_json(&retained)?;
        (
            [
                member(&prior["references"][0], "name")?.to_owned(),
                member(&prior["references"][1], "name")?.to_owned(),
                member(&prior["references"][2], "name")?.to_owned(),
            ],
            member(&prior, "manager")?.to_owned(),
        )
    };
    let refs = [
        reference(root, &names[0])?,
        reference(root, &names[1])?,
        reference(root, &names[2])?,
    ];
    let decl = declaration(workspace, &refs, &manager)?;
    if !retained.exists() {
        retain_discovery(&state.join("initial-discovery.json"), workspace, &refs, &manager)?;
    }
    retain(&retained, &decl)?;
    let mut index = 0;
    while index < 6 && confirmed(root, &state, index)? {
        index += 1;
    }
    if index < 6 && op == "prepare" {
        prepare_phase(root, workspace, &state, &id, &decl, index)?;
    }
    if index < 6 && matches!(op.as_str(), "submit" | "recover") {
        let phase_path = phase_dir(&state, index).join("prepared.json");
        if !phase_path.exists() {
            return Err("prepare the current lifecycle phase before submit/recover".into());
        }
        let phase = bounded_json(&phase_path)?;
        let attempt = member_path(&phase, "attempt")?;
        if attempt.exists() {
            if !attempt.join("call.bin").is_file() {
                return Err(format!("lifecycle preparation incomplete before submission; run prepare with the same request ID to retain and replace this prepare-only attempt {}; no lifecycle effect was requested",attempt.display()));
            }
            // Explicit submit reuses the exact generic admitted operation ID;
            // recover is lookup-only and never resubmits an uncertain effect.
            if op == "submit" {
                retain(
                    &phase_dir(&state, index).join("submission-intent.json"),
                    &json!({"attempt":attempt,"callSha256":format!("{:x}",Sha256::digest(fs::read(attempt.join("call.bin")).map_err(|e|e.to_string())?))}),
                )?;
            }
            retry(
                &attempt,
                if op == "recover" { "lookup" } else { "submit" },
                false,
            )?;
        } else if op == "recover" {
            return Err("lifecycle phase has not prepared/submitted a call".into());
        } else {
            let source = member_path(&phase["summary"], "intentPath")?;
            let bytes = fs::read(&source).map_err(|e| e.to_string())?;
            if format!("{:x}", Sha256::digest(&bytes)) != member(&phase["summary"], "intentSha256")?
            {
                return Err("retained lifecycle intent differs from exact prepared source".into());
            }
            // Preparation never submits. Once a complete durable call exists,
            // every effect/recovery path below operates on that exact call.
            submit_intent(root, workspace, &source, "intent", true, Some(&attempt))?;
            retain(
                &phase_dir(&state, index).join("submission-intent.json"),
                &json!({"attempt":attempt,"callSha256":format!("{:x}",Sha256::digest(fs::read(attempt.join("call.bin")).map_err(|e|e.to_string())?))}),
            )?;
            retry(&attempt, "submit", false)?;
        }
        if accepted_outcome(&attempt)?.is_some() {
            if index >= 3 {
                publish_phase(root, &phase)?;
            }
            index += 1;
        }
    }
    // A reply can be lost after admission but before delegation publication.
    // Repair publication from the retained exact receipt without new authority.
    if op != "status" {
        for phase_index in 3..index {
            let phase = bounded_json(&phase_dir(&state, phase_index).join("prepared.json"))?;
            publish_phase(root, &phase)?;
        }
    }
    if index == 6 {
        retain(&state.join("management-selector.json"), &selectors(&state, &decl)?)?;
    }
    let result = workflow_result(&state, &decl, &id, index)?;
    println!(
        "{}",
        serde_json::to_string_pretty(&result).map_err(|e| e.to_string())?
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn refs() -> [Value; 3] {
        std::array::from_fn(|i| {
            json!({"name":format!("app-{i}"),"kind":"object","target":(530101+i).to_string(),
            "observeCapability":(960000+i).to_string(),"operationCapability":(960000+i).to_string(),"controlCapability":(960010+i).to_string()})
        })
    }
    fn status_fixture() -> (PathBuf,PathBuf,Value) {
        let root = std::env::temp_dir().join(format!("app-lifecycle-status-{}",random_nonce().unwrap()));
        directory(&root).unwrap();
        directory(&root.join("attempts")).unwrap();
        directory(&root.join("app-lifecycle")).unwrap();
        let state = root.join("app-lifecycle/one");
        directory(&state).unwrap();
        drop(lock(&state.join(".lock")).unwrap());
        let workspace = json!({"subject":"7"});
        retain(&state.join("declaration.json"),&declaration(&workspace,&refs(),"8").unwrap()).unwrap();
        (root,state,workspace)
    }
    fn status_phase(root: &Path,state: &Path,index: usize) -> PathBuf {
        let phase = phase_dir(state,index);
        directory(&phase).unwrap();
        let attempt = root.join("attempts").join(format!("phase-{index}"));
        directory(&attempt).unwrap();
        create_private(&attempt.join("call.bin"),b"exact").unwrap();
        retain(&phase.join("prepared.json"),&json!({"attempt":attempt,
            "summary":{"delegation":{"childCapability":(980000+index).to_string()}}})).unwrap();
        attempt
    }
    #[test]
    fn retained_status_never_creates_absent_requests_and_refuses_foreign_owner() {
        let (root,state,workspace) = status_fixture();
        assert!(retained_status(&root,&workspace,"missing").is_err());
        assert!(!root.join("app-lifecycle/missing").exists());
        let before: std::collections::BTreeSet<_> = fs::read_dir(&state).unwrap().map(|r|r.unwrap().file_name()).collect();
        let first = retained_status(&root,&workspace,"one").unwrap();
        assert_eq!(first["phase"],"app-policy");
        assert_eq!(first["nextAction"],"prepare");
        assert!(retained_status(&root,&json!({"subject":"9"}),"one").is_err());
        let after: std::collections::BTreeSet<_> = fs::read_dir(&state).unwrap().map(|r|r.unwrap().file_name()).collect();
        assert_eq!(before,after);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn retained_status_preserves_exact_uncertainty_without_continuity_writes() {
        let (root,state,workspace) = status_fixture();
        let attempt = status_phase(&root,&state,0);
        retain(&attempt.join("outcome.json"),&json!({"type":"refused"})).unwrap();
        retain(&attempt.join("retry-0001.json"),&json!({"type":"uncertain"})).unwrap();
        let before: std::collections::BTreeSet<_> = fs::read_dir(&attempt).unwrap().map(|r|r.unwrap().file_name()).collect();
        let result = retained_status(&root,&workspace,"one").unwrap();
        assert_eq!(result["phase"],"app-policy");
        assert_eq!(result["nextAction"],"recover");
        let after: std::collections::BTreeSet<_> = fs::read_dir(&attempt).unwrap().map(|r|r.unwrap().file_name()).collect();
        assert_eq!(before,after);
        assert!(!root.join("receipt-continuity").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn retained_status_repairs_only_an_incomplete_unsubmitted_preparation() {
        let (root,state,workspace) = status_fixture();
        let attempt = status_phase(&root,&state,0);
        fs::remove_file(attempt.join("call.bin")).unwrap();
        let result = retained_status(&root,&workspace,"one").unwrap();
        assert_eq!(result["nextAction"],"prepare");
        assert!(!attempt.join("call.bin").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn retained_status_keeps_completed_selector_publication_pending() {
        let (root,state,workspace) = status_fixture();
        for index in 0..6 {
            let attempt = status_phase(&root,&state,index);
            retain(&attempt.join("outcome.json"),&json!({"type":"confirmed","confirmation":"installed"})).unwrap();
        }
        let result = retained_status(&root,&workspace,"one").unwrap();
        assert_eq!(result["complete"],true);
        assert_eq!(result["selectorPublicationPending"],true);
        assert_eq!(result["nextAction"],"recover");
        assert!(result.get("managementSelector").is_none());
        assert!(!state.join("management-selector.json").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn owner_zero_and_distinct_manager_are_bound_without_transfer() {
        let d = declaration(&json!({"subject":"0"}), &refs(), "8").unwrap();
        assert_eq!(d["owner"], "0");
        assert_eq!(d["manager"], "8");
    }
    #[test]
    fn missing_owner_control_and_cross_resource_alias_refuse() {
        let mut r = refs();
        r[1]["target"] = r[0]["target"].clone();
        assert!(declaration(&json!({"subject":"7"}), &r, "8").is_err());
        let mut r = refs();
        r[0].as_object_mut().unwrap().remove("controlCapability");
        assert!(declaration(&json!({"subject":"7"}), &r, "8").is_err());
        assert!(declaration(&json!({"subject":"7"}), &refs(), "08").is_err());
    }
    #[test]
    fn discovery_metadata_changes_do_not_change_retained_authority() {
        let mut before = refs();
        before[0]["sharedName"] = json!("before");
        let mut after = before.clone();
        after[0]["sharedName"] = json!("after");
        after[0]["provenance"] = json!({"browser":"now available"});
        let owner = json!({"subject":"7"});
        assert_eq!(
            declaration(&owner, &before, "8").unwrap(),
            declaration(&owner, &after, "8").unwrap()
        );
        after[0]["target"] = json!("531101");
        assert_ne!(
            declaration(&owner, &before, "8").unwrap(),
            declaration(&owner, &after, "8").unwrap()
        );
    }
    #[test]
    fn first_discovery_cut_preserves_bytes_and_stable_consent() {
        let temp = std::env::temp_dir().join(format!("app-lifecycle-discovery-{}", random_nonce().unwrap()));
        directory(&temp).unwrap();
        let _guard = lock(&temp.join(".lock")).unwrap();
        let path = temp.join("initial-discovery.json");
        let owner = json!({"subject":"7"});
        let mut initial = refs();initial[0]["sharedName"]=json!("first");
        retain_discovery(&path,&owner,&initial,"8").unwrap();
        let bytes=fs::read(&path).unwrap();
        // Crash before declaration publication; current discovery has evolved.
        let mut current=initial.clone();current[0]["sharedName"]=json!("later");
        current[0]["provenance"]=json!({"browser":"available"});
        retain_discovery(&path,&owner,&current,"8").unwrap();
        assert_eq!(fs::read(&path).unwrap(),bytes);
        current[0]["target"]=json!("531101");
        assert!(retain_discovery(&path,&owner,&current,"8").is_err());
        assert_eq!(fs::read(&path).unwrap(),bytes);
        fs::remove_dir_all(temp).unwrap();
    }
    #[test]
    fn exclusive_request_lock_is_bounded_and_recoverable() {
        let temp =
            std::env::temp_dir().join(format!("app-lifecycle-lock-{}", random_nonce().unwrap()));
        directory(&temp).unwrap();
        let path = temp.join(".lock");
        let first = lock(&path).unwrap();
        assert!(lock(&path).is_err());
        drop(first);
        let second = lock(&path).unwrap();
        drop(second);
        fs::remove_dir_all(temp).unwrap();
    }
    #[test]
    fn replacement_requires_exact_prior_phase_and_keeps_old_evidence() {
        let temp =
            std::env::temp_dir().join(format!("app-lifecycle-replace-{}", random_nonce().unwrap()));
        directory(&temp).unwrap();
        let _guard = lock(&temp.join(".lock")).unwrap();
        let p = temp.join("prepared.json");
        let old = json!({"attempt":"old"});
        let next = json!({"attempt":"new"});
        retain(&p, &old).unwrap();
        retain(&temp.join("abandoned.json"), &old).unwrap();
        assert!(replace_preparation(&p, &next, &json!({"attempt":"other"})).is_err());
        replace_preparation(&p, &old, &next).unwrap();
        assert_eq!(bounded_json(&p).unwrap(), next);
        assert_eq!(bounded_json(&temp.join("abandoned.json")).unwrap(), old);
        fs::remove_dir_all(temp).unwrap();
    }
    #[test]
    fn immutable_phase_publication_survives_owned_orphan_stage() {
        let temp = std::env::temp_dir().join(format!("app-lifecycle-{}", random_nonce().unwrap()));
        directory(&temp).unwrap();
        let _guard = lock(&temp.join(".lock")).unwrap();
        let p = temp.join("record.json");
        let v = json!({"attempt":"exact"});
        create_private(&temp.join(".stage-orphan"), b"torn").unwrap();
        retain(&p, &v).unwrap();
        retain(&p, &v).unwrap();
        assert!(retain(&p, &json!({"attempt":"other"})).is_err());
        fs::remove_dir_all(temp).unwrap();
    }
}
