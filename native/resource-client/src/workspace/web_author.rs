//! Browser editing is a client of the ordinary document diff and admission path.
//! Each tab retains its own signed base; no shared `seen/NAME` slot is consulted.
//! A durable start record precedes submission. Repeated POSTs only read that
//! operation; uncertain operations may be looked up, never silently resubmitted.

use super::*;

#[path = "../web_actions.rs"]
pub(crate) mod actions;

const SESSION_TYPE: &str = "mini-web-edit-v2";
const LEGACY_SESSION_TYPE: &str = "mini-web-edit-v1";

pub(crate) struct Edit {
    pub id: String,
    pub name: String,
    pub text: String,
    pub height: String,
    pub authority_root: String,
    pub cell_root: String,
    pub preview: String,
    pub status: String,
    pub message: String,
    pub outcome: Option<Value>,
    pub action: Option<Value>,
    pub structure: String,
}

fn directory(root: &Path, id: &str) -> Result<PathBuf> {
    if id.len() != 32 || !id.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid edit session".into());
    }
    Ok(root.join("web-edits").join(id))
}

fn save(path: &Path, value: &Value) -> Result<()> {
    create_private(path, &serde_json::to_vec(value).map_err(|e| e.to_string())?)
}

pub(crate) fn open(root: &Path, workspace: &Value, name: &str) -> Result<Edit> {
    validate_name(name)?;
    let (read, rendered) = read_rendered(root, workspace, name, None)?;
    content_page(&read.view, name)?;
    let challenge = bounded_json(&read.attempt.join("challenge.json"))?;
    let seen = seen_read_value(name, &read, &challenge);
    let text = String::from_utf8(pull_text(&seen)?).map_err(|_| {
        "this document contains non-UTF-8 text; use the byte-preserving CLI editor".to_owned()
    })?;
    if text.contains('\r') {
        return Err(
            "this document contains carriage-return bytes; use the byte-preserving CLI editor"
                .into(),
        );
    }
    let parent = root.join("web-edits");
    if !parent.exists() {
        make_private_dir(&parent)?;
    }
    private_dir(&parent)?;
    let token = crate::fsio::random::<16>()?;
    let id = hex(&token);
    let dir = directory(root, &id)?;
    make_private_dir(&dir)?;
    let reference = reference(root, name)?;
    save(
        &dir.join("session.json"),
        &json!({"type":SESSION_TYPE,"id":id,"name":name,
        "subject":member(workspace,"subject")?, "reference":reference, "seen":seen,
        "text":text,"preview":rendered.html(name),"authorityRoot":challenge["authorityRoot"],"cellRoot":read.view["cell"]["root"]}),
    )?;
    load(root, workspace, name, &id)
}

fn retained(root: &Path, workspace: &Value, name: &str, id: &str) -> Result<(PathBuf, Value)> {
    let dir = directory(root, id)?;
    private_dir(&dir)?;
    let session = bounded_json_limit(&dir.join("session.json"), MAX_SEEN * 2)?;
    if !matches!(
        session["type"].as_str(),
        Some(SESSION_TYPE | LEGACY_SESSION_TYPE)
    ) || session["id"] != id
        || session["name"] != name
        || session["subject"] != member(workspace, "subject")?
    {
        return Err("edit session does not belong to this document and subject".into());
    }
    // A workspace alias may be rebound while a browser tab is open. Its held
    // capability slots must not turn the retained edit into another operation.
    if session["reference"] != reference(root, name)? {
        return Err("this document reference changed; open a new editor".into());
    }
    Ok((dir, session))
}

pub(crate) fn load(root: &Path, workspace: &Value, name: &str, id: &str) -> Result<Edit> {
    let (dir, session) = retained(root, workspace, name, id)?;
    let started = dir.join("started.json");
    let mut edit = Edit {
        id: id.into(),
        name: name.into(),
        text: member(&session, "text")?.into(),
        height: member(&session["seen"], "height")?.into(),
        authority_root: session["authorityRoot"]
            .as_str()
            .unwrap_or("not retained in this older draft")
            .into(),
        cell_root: session["cellRoot"]
            .as_str()
            .or_else(|| session["seen"]["view"]["cell"]["root"].as_str())
            .unwrap_or("?")
            .into(),
        preview: member(&session, "preview")?.into(),
        status: "editing".into(),
        message: String::new(),
        outcome: None,
        action: None,
        structure: actions::structure(&session["seen"]),
    };
    if started.exists() {
        let start = bounded_json(&started)?;
        edit.text = member(&start, "text")?.into();
        edit.action = start.get("action").filter(|a| !a.is_null()).cloned();
        edit.status = "uncertain".into();
        edit.message = "This save started. Its exact outcome is not yet known. Check the retained operation before making another save.".into();
        let attempt = member_path(&start, "attempt")?;
        if attempt.exists() {
            if let Some(outcome) = accepted_outcome(&attempt)? {
                edit.status = "saved".into();
                edit.message = "Saved. The Store confirmed this exact operation.".into();
                edit.outcome = Some(outcome);
            }
        }
    }
    let result = if dir.join("pre-submit-stopped.json").exists() {
        dir.join("pre-submit-stopped.json")
    } else {
        dir.join("result.json")
    };
    if result.exists() && edit.status != "saved" {
        let result = bounded_json(&result)?;
        edit.status = member(&result, "status")?.into();
        edit.message = member(&result, "message")?.into();
    }
    Ok(edit)
}

pub(crate) fn submit(
    root: &Path,
    workspace: &Value,
    name: &str,
    id: &str,
    text: &str,
) -> Result<Edit> {
    submit_operation(root, workspace, name, id, Some(text), None)
}

pub(crate) fn submit_action(
    root: &Path,
    workspace: &Value,
    name: &str,
    id: &str,
    action: &Value,
) -> Result<Edit> {
    actions::validate(action)?;
    submit_operation(root, workspace, name, id, None, Some(action))
}

fn submit_operation(
    root: &Path,
    workspace: &Value,
    name: &str,
    id: &str,
    text: Option<&str>,
    action: Option<&Value>,
) -> Result<Edit> {
    let (dir, session) = retained(root, workspace, name, id)?;
    let text = text.unwrap_or(member(&session, "text")?);
    let _writer = crate::transport::service_lock(&dir.join("save.lock"))?;
    if dir.join("started.json").exists() {
        let start = bounded_json(&dir.join("started.json"))?;
        if start["text"] != text || start.get("action").filter(|a| !a.is_null()) != action {
            return Err("this editor already started different work; its retained operation must be resolved first".into());
        }
        return load(root, workspace, name, id);
    }
    if session["type"] != SESSION_TYPE {
        return Err(
            "this draft predates durable save ownership; copy it into a freshly opened editor"
                .into(),
        );
    }
    let (attempt, _) = new_attempt(root)?;
    let proposal = format!("web-{id}");
    // Retain the exact authored operation before reads, preparation or submission.
    save(
        &dir.join("started.json"),
        &json!({"text":text,"action":action,"attempt":attempt,"proposal":proposal}),
    )?;
    crate::take_host_decision();
    let mut text_plan = None;
    let result = (|| -> Result<()> {
        let request = match action {
            Some(action) => actions::plan(root, workspace, name, &session["seen"], action)?,
            None => {
                let plan = push_actions(&session["seen"], text.as_bytes())?;
                if plan.actions.is_empty() {
                    save(
                        &dir.join("result.json"),
                        &json!({"status":"unchanged","message":"No changes to save. Nothing was submitted."}),
                    )?;
                    return Ok(());
                }
                let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                    "targets":[{"name":name,"payload":{"type":"content","actions":plan.actions}}]});
                text_plan = Some(plan);
                request
            }
        };
        propose_request(root, workspace, &request, &proposal, None, false)?;
        submit_intent(
            root,
            workspace,
            &root.join("proposals").join(&proposal).join("intent.json"),
            "intent",
            false,
            Some(&attempt),
        )
    })();
    if let Err(error) = result {
        let decided = crate::take_host_decision().is_some();
        let detail = if decided {
            text_plan
                .as_ref()
                .and_then(|plan| {
                    stale_lines(root, workspace, name, &session["seen"], plan)
                        .ok()
                        .flatten()
                })
                .unwrap_or_else(|| crate::web::refusal_text(&error).unwrap_or(error))
        } else {
            error
        };
        let status = if decided {
            "refused"
        } else if !attempt.join("call.bin").exists() {
            "failed"
        } else {
            "uncertain"
        };
        let message = match status {
            "refused" => format!("The Store refused this operation: {detail}. Your draft and authored action remain below."),
            "failed" => format!("The client could not prepare this operation: {detail}. Nothing was submitted. Your draft and authored action remain below."),
            _ => format!("The reply was interrupted: {detail}. Check the exact outcome; your draft and authored action remain below."),
        };
        save(
            &dir.join("result.json"),
            &json!({"status":status,"message":message}),
        )?;
    }
    load(root, workspace, name, id)
}

/// Recent authenticated turn metadata, without replaying each historical body.
/// Detailed content stays on the existing history/diff routes.
pub(crate) fn recent_turns(root: &Path, workspace: &Value, name: &str) -> Result<Vec<Value>> {
    let reference = reference(root, name)?;
    let target = member(&reference, "target")?;
    let (since, _) = doc_query(
        root,
        workspace,
        &reference,
        "since",
        Some("0"),
        "view-since",
    )?;
    let entries = since["entries"]
        .as_array()
        .ok_or("signed history lacks entries")?;
    let mut rows: Vec<_> = entries
        .iter()
        .filter(|entry| {
            entry["cells"]
                .as_array()
                .is_some_and(|cells| cells.iter().any(|cell| cell.as_str() == Some(target)))
        })
        .cloned()
        .collect();
    if rows.len() > 5 {
        rows.drain(..rows.len() - 5);
    }
    rows.reverse();
    Ok(rows)
}

pub(crate) fn lookup(root: &Path, workspace: &Value, name: &str, id: &str) -> Result<Edit> {
    let (dir, session) = retained(root, workspace, name, id)?;
    // This physical lock is held from before start through the last submit
    // reply. Acquiring it proves no conforming writer remains in flight.
    let _writer = crate::transport::service_lock(&dir.join("save.lock"))?;
    let current = load(root, workspace, name, id)?;
    if current.status != "uncertain" {
        return Ok(current);
    }
    let start = bounded_json(&dir.join("started.json"))?;
    let attempt = member_path(&start, "attempt")?;
    let call_exists = match fs::symlink_metadata(attempt.join("call.bin")) {
        Ok(_) => true,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
        Err(error) => {
            return Err(format!(
                "cannot establish whether the exact call exists: {error}"
            ))
        }
    };
    if session["type"] == SESSION_TYPE && !call_exists {
        // The client fsyncs call.bin before invoking submit. A stopped writer
        // with no call never crossed that boundary. Never synthesize a retry.
        let result = dir.join("pre-submit-stopped.json");
        if !result.exists() {
            save(
                &result,
                &json!({"status":"failed","message":"This save stopped before submission. Nothing was submitted. Your draft remains below; open the current version to continue editing."}),
            )?;
        }
        return load(root, workspace, name, id);
    }
    if call_exists {
        // Lookup never appends a new event and never constructs a new intent.
        let _ = recover(root, &attempt);
    }
    load(root, workspace, name, id)
}

#[cfg(test)]
mod tests {
    use super::*;
    const ID: &str = "0123456789abcdef0123456789abcdef";

    fn session() -> (PathBuf, Value, PathBuf) {
        let root = std::env::temp_dir().join(format!(
            "mini-web-edit-test-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        for child in ["refs", "attempts", "web-edits"] {
            make_private_dir(&root.join(child)).unwrap();
        }
        let reference = json!({"type":"minidregg-participant-reference-v1","name":"paper","kind":"object","target":"7","observeCapability":"8","operationCapability":"9"});
        save(&root.join("refs/paper.json"), &reference).unwrap();
        let dir = directory(&root, ID).unwrap();
        make_private_dir(&dir).unwrap();
        save(&dir.join("session.json"),&json!({"type":SESSION_TYPE,"id":ID,"name":"paper","subject":"11","reference":reference,"seen":{"height":"12"},"text":"original\n","preview":"<p>original</p>"})).unwrap();
        let workspace = json!({"subject":"11"});
        (root, workspace, dir)
    }

    #[test]
    fn repeated_save_is_read_only_even_after_restart_or_lost_reply() {
        let (root, workspace, dir) = session();
        let attempt = root.join("attempts/a-pinned");
        save(
            &dir.join("started.json"),
            &json!({"text":"saved text\n","attempt":attempt,"proposal":"pinned"}),
        )
        .unwrap();
        // The snapshot intentionally cannot produce a diff, and no Host or key
        // exists. A retry must return retained state without preparing anything.
        let edit = submit(&root, &workspace, "paper", ID, "saved text\n").unwrap();
        assert_eq!(edit.status, "uncertain");
        assert_eq!(edit.text, "saved text\n");
        assert!(!attempt.exists());
        assert!(!root.join("proposals").exists());
        assert!(submit(&root, &workspace, "paper", ID, "different\n").is_err());
        assert_eq!(
            lookup(&root, &workspace, "paper", ID).unwrap().status,
            "failed"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn exact_confirmed_outcome_supersedes_interrupted_status_and_keeps_draft() {
        let (root, workspace, dir) = session();
        let attempt = root.join("attempts/a-pinned");
        make_private_dir(&attempt).unwrap();
        save(
            &dir.join("started.json"),
            &json!({"text":"saved text\n","attempt":attempt,"proposal":"pinned"}),
        )
        .unwrap();
        save(
            &dir.join("result.json"),
            &json!({"status":"uncertain","message":"connection interrupted"}),
        )
        .unwrap();
        save(
            &attempt.join("outcome.json"),
            &json!({"type":"confirmed","confirmation":"installed","height":"13"}),
        )
        .unwrap();
        let edit = load(&root, &workspace, "paper", ID).unwrap();
        assert_eq!(edit.status, "saved");
        assert_eq!(edit.text, "saved text\n");
        assert_eq!(edit.outcome.unwrap()["height"], "13");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn connection_action_retries_recover_exact_identity_without_new_source_reads() {
        let (root, workspace, dir) = session();
        let action = json!({"type":"transclude","source":"source","from":"1","to":"2","mode":"snapshot","death":"invalidate"});
        let attempt = root.join("attempts/pinned-action");
        save(
            &dir.join("started.json"),
            &json!({"text":"original\n","action":action,"attempt":attempt,"proposal":"pinned"}),
        )
        .unwrap();
        // No source, Host or key exists: repeated POST must use only retained work.
        let edit = submit_action(&root, &workspace, "paper", ID, &action).unwrap();
        assert_eq!(edit.status, "uncertain");
        assert_eq!(edit.action, Some(action.clone()));
        let mut changed = action.clone();
        changed["mode"] = json!("live");
        assert!(submit_action(&root, &workspace, "paper", ID, &changed).is_err());
        assert!(submit(&root, &workspace, "paper", ID, "original\n").is_err());
        assert!(!root.join("proposals").exists());
        assert_eq!(
            lookup(&root, &workspace, "paper", ID).unwrap().status,
            "failed"
        );
        assert_eq!(
            load(&root, &workspace, "paper", ID).unwrap().action,
            Some(action)
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn active_writer_prevents_abandonment_and_old_sessions_remain_uncertain() {
        let (root, workspace, dir) = session();
        save(
            &dir.join("started.json"),
            &json!({"text":"draft","attempt":root.join("attempts/a-pinned"),"proposal":"pinned"}),
        )
        .unwrap();
        let owner = crate::transport::service_lock(&dir.join("save.lock")).unwrap();
        assert!(lookup(&root, &workspace, "paper", ID).is_err());
        assert!(!dir.join("pre-submit-stopped.json").exists());
        drop(owner);
        assert_eq!(
            lookup(&root, &workspace, "paper", ID).unwrap().status,
            "failed"
        );
        assert_eq!(load(&root, &workspace, "paper", ID).unwrap().text, "draft");
        fs::remove_dir_all(root).unwrap();

        let (root, workspace, dir) = session();
        let mut old = bounded_json(&dir.join("session.json")).unwrap();
        old["type"] = json!(LEGACY_SESSION_TYPE);
        fs::write(dir.join("session.json"), serde_json::to_vec(&old).unwrap()).unwrap();
        save(
            &dir.join("started.json"),
            &json!({"text":"old draft","attempt":root.join("attempts/a-old"),"proposal":"old"}),
        )
        .unwrap();
        assert_eq!(
            lookup(&root, &workspace, "paper", ID).unwrap().status,
            "uncertain"
        );
        assert!(!dir.join("pre-submit-stopped.json").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn retained_session_binds_document_subject_and_capability_reference() {
        let (root, workspace, dir) = session();
        assert!(load(&root, &json!({"subject":"12"}), "paper", ID).is_err());
        assert!(load(&root, &workspace, "other", ID).is_err());
        let mut session = bounded_json(&dir.join("session.json")).unwrap();
        session["reference"]["target"] = json!("99");
        // Mutate only this test's fixture reference, never the immutable session.
        fs::write(
            root.join("refs/paper.json"),
            serde_json::to_vec(&session["reference"]).unwrap(),
        )
        .unwrap();
        assert!(load(&root, &workspace, "paper", ID).is_err());
        for id in ["../paper", "0", "0123456789abcdef0123456789abcdeg"] {
            assert!(directory(&root, id).is_err());
        }
        fs::remove_dir_all(root).unwrap();
    }
}
