//! Browser document creation keeps birth and tree initialization as two exact
//! operations. Lookup never advances into a new operation.
use super::*;

fn dir(root: &Path, id: &str) -> Result<PathBuf> {
    if id.len() != 32 || !id.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("invalid creation session".into());
    }
    Ok(root.join("web-creates").join(id))
}
fn save(path: &Path, value: &Value) -> Result<()> {
    create_private(path, &serde_json::to_vec(value).map_err(|e| e.to_string())?)
}
fn session(root: &Path, workspace: &Value, id: &str) -> Result<(PathBuf, Value)> {
    let d = dir(root, id)?;
    private_dir(&d)?;
    let s = bounded_json(&d.join("session.json"))?;
    if s["type"] != "mini-web-create-v1"
        || s["id"] != id
        || s["subject"] != member(workspace, "subject")?
    {
        return Err("creation session belongs to another member".into());
    }
    if let Some(room) = s["room"].as_str() {
        if reference(root, room)? != s["roomReference"] {
            return Err(
                "room reference changed; retain this operation and open a new creation form".into(),
            );
        }
    }
    Ok((d, s))
}
pub(crate) fn open(root: &Path, workspace: &Value, room: Option<&str>) -> Result<Value> {
    let room_reference = room.map(|name| reference(root, name)).transpose()?;
    if let Some(r) = &room_reference {
        signed_view(root, workspace, r, "resource")?;
    }
    let parent = root.join("web-creates");
    if !parent.exists() {
        make_private_dir(&parent)?;
    }
    private_dir(&parent)?;
    let mut token = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut f| f.read_exact(&mut token))
        .map_err(|e| e.to_string())?;
    let id = hex(&token);
    let d = dir(root, &id)?;
    make_private_dir(&d)?;
    save(
        &d.join("session.json"),
        &json!({"type":"mini-web-create-v1","id":id,"subject":member(workspace,"subject")?,"room":room,"roomReference":room_reference,"element":random_nonce()?}),
    )?;
    load(root, workspace, &id)
}
fn attempts(root: &Path, s: &Value, start: &Value) -> (PathBuf, PathBuf) {
    (
        root.join("attempts").join(format!(
            "create-{}",
            ref_file(start["name"].as_str().unwrap_or("invalid"))
        )),
        root.join("attempts").join(format!(
            "web-create-{}",
            s["id"].as_str().unwrap_or("invalid")
        )),
    )
}
fn outcome(attempt: &Path) -> Result<Option<Value>> {
    if !attempt.exists() {
        return Ok(None);
    }
    accepted_outcome(attempt)
}
fn born_reference(root: &Path, start: &Value) -> Result<Value> {
    let name = member(start, "name")?;
    let r = reference(root, name)?;
    let source = bounded_json(&root.join("sources").join(format!("create-{name}.json")))?;
    if r["target"] != source["birth"]["resources"][0]["target"] {
        return Err(
            "created document reference changed; retain this operation rather than redirecting it"
                .into(),
        );
    }
    Ok(r)
}
/// Member-local discovery only: no receipt is inferred from a saved start.
pub(crate) fn recent(root: &Path, workspace: &Value) -> Result<Vec<Value>> {
    let parent = root.join("web-creates");
    if !parent.exists() {
        return Ok(vec![]);
    }
    private_dir(&parent)?;
    let mut rows = Vec::new();
    for entry in fs::read_dir(&parent).map_err(|e| e.to_string())?.take(128) {
        let entry = entry.map_err(|e| e.to_string())?;
        if !entry.file_type().map_err(|e| e.to_string())?.is_dir() {
            continue;
        }
        let Some(id) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if dir(root, &id).is_err() {
            continue;
        }
        let Ok(saved) = bounded_json(&entry.path().join("session.json")) else {
            continue;
        };
        if saved["subject"] != member(workspace, "subject")?
            || saved["type"] != "mini-web-create-v1"
            || saved["id"] != id
        {
            continue;
        }
        let Ok(start) = bounded_json(&entry.path().join("started.json")) else {
            continue;
        };
        rows.push(json!({"id":id,"name":start["name"],"room":saved["room"]}));
    }
    rows.sort_by(|a, b| a["name"].as_str().cmp(&b["name"].as_str()));
    Ok(rows)
}
pub(crate) fn load(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let (d, s) = session(root, workspace, id)?;
    let mut out = json!({"id":id,"room":s["room"],"status":"editing","message":"Choose a name and document law."});
    if !d.join("started.json").exists() {
        return Ok(out);
    }
    let start = bounded_json(&d.join("started.json"))?;
    if d.join("document-started.json").exists() {
        let retained = bounded_json(&d.join("document-started.json"))?;
        if reference(root, member(&start, "name")?)? != retained["reference"] {
            return Err(
                "document reference changed; this retained creation cannot be redirected".into(),
            );
        }
    }
    out["name"] = start["name"].clone();
    out["law"] = start["law"].clone();
    out["status"] = json!("uncertain");
    out["message"] = json!("Creation started. Check the exact outcome before continuing.");
    let (birth, document) = attempts(root, &s, &start);
    if birth.exists() && matches!(retained_attempt_outcome(&birth)?, AttemptOutcome::Refused) {
        out["status"] = json!("refused");
        out["message"] = json!(
            "The exact resource birth was refused. Its retained request has not been replaced."
        );
    }
    if let Some(receipt) = outcome(&birth)? {
        out["birthReceipt"] = receipt;
        out["status"] = json!("birth-complete");
        out["message"] = json!(
            "The resource birth is confirmed. Finish its empty document, then open the editor."
        );
    }
    if let Some(receipt) = outcome(&document)? {
        out["receipt"] = receipt;
        out["status"] = json!("created");
        out["message"] = json!("Document created. Open it to write.");
    } else if d.join("document-started.json").exists() {
        if document.exists()
            && matches!(
                retained_attempt_outcome(&document)?,
                AttemptOutcome::Refused
            )
        {
            out["status"] = json!("refused");
            out["message"]=json!("The exact document operation was refused. The confirmed resource birth and both operation identities are retained.");
        } else {
            out["status"] = json!("uncertain");
            out["message"] = json!("The document operation started. Check its exact outcome.");
        }
    }
    if d.join("result.json").exists()
        && out["status"] != "created"
        && out["status"] != "refused"
        && out["status"] != "birth-complete"
    {
        let r = bounded_json(&d.join("result.json"))?;
        out["status"] = r["status"].clone();
        out["message"] = r["message"].clone();
    }
    Ok(out)
}
fn record_error(d: &Path, attempt: &Path, error: String) -> Result<()> {
    let status = if crate::take_host_decision().is_some() {
        "refused"
    } else if attempt.join("call.bin").exists() {
        "uncertain"
    } else {
        "failed"
    };
    save(
        &d.join("result.json"),
        &json!({"status":status,"message":error}),
    )
}
pub(crate) fn submit(
    root: &Path,
    workspace: &Value,
    id: &str,
    name: &str,
    law: &str,
) -> Result<Value> {
    validate_name(name)?;
    if !matches!(law, "draft" | "note") {
        return Err("choose draft or note".into());
    }
    let (d, s) = session(root, workspace, id)?;
    let _lock = crate::transport::service_lock(&d.join("create.lock"))?;
    let start = json!({"name":name,"law":law});
    if d.join("started.json").exists() {
        if bounded_json(&d.join("started.json"))? != start {
            return Err(
                "this creation already started different work; check its retained outcome".into(),
            );
        }
        return load(root, workspace, id);
    }
    // Serialize claiming a name with other browser creations. A reservation is
    // member-local custody only; the ordinary birth still decides authority.
    let parent = root.join("web-creates");
    let _names = crate::transport::service_lock(&parent.join("names.lock"))?;
    let claim = parent.join(format!("name-{name}.json"));
    if claim.exists()
        || root.join("refs").join(format!("{name}.json")).exists()
        || root
            .join("sources")
            .join(format!("create-{name}.request.json"))
            .exists()
    {
        return Err(
            "this name already has a resource or retained creation; choose a new name".into(),
        );
    }
    save(
        &claim,
        &json!({"id":id,"subject":member(workspace,"subject")?}),
    )?;
    save(&d.join("started.json"), &start)?;
    let predicate = crate::shell::document_law(law).ok_or("unknown document law")?;
    save(&d.join("law.json"), &predicate)?;
    crate::take_host_decision();
    let (birth, _) = attempts(root, &s, &start);
    if let Err(e) = create(
        root,
        workspace,
        name,
        "content",
        &d.join("law.json"),
        s["room"].as_str(),
        "object",
        None,
        None,
        None,
    ) {
        record_error(&d, &birth, e)?;
        return load(root, workspace, id);
    }
    initialize(root, workspace, id, &d, &s, &start)?;
    load(root, workspace, id)
}
fn initialize(
    root: &Path,
    workspace: &Value,
    id: &str,
    d: &Path,
    s: &Value,
    start: &Value,
) -> Result<()> {
    let (_, attempt) = attempts(root, s, start);
    let proposal = format!("web-create-{id}");
    if d.join("document-started.json").exists() {
        return Ok(());
    }
    let name = member(start, "name")?;
    let r = born_reference(root, start)?;
    save(
        &d.join("document-started.json"),
        &json!({"reference":r,"attempt":attempt,"proposal":proposal,"element":s["element"]}),
    )?;
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":name,"payload":{"type":"content","actions":[{"type":"createDocument","rootElement":s["element"],"schema":"0"}]}}]});
    crate::take_host_decision();
    let result = (|| {
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
    if let Err(e) = result {
        record_error(d, &attempt, e)?;
    }
    Ok(())
}
pub(crate) fn finish(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let (d, s) = session(root, workspace, id)?;
    let _lock = crate::transport::service_lock(&d.join("create.lock"))?;
    let start = bounded_json(&d.join("started.json"))?;
    let (birth, _) = attempts(root, &s, &start);
    if outcome(&birth)?.is_none() {
        return Err("birth must be confirmed before finishing the document".into());
    }
    if !root
        .join("refs")
        .join(format!("{}.json", member(&start, "name")?))
        .exists()
    {
        return Err("check the retained birth to recover its workspace reference first".into());
    }
    if d.join("result.json").exists() {
        return load(root, workspace, id);
    }
    initialize(root, workspace, id, &d, &s, &start)?;
    load(root, workspace, id)
}
pub(crate) fn lookup(root: &Path, workspace: &Value, id: &str) -> Result<Value> {
    let (d, s) = session(root, workspace, id)?;
    let _lock = crate::transport::service_lock(&d.join("create.lock"))?;
    if !d.join("started.json").exists() {
        return load(root, workspace, id);
    }
    let start = bounded_json(&d.join("started.json"))?;
    let (birth, document) = attempts(root, &s, &start);
    for attempt in [&birth, &document] {
        if attempt.join("call.bin").is_file() && outcome(attempt)?.is_none() {
            let _ = recover(root, attempt);
        }
    }
    // Only a confirmed exact birth may reconstruct the workspace reference.
    // create then returns the retained receipt and cannot submit another birth.
    if outcome(&birth)?.is_some() {
        let name = member(&start, "name")?;
        if !root.join("refs").join(format!("{name}.json")).exists() {
            create(
                root,
                workspace,
                name,
                "content",
                &d.join("law.json"),
                s["room"].as_str(),
                "object",
                None,
                None,
                None,
            )?;
        }
    }
    let unfinished = if d.join("document-started.json").exists() {
        &document
    } else {
        &birth
    };
    if !d.join("result.json").exists()
        && !unfinished.join("call.bin").exists()
        && (unfinished == &document || outcome(&birth)?.is_none())
    {
        save(
            &d.join("result.json"),
            &json!({"status":"failed","message":"This operation stopped before its exact call. No replacement was submitted. The retained creation remains available for inspection."}),
        )?;
    }
    load(root, workspace, id)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn creation_identity_rejects_paths() {
        let r = Path::new("/unused");
        for id in ["../test", "", "gggggggggggggggggggggggggggggggg"] {
            assert!(dir(r, id).is_err())
        }
    }
    #[test]
    fn creation_attempts_are_fixed_and_distinct() {
        let (b, d) = attempts(
            Path::new("/workspace"),
            &json!({"id":"0123456789abcdef0123456789abcdef"}),
            &json!({"name":"notes"}),
        );
        assert_eq!(b, Path::new("/workspace/attempts/create-notes"));
        assert_eq!(
            d,
            Path::new("/workspace/attempts/web-create-0123456789abcdef0123456789abcdef")
        );
        assert_ne!(b, d)
    }
    #[test]
    fn stopped_creation_retains_exact_request_without_replacement() {
        let root = std::env::temp_dir().join(format!(
            "mini-web-create-{}-{}",
            std::process::id(),
            random_nonce().unwrap()
        ));
        make_private_dir(&root).unwrap();
        let workspace = json!({"subject":"7"});
        let opened = open(&root, &workspace, None).unwrap();
        let id = opened["id"].as_str().unwrap();
        let result = submit(&root, &workspace, id, "paper", "draft").unwrap();
        assert_eq!(result["status"], "failed");
        assert_eq!(recent(&root, &workspace).unwrap()[0]["id"], id);
        assert!(recent(&root, &json!({"subject":"8"})).unwrap().is_empty());
        assert_eq!(
            submit(&root, &workspace, id, "paper", "draft").unwrap(),
            result
        );
        assert!(submit(&root, &workspace, id, "other", "draft").is_err());
        assert!(submit(&root, &workspace, id, "paper", "note").is_err());
        assert_eq!(lookup(&root, &workspace, id).unwrap()["name"], "paper");
        assert!(!root.join("attempts/create-paper/call.bin").exists());
        let second = open(&root, &workspace, None).unwrap();
        assert!(submit(
            &root,
            &workspace,
            second["id"].as_str().unwrap(),
            "paper",
            "draft"
        )
        .is_err());
        assert!(load(&root, &json!({"subject":"8"}), id).is_err());
    }
}
