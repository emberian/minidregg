//! Member workspace projection. Local references are discovery hints; selected
//! resources are read through the member's existing signed Mini authority.
//! No controller state, custody secret or second resource registry is consulted.
#[path = "member_app.rs"]
mod application;

use crate::{workspace, Args, Result};
use serde_json::{json, Value};
use std::path::{Path, PathBuf};

#[derive(Debug)]
struct Action {
    label: &'static str,
    command: String,
}
impl Action {
    fn json(&self) -> Value {
        json!({"label":self.label,"command":self.command})
    }
}
#[derive(Debug)]
struct Resource {
    name: String,
    kind: String,
    target: String,
    room: bool,
    actions: Vec<Action>,
}
impl Resource {
    fn from_reference(reference: &Value) -> Result<Self> {
        let name = workspace::member(reference, "name")?.to_owned();
        workspace::validate_ref_name(&name)?;
        let room = reference.get("room").and_then(Value::as_str).is_some();
        let mut actions = vec![
            Action {
                label: "inspect",
                command: format!("home {name}"),
            },
            Action {
                label: "read",
                command: format!("read {name}"),
            },
            Action {
                label: "rights",
                command: format!("can {name}"),
            },
        ];
        if room {
            actions.extend([
                Action {
                    label: "enter",
                    command: format!("chat enter {name}"),
                },
                Action {
                    label: "contents",
                    command: format!("room ls {name} --import"),
                },
                Action {
                    label: "allowance",
                    command: format!("room status {name}"),
                },
            ]);
        }
        Ok(Self {
            name,
            kind: workspace::member(reference, "kind")?.to_owned(),
            target: workspace::member(reference, "target")?.to_owned(),
            room,
            actions,
        })
    }
    fn json(&self) -> Value {
        json!({"name":self.name,"kind":self.kind,"target":self.target,
        "room":self.room,"origin":"member-workspace-reference","currentness":"discovery-only",
        "actions":self.actions.iter().map(Action::json).collect::<Vec<_>>()})
    }
}

fn regular(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok_and(|m| m.file_type().is_file())
}

/// Only the current member's retained signed calls are inspected. No retry is
/// suggested: lookup recovers the exact operation, including uncertain effects.
fn pending_attempts(root: &Path) -> Result<Vec<Value>> {
    let attempts = root.join("attempts");
    if !attempts.exists() {
        return Ok(vec![]);
    }
    let mut pending = vec![];
    for entry in std::fs::read_dir(attempts).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        if !entry.file_type().map_err(|e| e.to_string())?.is_dir() {
            continue;
        }
        let Some(name) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if workspace::validate_name(&name).is_err() || !regular(&entry.path().join("call.bin")) {
            continue;
        }
        let terminal = matches!(workspace::retained_attempt_outcome(&entry.path()),
            Ok(workspace::AttemptOutcome::Confirmed(_) | workspace::AttemptOutcome::Refused));
        if !terminal {
            pending.push(json!({"attempt":name,"status":"needs-exact-lookup",
            "origin":"member-retained-call","currentness":"retained-evidence",
            "actions":[{"label":"recover","command":format!("lookup {name}")}]}));
        }
    }
    pending.sort_by(|a, b| a["attempt"].as_str().cmp(&b["attempt"].as_str()));
    Ok(pending)
}

/// Connector state belongs to this member and uses the connector's own exact
/// phase classifier. Its export custody is never surfaced as discovery data.
fn connector_operation(root: &Path, pin: &Value, id: &str) -> Value {
    let mut row = json!({"id":id,"origin":"member-retained-connector",
        "currentness":"retained-evidence","actions":[{"label":"status",
        "command":format!("doc app-export status {id}")}]});
    match workspace::app_document::status(root, pin, id) {
        Ok(state) => {
            for field in [
                "status", "subject", "document", "target", "receipt", "message",
            ] {
                if let Some(value) = state.get(field) {
                    row[field] = value.clone();
                }
            }
            let next = match state["status"].as_str() {
                Some("captured") => Some(("publish", format!("doc app-export publish {id}"))),
                Some("uncertain") => Some(("recover", format!("doc app-export recover {id}"))),
                Some("failed" | "refused") => {
                    Some(("repair", format!("doc app-export rebase {id} NEXT")))
                }
                _ => None,
            };
            if let Some((label, command)) = next {
                row["actions"]
                    .as_array_mut()
                    .unwrap()
                    .push(json!({"label":label,"command":command}));
            }
        }
        Err(_) => row["status"] = json!("unavailable"),
    }
    row
}

fn connector_operations(root: &Path, pin: &Value) -> Result<Vec<Value>> {
    let parent = root.join("app-documents");
    let metadata = match std::fs::symlink_metadata(&parent) {
        Ok(m) => m,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(vec![]),
        Err(e) => return Err(e.to_string()),
    };
    if !metadata.file_type().is_dir() {
        return Ok(vec![]);
    }
    let mut rows = vec![];
    for entry in std::fs::read_dir(&parent).map_err(|e| e.to_string())? {
        let entry = entry.map_err(|e| e.to_string())?;
        if !entry.file_type().map_err(|e| e.to_string())?.is_dir() {
            continue;
        }
        let Some(id) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if workspace::validate_name(&id).is_err() {
            continue;
        }
        rows.push(connector_operation(root, pin, &id));
    }
    rows.sort_by(|a, b| a["id"].as_str().cmp(&b["id"].as_str()));
    Ok(rows)
}

/// Discovery stays within the member's workspace. The lifecycle owner decides
/// phase and next action; home never interprets controller or grant custody.
fn lifecycle_operations(root: &Path, pin: &Value) -> Result<Vec<Value>> {
    let parent = root.join("app-lifecycle");
    if !parent.exists() { return Ok(vec![]); }
    workspace::private_dir(&parent)?;
    let mut rows = vec![];
    for entry in std::fs::read_dir(&parent).map_err(|e|e.to_string())? {
        let entry = entry.map_err(|e|e.to_string())?;
        if !entry.file_type().map_err(|e|e.to_string())?.is_dir() { continue; }
        let Some(id) = entry.file_name().to_str().map(str::to_owned) else { continue; };
        if workspace::validate_name(&id).is_err() || id.len() > 40 { continue; }
        let mut row = json!({"id":id,"origin":"member-retained-workflow",
            "currentness":"retained-evidence","authority":"requires-current-source-admission",
            "actions":[{"label":"status","command":format!("app delegate-lifecycle status {id}")}]});
        match workspace::app_lifecycle::retained_status(root,pin,&id) {
            Ok(status) => {
                for field in ["complete","phase","prepared","owner","manager","selectorPublicationPending"] {
                    if let Some(value) = status.get(field) { row[field] = value.clone(); }
                }
                row["status"] = json!(if status["selectorPublicationPending"] == true {"needs-recovery"} else if status["complete"] == true {"complete"} else {"in-progress"});
                if let Some(action) = status["nextAction"].as_str() {
                    row["actions"].as_array_mut().unwrap().push(json!({"label":action,
                        "command":format!("app delegate-lifecycle {action} {id}")}));
                }
            }
            Err(_) => row["status"] = json!("unavailable"),
        }
        rows.push(row);
    }
    rows.sort_by(|a,b|a["id"].as_str().cmp(&b["id"].as_str()));
    Ok(rows)
}

/// World objects carry their own descriptor and natural-key map. Presentation
/// follows the signed descriptor instead of a host list of board/poll kinds.
fn programmable_object(view: &Value) -> Option<Value> {
    for (role, command) in [("worldKind", "kind"), ("worldInstance", "instance")] {
        if let Some(data) = view.pointer(&format!("/cell/{role}")) {
            return Some(json!({"type":role,"origin":"native-signed-resource",
                "currentness":"at-observed-head","descriptor":data["descriptor"],
                "entries":data[if role == "worldKind" {"defaults"} else {"entries"}],
                "entryRole":if role == "worldKind" {"defaults"} else {"current-values"},
                "kindRoot":data["kindRoot"],"methods":data["methods"],"command":command}));
        }
    }
    None
}

fn object_value(field: &Value, value: &Value) -> String {
    if field["codec"] == "bytes" {
        if let Some(text) = value
            .as_str()
            .and_then(|hex| crate::decode_hex(hex).ok())
            .and_then(|bytes| String::from_utf8(bytes).ok())
        {
            // JSON quoting keeps untrusted text and terminal controls visible.
            return serde_json::to_string(&text).unwrap_or_default();
        }
    }
    value.to_string()
}

fn projection(root: &Path, selected: Option<&str>) -> Result<Value> {
    let pin = workspace::load(root)?;
    let config = workspace::bounded_json(&workspace::member_path(&pin, "config")?)?;
    projection_with(root,&pin,&config,selected,
        |name|workspace::reference(root,name),
        |reference|workspace::signed_view(root,&pin,reference,"resource").map(|(view,challenge,_)|(view,challenge)))
}

fn projection_with(root: &Path, pin: &Value, config: &Value, selected: Option<&str>,
    mut resolve: impl FnMut(&str)->Result<Value>,
    mut read: impl FnMut(&Value)->Result<(Value,Value)>) -> Result<Value> {
    let mut resources = vec![];
    let mut unavailable = vec![];
    let selected_reference = selected.map(&mut resolve).transpose()?;
    if let Some(reference) = &selected_reference {
        resources.push(Resource::from_reference(reference)?.json());
    } else {
        for entry in std::fs::read_dir(root.join("refs")).map_err(|e| e.to_string())? {
            let entry = entry.map_err(|e| e.to_string())?;
            let filename = entry.file_name();
            let Some(stem) = filename.to_str().and_then(|f| f.strip_suffix(".json")) else {
                continue;
            };
            let name = workspace::ref_name_of_file(stem);
            match workspace::local_reference(root,&name).and_then(|r|Resource::from_reference(&r)) {
                Ok(resource)=>resources.push(resource.json()),
                Err(_)=>unavailable.push(json!({"name":name,"status":"unavailable","origin":"member-workspace-reference"})),
            }
        }
    }
    resources.sort_by(|a, b| a["name"].as_str().cmp(&b["name"].as_str()));
    let mut value = json!({"type":"mini-member-workspace-v1","subject":pin["subject"],
        "origin":"member-workspace","currentness":"discovery-only",
        "world":{"domain":config["domain"],"expectedSeed":config["expectedSeed"],"origin":"pinned-member-config"},"resources":resources,
        "unavailable":unavailable,"recovery":pending_attempts(root)?,
        "documentExports":connector_operations(root,&pin)?,
        "appLifecycles":lifecycle_operations(root,&pin)?,
        "actions":[{"label":"providers","command":"key providers"},
            {"label":"provider grants","command":"key ls"},
            {"label":"credits","command":"pay status"},
            {"label":"incoming references","command":"inbox"},
            {"label":"recent work","command":"history"}]});
    if let (Some(name), Some(reference)) = (selected, selected_reference.as_ref()) {
        let (view, challenge) = read(reference)?;
        value["currentness"] = json!("source-checked");
        value["observation"] = json!({"origin":"native-signed-resource","currentness":"at-observed-head",
            "domain":challenge["domain"],"semantics":challenge["semantics"],
            "height":challenge["height"],"worldRoot":challenge["worldRoot"],"clock":challenge["clock"],
            "target":reference["target"],"resourceRoot":view.pointer("/cell/root"),
            "balances":view.get("balances")});
        if reference.pointer("/provenance/memberApp").is_some() {
            value["resources"][0]["actions"]
                .as_array_mut()
                .unwrap()
                .push(json!({"label":"app authorization","command":format!("app status {name}")}));
        }
        if let Some(object) = programmable_object(&view) {
            let command = object["command"].as_str().unwrap();
            value["resources"][0]["actions"]
                .as_array_mut()
                .unwrap()
                .push(json!({"label":"object details","command":format!("{command} show {name}")}));
            value["object"] = object;
        }
        if reference.get("room").and_then(Value::as_str).is_some() {
            value["resident"] = resident(&view);
            if value["resident"]["subject"]
                .as_str()
                .is_some_and(|s| s != "0")
            {
                value["resources"][0]["actions"]
                    .as_array_mut()
                    .unwrap()
                    .push(json!({"label":"ask resident","command":format!("ask {name} TEXT")}));
            }
        }
    }
    Ok(value)
}

/// Assignment is a signed room fact; it does not establish a running process.
fn resident(view: &Value) -> Value {
    let fields = |name: &str| -> Value {
        let Some((_, key)) = crate::room_schema::TARIFF_FIELDS
            .iter()
            .find(|(n, _)| *n == name)
        else {
            return Value::Null;
        };
        view.pointer("/cell/entries")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .find(|e| e.pointer("/key/field").and_then(Value::as_str) == Some(*key))
            .and_then(|e| e.get("value"))
            .cloned()
            .unwrap_or(Value::Null)
    };
    json!({"subject":fields("hermes"),"account":fields("hermes/account"),
        "assignment":fields("hermes/assignment"),"origin":"native-signed-room-fields",
        "currentness":"at-observed-head","activation":{"status":"unavailable"},
        "requestStatus":{"status":"unavailable"}})
}

fn render(value: &Value) -> String {
    let mut text = format!(
        "Mini workspace · subject {}\n",
        value["subject"].as_str().unwrap_or("?")
    );
    if let Some(observation) = value.get("observation") {
        text.push_str(&format!(
            "Observed at height {}\n",
            observation["height"].as_str().unwrap_or("?")
        ));
    }
    for resource in value["resources"].as_array().into_iter().flatten() {
        text.push_str(&format!(
            "\n{} · {} {}\n",
            resource["name"].as_str().unwrap_or("?"),
            if resource["room"] == true {
                "room"
            } else {
                resource["kind"].as_str().unwrap_or("resource")
            },
            resource["target"].as_str().unwrap_or("?")
        ));
        for action in resource["actions"].as_array().into_iter().flatten() {
            text.push_str(&format!("  {}\n", action["command"].as_str().unwrap_or("")));
        }
    }
    if let Some(balances) = value
        .pointer("/observation/balances")
        .and_then(Value::as_array)
    {
        for balance in balances {
            text.push_str(&format!("Balance: {}\n", balance));
        }
    }
    if let Some(object) = value.get("object") {
        text.push_str(&format!(
            "\nObject kind {} · revision {}\n",
            object["descriptor"]["kind"].as_str().unwrap_or("?"),
            object["descriptor"]["revision"].as_str().unwrap_or("?")
        ));
        if object["type"] == "worldKind" {
            text.push_str("Default values:\n");
        }
        for field in object["descriptor"]["fields"]
            .as_array()
            .into_iter()
            .flatten()
        {
            text.push_str(&format!(
                "  {} · {} · {} {}\n",
                field["name"],
                field["meaning"],
                field["codec"].as_str().unwrap_or("?"),
                field["discipline"].as_str().unwrap_or("?")
            ));
            for entry in object["entries"]
                .as_array()
                .into_iter()
                .flatten()
                .filter(|e| e["field"] == field["id"])
            {
                text.push_str(&format!(
                    "    [{}] {}\n",
                    entry["key"],
                    object_value(field, &entry["value"])
                ));
            }
        }
        for method in object["methods"].as_array().into_iter().flatten() {
            text.push_str(&format!(
                "  Method {} · program {}\n",
                method["name"], method["program"]
            ));
            for output in method["outputs"].as_array().into_iter().flatten() {
                text.push_str(&format!(
                    "    output {} → field {} key {}\n",
                    output["output"], output["field"], output["key"]
                ));
            }
        }
    }
    if let Some(resident) = value.get("resident") {
        if resident["subject"].as_str().is_some_and(|s| s != "0") {
            text.push_str(&format!("Resident {} · allowance account {} · assignment {}\nRuntime status is unavailable.\n",
                resident["subject"].as_str().unwrap_or("?"),resident["account"].as_str().unwrap_or("?"),resident["assignment"].as_str().unwrap_or("?")));
        } else {
            text.push_str("No resident is assigned.\n");
        }
    }
    for unavailable in value["unavailable"].as_array().into_iter().flatten() {
        text.push_str(&format!(
            "\n{} · reference unavailable\n",
            unavailable["name"].as_str().unwrap_or("?")
        ));
    }
    for recovery in value["recovery"].as_array().into_iter().flatten() {
        text.push_str(&format!(
            "\nRecover pending work: {}\n",
            recovery["actions"][0]["command"].as_str().unwrap_or("")
        ));
    }
    for operation in value["documentExports"].as_array().into_iter().flatten() {
        text.push_str(&format!(
            "\nDocument export {} · {}\n",
            operation["id"].as_str().unwrap_or("?"),
            operation["status"].as_str().unwrap_or("unavailable")
        ));
        for action in operation["actions"].as_array().into_iter().flatten() {
            text.push_str(&format!("  {}\n", action["command"].as_str().unwrap_or("")));
        }
        if let Some(message) = operation["message"].as_str() {
            text.push_str(&format!("  {message}\n"));
        }
    }
    for operation in value["appLifecycles"].as_array().into_iter().flatten() {
        text.push_str(&format!("\nApp delegation {} · {}\n", operation["id"].as_str().unwrap_or("?"),
            operation["phase"].as_str().unwrap_or_else(|| operation["status"].as_str().unwrap_or("unavailable"))));
        for action in operation["actions"].as_array().into_iter().flatten() {
            text.push_str(&format!("  {}\n",action["command"].as_str().unwrap_or("")));
        }
    }
    text.push_str("\nProviders: key providers · Credits: pay status · Recent work: history\n");
    if value.get("observation").is_none() {
        text.push_str("Choose a resource with home NAME to inspect its current state.\n");
    }
    text
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let root = PathBuf::from(args.required("dir")?);
    let name = args
        .optional("name")
        .map(|v| v.into_string().map_err(|_| "member name must be UTF-8"))
        .transpose()?;
    let json_output = match args.optional("json").as_deref() {
        None => false,
        Some(v) if v == std::ffi::OsStr::new("false") => false,
        Some(v) if v == std::ffi::OsStr::new("true") => true,
        _ => return Err("--json must be true or false".into()),
    };
    let action = args
        .optional("action")
        .map(|v| v.into_string().map_err(|_| "member action must be UTF-8"))
        .transpose()?;
    args.finish()?;
    let value = match action.as_deref() {
        None | Some("workspace") => projection(&root, name.as_deref())?,
        Some("app-status") => application::status(
            &root,
            &workspace::load(&root)?,
            name.as_deref().ok_or("App status requires a reference")?,
        )?,
        _ => return Err("Unknown member action".into()),
    };
    if json_output {
        println!(
            "{}",
            serde_json::to_string_pretty(&value).map_err(|e| e.to_string())?
        );
    } else if action.as_deref() == Some("app-status") {
        println!(
            "{} · authorization is current at height {}",
            value["name"].as_str().unwrap_or("app"),
            value["height"].as_str().unwrap_or("?")
        );
        println!("Browser entry is not configured.");
    } else {
        print!("{}", render(&value));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};
    static NEXT: AtomicU64 = AtomicU64::new(0);
    fn fixture() -> PathBuf {
        let p = std::env::temp_dir().join(format!(
            "mini-member-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir_all(p.join("attempts")).unwrap();
        p
    }
    fn attempt(root: &Path, name: &str, outcome: Option<Value>) {
        let p = root.join("attempts").join(name);
        std::fs::create_dir(&p).unwrap();
        std::fs::write(p.join("call.bin"), [1, 2, 3]).unwrap();
        if let Some(outcome) = outcome {
            std::fs::write(
                p.join("outcome.json"),
                serde_json::to_vec(&outcome).unwrap(),
            )
            .unwrap();
        }
    }
    #[test]
    fn uncertainty_exposes_exact_lookup_without_new_submit_action() {
        let root = fixture();
        attempt(&root, "a-uncertain", Some(json!({"type":"uncertain"})));
        attempt(
            &root,
            "a-known",
            Some(json!({"type":"confirmed","confirmation":"installed"})),
        );
        attempt(
            &root,
            "a-refused",
            Some(json!({"type":"refused","reason":"undisclosed"})),
        );
        let rows = pending_attempts(&root).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["actions"][0]["command"], "lookup a-uncertain");
        assert!(!serde_json::to_string(&rows).unwrap().contains("retry"));
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn selected_alias_is_resolved_once_for_label_and_observation() {
        let root=fixture();
        let mut calls=0;
        let value=projection_with(&root,&json!({"subject":"8"}),&json!({"domain":"8501","expectedSeed":"1"}),Some("alias"),
            |_| {calls+=1;Ok(json!({"name":"alias","kind":"object","target":if calls==1 {"7"} else {"9"}}))},
            |reference| {assert_eq!(reference["target"],"7");Ok((json!({"cell":{"root":"2"},"balances":[]}),
                json!({"domain":"8501","semantics":"3","height":"4","worldRoot":"5","clock":"6"}))) }).unwrap();
        assert_eq!(calls,1);
        assert_eq!(value["resources"][0]["target"],value["observation"]["target"]);
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn newer_uncertainty_keeps_recovery_after_an_old_refusal() {
        let root = fixture();
        attempt(&root,"a-old-refusal",Some(json!({"type":"refused"})));
        std::fs::write(root.join("attempts/a-old-refusal/retry-001.json"),br#"{"type":"uncertain"}"#).unwrap();
        attempt(&root,"a-confirmed",Some(json!({"type":"confirmed","confirmation":"installed"})));
        std::fs::write(root.join("attempts/a-confirmed/retry-001.json"),br#"{"type":"unavailable"}"#).unwrap();
        let rows=pending_attempts(&root).unwrap();
        assert_eq!(rows.len(),1);
        assert_eq!(rows[0]["attempt"],"a-old-refusal");
        assert_eq!(rows[0]["actions"][0]["command"],"lookup a-old-refusal");
        std::fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn foreign_symlink_attempt_and_fake_outcome_do_not_hide_uncertainty() {
        let root = fixture();
        attempt(&root, "a-owner", None);
        std::fs::write(
            root.join("fake.json"),
            br#"{"type":"confirmed","confirmation":"installed"}"#,
        )
        .unwrap();
        std::os::unix::fs::symlink(
            root.join("fake.json"),
            root.join("attempts/a-owner/outcome.json"),
        )
        .unwrap();
        std::os::unix::fs::symlink(
            root.join("attempts/a-owner"),
            root.join("attempts/a-foreign"),
        )
        .unwrap();
        let rows = pending_attempts(&root).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["attempt"], "a-owner");
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn room_actions_use_member_commands_and_never_controller_paths() {
        let r = Resource::from_reference(
            &json!({"name":"lab","kind":"object","target":"7","room":"member"}),
        )
        .unwrap()
        .json();
        assert!(r["actions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|a| a["command"] == "room status lab"));
        assert_eq!(r["currentness"], "discovery-only");
        assert!(!serde_json::to_string(&r).unwrap().contains("controller"));
        assert!(
            Resource::from_reference(&json!({"name":"lab;cat","kind":"object","target":"7"}))
                .is_err()
        );
    }
    #[test]
    fn connector_source_uncertainty_uses_owner_status_and_never_recaptures() {
        let root = fixture();
        let op = root.join("app-documents/export-a");
        std::fs::create_dir_all(&op).unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&op, std::fs::Permissions::from_mode(0o700)).unwrap();
        std::fs::write(op.join("fetch-started.json"),br#"{"type":"mini-app-document-fetch-v1","capture":"a","subject":"8","app":"9","generation":"1","document":"10"}"#).unwrap();
        let rows = connector_operations(&root, &json!({"subject":"8"})).unwrap();
        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0]["status"], "source-uncertain");
        assert_eq!(rows[0]["actions"].as_array().unwrap().len(), 1);
        assert_eq!(
            rows[0]["actions"][0]["command"],
            "doc app-export status export-a"
        );
        assert!(rows[0].get("custody").is_none());
        let foreign = connector_operations(&root, &json!({"subject":"11"})).unwrap();
        assert_eq!(foreign[0]["status"], "unavailable");
        assert!(foreign[0].get("message").is_none());
        std::os::unix::fs::symlink(&op, root.join("app-documents/export-symlink")).unwrap();
        assert_eq!(
            connector_operations(&root, &json!({"subject":"8"}))
                .unwrap()
                .len(),
            1
        );
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn programmable_objects_keep_natural_keys_and_method_bindings() {
        let field = json!({"id":"1","name":"title","meaning":"tasks/title","codec":"bytes","discipline":"ram"});
        let data = json!({"descriptor":{"kind":"77","revision":"2","fields":[field]},
            "entries":[{"field":"1","key":"100000000000","value":"7461736b"}],
            "methods":[{"name":"close","program":"42","outputs":[{"output":"90","field":"3","key":"0"}]}]});
        let object = programmable_object(&json!({"cell":{"worldInstance":data}})).unwrap();
        assert_eq!(object["entries"][0]["key"], "100000000000");
        assert_eq!(object["methods"][0]["outputs"][0]["output"], "90");
        assert_eq!(object_value(&field, &json!("7461736b")), "\"task\"");
        assert_eq!(
            object_value(&field, &json!("1b5b33316d")),
            "\"\\u001b[31m\""
        );
        let kind=programmable_object(&json!({"cell":{"worldKind":{"descriptor":data["descriptor"],"defaults":data["entries"],"methods":data["methods"]}}})).unwrap();
        assert_eq!(kind["entries"], object["entries"]);
        assert_eq!(kind["entryRole"], "defaults");
        assert!(programmable_object(&json!({"cell":{"entries":[]}})).is_none());
    }
    #[test]
    fn assignment_never_claims_runtime_liveness_and_uses_shared_schema() {
        let field = |name: &str, value: &str| {
            let key = crate::room_schema::TARIFF_FIELDS
                .iter()
                .find(|(n, _)| *n == name)
                .unwrap()
                .1;
            json!({"key":{"field":key},"value":value})
        };
        let r = resident(
            &json!({"cell":{"entries":[field("hermes","8"),field("hermes/account","10"),field("hermes/assignment","11")]}}),
        );
        assert_eq!(r["subject"], "8");
        assert_eq!(r["assignment"], "11");
        assert_eq!(r["activation"]["status"], "unavailable");
        assert_eq!(r["requestStatus"]["status"], "unavailable");
    }
}
