//! Member workspace projection. Local references are discovery hints; selected
//! resources are read through the member's existing signed Mini authority.
//! No controller state, custody secret or second resource registry is consulted.
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
        let mut terminal = false;
        for outcome in std::fs::read_dir(entry.path()).map_err(|e| e.to_string())? {
            let outcome = outcome.map_err(|e| e.to_string())?;
            let filename = outcome.file_name();
            let Some(filename) = filename.to_str() else {
                continue;
            };
            if filename != "outcome.json"
                && !(filename.starts_with("retry-") && filename.ends_with(".json"))
            {
                continue;
            }
            if let Ok(value) = workspace::bounded_json(&outcome.path()) {
                terminal |= value["type"] == "refused"
                    || (value["type"] == "confirmed"
                        && matches!(
                            value["confirmation"].as_str(),
                            Some("installed" | "replayed")
                        ));
            }
        }
        if !terminal {
            pending.push(json!({"attempt":name,"status":"needs-exact-lookup",
            "origin":"member-retained-call","currentness":"retained-evidence",
            "actions":[{"label":"recover","command":format!("lookup {name}")}]}));
        }
    }
    pending.sort_by(|a, b| a["attempt"].as_str().cmp(&b["attempt"].as_str()));
    Ok(pending)
}

fn projection(root: &Path, selected: Option<&str>) -> Result<Value> {
    let pin = workspace::load(root)?;
    let config = workspace::bounded_json(&workspace::member_path(&pin, "config")?)?;
    let mut resources = vec![];
    let mut unavailable = vec![];
    if let Some(name) = selected {
        resources.push(Resource::from_reference(&workspace::reference(root, name)?)?.json());
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
        "actions":[{"label":"providers","command":"key providers"},
            {"label":"provider grants","command":"key ls"},
            {"label":"credits","command":"pay status"},
            {"label":"incoming references","command":"inbox"},
            {"label":"recent work","command":"history"}]});
    if let Some(name) = selected {
        let reference = workspace::reference(root, name)?;
        let (view, challenge, _) = workspace::signed_view(root, &pin, &reference, "resource")?;
        value["currentness"] = json!("source-checked");
        value["observation"] = json!({"origin":"native-signed-resource","currentness":"at-observed-head",
            "domain":challenge["domain"],"semantics":challenge["semantics"],
            "height":challenge["height"],"worldRoot":challenge["worldRoot"],"clock":challenge["clock"],
            "target":reference["target"],"resourceRoot":view.pointer("/cell/root"),
            "balances":view.get("balances")});
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
    args.finish()?;
    let value = projection(&root, name.as_deref())?;
    if json_output {
        println!(
            "{}",
            serde_json::to_string_pretty(&value).map_err(|e| e.to_string())?
        );
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
