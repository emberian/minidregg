//! `can [NAME] [--all]` (P-AFFORDANCES; DEOS §1.3, deos's `project_for(held)`).
//!
//! For each resource this workspace names (or NAME): read, from the Host, the
//! capability record behind each capability the reference names (a signed
//! `capability` view per capability) and take the verbs those records carry.
//! For each shell verb they cover, build the smallest representative command,
//! author it as a proposal (the same `propose` every verb uses) and ask the
//! Host to dry-run it (`main::dry_run`, op 130): planned as op 1 (where a law
//! refusal names its clause), assembled and submitted over a Store writer that
//! never appends. Nothing is submitted; the Host commits nothing. One line per
//! probe; a verb no grant covers is omitted (`--all` prints it as `noGrant`).
//!
//! What each probe prepares, and why it is representative, is the table in
//! `planning/docuverse/p-affordances.md`; the bracket at the end of each line
//! names it.

use super::*;
use crate::{dry_run, host_decided, take_host_decision};
use std::collections::BTreeSet;

/// Shell verb -> the capability verb that authorizes it.
const KERNEL_VERB: &[(&str, &str)] = &[
    ("read", "observe"),
    ("write", "mutate"),
    ("edit", "mutate"),
    ("mark", "mutate"),
    ("link", "mutate"),
    ("transfer", "transfer"),
    ("install", "install"),
    ("delegate", "delegate"),
    ("law", "installPolicy"),
    ("revoke", "revokeCapability"),
];

fn kernel_verb(verb: &str) -> &'static str {
    KERNEL_VERB
        .iter()
        .find(|(shell, _)| *shell == verb)
        .map(|(_, kernel)| *kernel)
        .expect("every shell verb has a capability verb")
}

fn shell_verbs(kind: &str, document: bool) -> &'static [&'static str] {
    match (kind, document) {
        ("object", true) => &["read", "write", "edit", "mark", "link", "delegate", "law", "revoke"],
        ("object", false) => &["read", "write", "delegate", "law", "revoke"],
        ("account", _) => &["read", "transfer", "delegate", "law", "revoke"],
        _ => &["read", "install", "delegate", "law", "revoke"],
    }
}

/// When a capability record cannot be read (the law hides it, or the
/// capability carries no `observe` to read itself with, as an owner's control
/// capability), the record is not gone: probe the verbs its reference slot is
/// for and let the Host judge each one. A `revoked` or `expired` refusal means
/// the grant does not stand, and it covers nothing.
fn slot_verbs(slot: &str) -> &'static [&'static str] {
    match slot {
        "observeCapability" => &["observe"],
        "operationCapability" => &["mutate", "delegate", "transfer", "install"],
        _ => &["installPolicy", "revokeCapability"],
    }
}

fn verdict_of(line: Option<String>) -> String {
    match line {
        None => "admitted".into(),
        Some(line) => line.strip_prefix("refused: ").unwrap_or(&line).to_owned(),
    }
}

fn row(verb: &str, verdict: &str, what: &str) {
    println!("  {verb:<9} {verdict}   [{what}]");
}

fn signed_view_decided(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    view: &str,
) -> Result<std::result::Result<Value, String>> {
    take_host_decision();
    Ok(host_decided(signed_view(root, workspace, reference, view))?.map(|(value, _, _)| value))
}

struct Run<'a> {
    root: &'a Path,
    workspace: &'a Value,
    tag: String,
    count: usize,
}

impl Run<'_> {
    /// Author `request` as a throwaway proposal, dry-run its intent, remove the
    /// proposal (a probe must not read as a delegation this workspace made).
    fn probe(&mut self, verb: &str, request: Value) -> Result<String> {
        self.count += 1;
        let id = format!("can-{}-{}-{}", self.tag, verb, self.count);
        let source = self.root.join("sources").join(format!("{id}.json"));
        private_file(
            &source,
            &serde_json::to_vec(&request).map_err(|error| error.to_string())?,
        )?;
        take_host_decision();
        let authored = host_decided(propose_request(self.root, self.workspace, &request, &id, None, true));
        let verdict = match authored {
            Ok(Err(line)) => Ok(verdict_of(Some(line))),
            Err(error) => Ok(format!("(not probed: {error})")),
            Ok(Ok(_)) => {
                let (attempt, _) = new_attempt(self.root)?;
                dry_run(
                    &member_path(self.workspace, "host")?,
                    &member_path(self.workspace, "config")?,
                    &self.root.join("proposals").join(&id).join("intent.json"),
                    OsStr::new("intent"),
                    &member_path(self.workspace, "key")?,
                    &attempt,
                )
                .map(verdict_of)
            }
        };
        let _ = fs::remove_dir_all(self.root.join("proposals").join(&id));
        let _ = fs::remove_file(&source);
        verdict
    }
}

fn invoke(name: &str, payload: Value) -> Value {
    json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":payload}]})
}

/// Fields probed per resource (each up and down by one).
const MAX_FIELDS: usize = 8;

/// The scalar fields and their values, in field order, from a signed resource
/// view.
fn fields(view: &Value) -> Vec<(String, i128)> {
    let mut found: Vec<(u128, String, i128)> = view["cell"]["entries"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| {
            let field = entry.get("key")?.get("field")?.as_str()?;
            let value = entry.get("value")?.as_str()?.parse::<i128>().ok()?;
            Some((field.parse::<u128>().ok()?, field.to_owned(), value))
        })
        .collect();
    found.sort();
    found
        .into_iter()
        .map(|(_, field, value)| (field, value))
        .collect()
}

/// Recipients this workspace delegated `name` to, from its own proposals.
fn delegated_recipients(root: &Path, name: &str) -> Vec<String> {
    let mut found = BTreeSet::new();
    if let Ok(entries) = fs::read_dir(root.join("proposals")) {
        for entry in entries.flatten() {
            if entry.file_name().to_string_lossy().starts_with("can-") {
                continue;
            }
            if let Ok(summary) = bounded_json(&entry.path().join("proposal.json")) {
                let delegation = &summary["delegation"];
                if delegation.get("name").and_then(Value::as_str) == Some(name) {
                    if let Some(recipient) = delegation.get("recipient").and_then(Value::as_str) {
                        found.insert(recipient.to_owned());
                    }
                }
            }
        }
    }
    found.into_iter().collect()
}

pub(super) fn can(root: &Path, workspace: &Value, name: Option<&str>, all: bool) -> Result<()> {
    let names = match name {
        Some(name) => vec![name.to_owned()],
        None => {
            let mut names = Vec::new();
            for entry in fs::read_dir(root.join("refs")).map_err(|error| error.to_string())? {
                let file = entry.map_err(|error| error.to_string())?.file_name();
                if let Some(stem) = file.to_str().and_then(|f| f.strip_suffix(".json")) {
                    names.push(stem.to_owned());
                }
            }
            names.sort();
            names
        }
    };
    let me = member(workspace, "subject")?.to_owned();
    let mut run = Run {
        root,
        workspace,
        tag: random_nonce()?[..8].to_owned(),
        count: 0,
    };
    for name in names {
        resource(&mut run, &me, &name, all)?;
    }
    Ok(())
}

fn resource(run: &mut Run<'_>, me: &str, name: &str, all: bool) -> Result<()> {
    let (root, workspace) = (run.root, run.workspace);
    let reference = reference(root, name)?;
    let kind = member(&reference, "kind")?.to_owned();
    let target = member(&reference, "target")?.to_owned();

    // The grants: the Host's own capability records, one signed view each.
    // One capability may fill several reference slots (an owner's root
    // capability is both its observe and its operation capability).
    let mut slots_of = Vec::<(String, Vec<&str>)>::new();
    for slot in [
        "observeCapability",
        "operationCapability",
        "controlCapability",
    ] {
        let Some(id) = reference.get(slot).and_then(Value::as_str) else {
            continue;
        };
        match slots_of.iter_mut().find(|(known, _)| known == id) {
            Some((_, slots)) => slots.push(slot),
            None => slots_of.push((id.to_owned(), vec![slot])),
        }
    }
    let mut held = BTreeSet::<String>::new();
    let mut parent = None::<Value>;
    let mut notes = Vec::new();
    for (id, slots) in &slots_of {
        let mut via = reference.clone();
        via["observeCapability"] = json!(id);
        match signed_view_decided(root, workspace, &via, "capability")? {
            Ok(record) => {
                let head = &record["head"];
                let holder = &head["holder"];
                let mine = holder["type"] == "bearer" || holder["subject"].as_str() == Some(me);
                // A scope is `targets` (explicit) or `room` (`under R`, K-ROOM: an
                // owner's capability on a cell it created is `room` = that cell).
                // Whether a room covers a target inside it depends on the parent
                // chain; the Host judges each probe, as it does at submission.
                let covers = head["targets"]
                    .as_array()
                    .is_some_and(|targets| targets.iter().any(|t| t.as_str() == Some(&target)))
                    || head["room"].is_string();
                if !mine || !covers {
                    notes.push(format!("capability {id}: not held by {me} on {target}"));
                    continue;
                }
                for verb in head["verbs"].as_array().into_iter().flatten() {
                    if let Some(verb) = verb.as_str() {
                        held.insert(verb.to_owned());
                    }
                }
                if slots.contains(&"operationCapability") {
                    parent = Some(head.clone());
                }
            }
            Err(line) => {
                let verdict = verdict_of(Some(line));
                if verdict.starts_with("revoked") || verdict.starts_with("expired") {
                    notes.push(format!("capability {id}: {verdict}; it covers nothing"));
                } else {
                    for verb in slots.iter().flat_map(|slot| slot_verbs(slot)) {
                        held.insert((*verb).to_owned());
                    }
                    notes.push(format!(
                        "capability {id} ({}): record unreadable ({verdict}); its verbs are probed and the Host judges each",
                        slots.join(", ")
                    ));
                }
            }
        }
    }

    // read: the signed resource query itself (op 5) is the judgement.
    let view = signed_view_decided(root, workspace, &reference, "resource")?;
    let document = view
        .as_ref()
        .is_ok_and(|view| content_page(view, name).is_ok());
    println!(
        "{name}  {kind} {target}{}  held: {}",
        if document { " (document)" } else { "" },
        if held.is_empty() {
            "nothing".to_owned()
        } else {
            held.iter().cloned().collect::<Vec<_>>().join(", ")
        }
    );
    for note in &notes {
        println!("  # {note}");
    }

    for verb in shell_verbs(&kind, document) {
        let covered = held.contains(kernel_verb(verb));
        if !covered && !all {
            continue;
        }
        // `--all`: a verb no record covers is still probed, so `noGrant` is
        // the Host's verdict too; a Host that admits it is a disagreement.
        let row = |verb: &str, verdict: &str, what: &str| {
            if covered {
                row(verb, verdict, what);
            } else if verdict == "admitted" {
                row(verb, "noGrant BUT THE HOST ADMITTED THE PROBE", what);
            } else {
                row(
                    verb,
                    "noGrant",
                    &format!(
                        "no capability names {}; Host: {verdict}; {what}",
                        kernel_verb(verb)
                    ),
                );
            }
        };
        match *verb {
            "read" => {
                let verdict = verdict_of(view.as_ref().err().cloned());
                row(verb, &verdict, "signed resource read");
            }
            "write" if document => {
                let request = invoke(
                    name,
                    json!({"type":"document",
                    "actions":[{"type":"append","text":"can probe"}]}),
                );
                row(verb, &run.probe(verb, request)?, "append one line");
            }
            "write" => {
                let fields = view.as_ref().ok().map(fields).unwrap_or_default();
                if fields.is_empty() {
                    let action =
                        json!({"type":"create","key":{"type":"object","field":"1"},"value":"0"});
                    let request = invoke(name, json!({"type":"scalar","actions":[action]}));
                    row(
                        verb,
                        &run.probe(verb, request)?,
                        "create field 1 = 0 (no field to write)",
                    );
                }
                for (field, value) in fields.iter().take(MAX_FIELDS) {
                    for (next, label) in [(value + 1, "up"), (value - 1, "down")] {
                        let action = json!({"type":"write","key":{"type":"object","field":field},
                            "value":next.to_string(),"expected":value.to_string()});
                        let request = invoke(name, json!({"type":"scalar","actions":[action]}));
                        row(
                            verb,
                            &run.probe(verb, request)?,
                            &format!("field {field}: {value} -> {next} ({label})"),
                        );
                    }
                }
                if fields.len() > MAX_FIELDS {
                    println!(
                        "  # write: {} more field(s) not probed",
                        fields.len() - MAX_FIELDS
                    );
                }
            }
            "edit" | "mark" => {
                // The last live text line of the kernel's order, as this probe's
                // own read places it (the line `doc show` numbers last).
                let last = host_document(root, workspace, &reference).ok().and_then(|document| {
                    let lines = live_lines(&document).ok()?;
                    let (index, line) = lines.iter().enumerate().rev().find(|(_, line)| line["kind"] == "atom")?;
                    Some((index + 1, line["atom"].as_str()?.to_owned(), line["payload"].as_str()?.to_owned()))
                });
                let Some((number, atom, payload)) = last else {
                    row(verb, "(not probed)", "no line");
                    continue;
                };
                if *verb == "edit" {
                    let text = String::from_utf8_lossy(&crate::decode_hex(&payload).unwrap_or_default()).into_owned();
                    let request = invoke(
                        name,
                        json!({"type":"document",
                        "actions":[{"type":"edit","line":number.to_string(),"text":text}]}),
                    );
                    row(verb, &run.probe(verb, request)?, &format!("line {number} to its own text"));
                } else {
                    // A mark writes the annotations field only (K-MARKS): a reviewer
                    // scoped to fields={annotations} holds this and not `edit`.
                    let revision = view
                        .as_ref()
                        .ok()
                        .and_then(|view| content_page(view, name).ok())
                        .and_then(|page| page_entries(page).ok())
                        .and_then(|entries| {
                            entries.iter().find(|entry| entry["type"] == "atom" && entry["id"] == atom.as_str())
                        })
                        .and_then(|entry| entry["revision"].as_str().map(str::to_owned))
                        .unwrap_or_default();
                    let request = invoke(
                        name,
                        json!({"type":"content","actions":[{"type":"mark","mark":random_nonce()?,
                            "target":{"type":"atom","atom":atom},"revision":revision,"kind":{"type":"bold"}}]}),
                    );
                    row(verb, &run.probe(verb, request)?, &format!("bold on line {number}"));
                }
            }
            "link" => {
                let request = invoke(
                    name,
                    json!({"type":"document",
                    "actions":[{"type":"link","to":name,"relation":"0"}]}),
                );
                row(
                    verb,
                    &run.probe(verb, request)?,
                    &format!("{name} -> {name}, relation 0"),
                );
            }
            "delegate" => {
                // To myself, narrowed to itself: the parent's own verbs and
                // maxCost. When the parent record is unreadable, authoring the
                // delegation reads it, and the Host's refusal of that read is
                // the verdict.
                let (verbs, max_cost, what) = match parent.as_ref() {
                    Some(head) => {
                        let max_cost = head["maxCost"].as_str().unwrap_or("0").to_owned();
                        let what = format!("to myself, the parent's own verbs, maxCost {max_cost}");
                        (head["verbs"].clone(), max_cost, what)
                    }
                    None => (
                        json!(["observe"]),
                        "1".to_owned(),
                        "to myself; the parent record is unreadable, so authoring reads it"
                            .to_owned(),
                    ),
                };
                let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                    "name":name,"recipient":me,"verbs":verbs,"maxCost":max_cost});
                row(verb, &run.probe(verb, request)?, &what);
            }
            "law" => match signed_view_decided(root, workspace, &reference, "policy")? {
                Ok(policy) => {
                    let request = json!({"type":"minidregg-workspace-proposal-v1",
                        "action":"install-policy","name":name,"predicate":policy["predicate"]});
                    row(
                        verb,
                        &run.probe(verb, request)?,
                        "reinstall the current law",
                    );
                }
                Err(line) => row(
                    verb,
                    &verdict_of(Some(line)),
                    "read the current law to reinstall it",
                ),
            },
            "revoke" => match delegated_recipients(root, name).first() {
                Some(recipient) => {
                    let request = json!({"type":"minidregg-workspace-proposal-v1",
                        "action":"revoke","name":name,"recipient":recipient});
                    row(
                        verb,
                        &run.probe(verb, request)?,
                        &format!("the grant this workspace made to {recipient}"),
                    );
                }
                None => row(
                    verb,
                    "(not probed)",
                    &format!("this workspace delegated nothing on {name}"),
                ),
            },
            _ => row(
                verb,
                "(not probed)",
                "no representative command in this client",
            ),
        }
    }
    Ok(())
}
