//! K-INSPECT-VIEWS (DEOS #13): `inspect caps|law|receipt|turn`, `why`.
//!
//! Each view gathers bytes this workspace already holds, or reads with its
//! own signed views (the same reads `read` and `can` make), writes them into
//! one JSON input (`inspect/NN-VIEW.json`, hex frames) and asks the Host's
//! `inspect VIEW` (Host/InspectRender.lean) to render them. Every decision
//! about what the bytes mean is the Lean view's; this file only collects
//! files and prints the Host's `text` (or, with `--json`, the whole result).
//! A view opens no Store and holds no authority: `inspect` is a pure function
//! of its input, and `turn` judges through the dry run (op 130), which never
//! appends.

use super::*;
use crate::{dry_run, inspect, note_host_decision, take_host_decision, HostDecision};
use std::time::SystemTime;

fn read_hex(path: &Path) -> Result<String> {
    Ok(hex(&fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?))
}

fn optional_hex(path: &Path) -> Result<Value> {
    if path.is_file() {
        Ok(Value::String(read_hex(path)?))
    } else {
        Ok(Value::Null)
    }
}

/// Run one Lean view over `input` and print its text (or its JSON).
fn render(root: &Path, workspace: &Value, view: &str, input: &Value, json_out: bool) -> Result<Value> {
    let dir = root.join("inspect");
    if !dir.exists() {
        fs::create_dir_all(&dir).map_err(|error| format!("cannot create {}: {error}", dir.display()))?;
    }
    let stem = format!("{}-{view}", random_nonce()?);
    let input_path = dir.join(format!("{stem}.json"));
    let output_path = dir.join(format!("{stem}.out.json"));
    create_private(
        &input_path,
        &serde_json::to_vec(input).map_err(|error| error.to_string())?,
    )?;
    let rendered = inspect(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        view,
        &input_path,
        &output_path,
    )?;
    if json_out {
        println!(
            "{}",
            serde_json::to_string_pretty(&rendered).map_err(|error| error.to_string())?
        );
    } else if let Some(text) = rendered.get("text").and_then(Value::as_str) {
        println!("{text}");
    }
    Ok(rendered)
}

/// A signed view of `view` through `reference`; the exact view bytes, or the
/// exact refusal frame the Host answered with.
fn signed_view_bytes(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    view: &str,
) -> Result<std::result::Result<Vec<u8>, Vec<u8>>> {
    take_host_decision();
    match signed_view(root, workspace, reference, view) {
        Ok((_, _, signed)) => {
            let attempt = signed.parent().ok_or("signed observation has no attempt")?;
            let bytes = fs::read(attempt.join("view.bin"))
                .map_err(|error| format!("cannot read the view: {error}"))?;
            Ok(Ok(bytes))
        }
        Err(error) => match take_host_decision() {
            Some(HostDecision::RefusedFrame { encoded, .. }) => Ok(Err(encoded)),
            _ => Err(error),
        },
    }
}

fn names(root: &Path, name: Option<&str>) -> Result<Vec<String>> {
    if let Some(name) = name {
        return Ok(vec![name.to_owned()]);
    }
    let mut names = Vec::new();
    for entry in fs::read_dir(root.join("refs")).map_err(|error| error.to_string())? {
        let file = entry.map_err(|error| error.to_string())?.file_name();
        if let Some(stem) = file.to_str().and_then(|f| f.strip_suffix(".json")) {
            // `lab.index` on disk is the reference `lab/index`.
            names.push(crate::workspace::ref_name_of_file(stem));
        }
    }
    names.sort();
    Ok(names)
}

/// `inspect caps [NAME]`: per resource, the capability records this reader
/// can read (one signed `capability` view per capability its reference names,
/// the Host's refusal frame where it cannot), plus the children of the
/// delegations it signed (its own plans and their outcomes).
fn caps(root: &Path, workspace: &Value, name: Option<&str>, json_out: bool) -> Result<()> {
    for name in names(root, name)? {
        let reference = reference(root, &name)?;
        let kind = member(&reference, "kind")?.to_owned();
        let target = member(&reference, "target")?.to_owned();
        let mut ids = Vec::<String>::new();
        for slot in ["observeCapability", "operationCapability", "controlCapability"] {
            if let Some(id) = reference.get(slot).and_then(Value::as_str) {
                if !ids.iter().any(|known| known == id) {
                    ids.push(id.to_owned());
                }
            }
        }
        let mut items = Vec::new();
        for id in &ids {
            let mut via = reference.clone();
            via["observeCapability"] = json!(id);
            match signed_view_bytes(root, workspace, &via, "capability")? {
                Ok(bytes) => items.push(json!({"type":"record","capability":id,"frame":hex(&bytes)})),
                Err(frame) => items.push(json!({"type":"refused","capability":id,"frame":hex(&frame)})),
            }
        }
        let mut proposals: Vec<PathBuf> = fs::read_dir(root.join("proposals"))
            .map(|entries| entries.flatten().map(|e| e.path()).collect())
            .unwrap_or_default();
        proposals.sort();
        for proposal in proposals {
            let id = proposal.file_name().and_then(|f| f.to_str()).unwrap_or("").to_owned();
            if id.starts_with("can-") {
                continue;
            }
            let Ok(summary) = bounded_json(&proposal.join("proposal.json")) else {
                continue;
            };
            if summary["delegation"]["name"].as_str() != Some(name.as_str()) {
                continue;
            }
            let attempt = root.join("attempts").join(&id);
            if !attempt.join("plan.bin").is_file() {
                continue;
            }
            items.push(json!({"type":"delegated","proposal":id,
                "plan":read_hex(&attempt.join("plan.bin"))?,
                "outcome":optional_hex(&attempt.join("outcome.bin"))?}));
        }
        render(
            root,
            workspace,
            "cap-tree",
            &json!({"kind":kind,"target":target,"items":items}),
            json_out,
        )?;
    }
    Ok(())
}

/// `inspect law NAME`: the installed law from the signed policy view, with the
/// current value of each slot it names from this reader's own resource read.
fn law(root: &Path, workspace: &Value, name: &str, json_out: bool) -> Result<()> {
    let reference = reference(root, name)?;
    let policy = match signed_view_bytes(root, workspace, &reference, "policy")? {
        Ok(bytes) => bytes,
        Err(frame) => {
            render(
                root,
                workspace,
                "why",
                &json!({"attempt":format!("policy read of {name}"),"frame":hex(&frame)}),
                json_out,
            )?;
            return Err("the Host refused the policy read".into());
        }
    };
    let resource = match signed_view_bytes(root, workspace, &reference, "resource")? {
        Ok(bytes) => Value::String(hex(&bytes)),
        Err(_) => Value::Null,
    };
    // The reader's own capability: which fields its grant names, so a field
    // missing from a narrowed read is told apart from one that is absent.
    let capability = match signed_view_bytes(root, workspace, &reference, "capability")? {
        Ok(bytes) => Value::String(hex(&bytes)),
        Err(_) => Value::Null,
    };
    render(
        root,
        workspace,
        "law",
        &json!({"name":name,"policy":hex(&policy),"resource":resource,"capability":capability}),
        json_out,
    )?;
    Ok(())
}

/// `inspect receipt ID`: the attempt's signed plan and the Host's outcome.
fn receipt(root: &Path, workspace: &Value, id: &str, json_out: bool) -> Result<()> {
    let attempt = root.join("attempts").join(id);
    let plan = attempt.join("plan.bin");
    if !plan.is_file() {
        return Err(format!("attempt {id} holds no signed plan"));
    }
    render(
        root,
        workspace,
        "receipt",
        &json!({"label":id,"plan":read_hex(&plan)?,"outcome":optional_hex(&attempt.join("outcome.bin"))?}),
        json_out,
    )?;
    Ok(())
}

/// `inspect turn ID|INTENT`: plan the proposal's intent and dry-run it (op
/// 130); render the plan the dry run judged, with its verdict. Nothing is
/// submitted.
fn turn(root: &Path, workspace: &Value, what: &str, json_out: bool) -> Result<()> {
    let intent = if what.contains('/') {
        PathBuf::from(what)
    } else {
        root.join("proposals").join(what).join("intent.json")
    };
    if !intent.is_file() {
        return Err(format!("no intent at {}", intent.display()));
    }
    let (attempt, _) = new_attempt(root)?;
    let verdict = dry_run(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        &intent,
        OsStr::new("intent"),
        &member_path(workspace, "key")?,
        &attempt,
    )?;
    let plan = if attempt.join("dry-run-plan.bin").is_file() {
        attempt.join("dry-run-plan.bin")
    } else {
        attempt.join("plan.bin")
    };
    let label = format!("{what} (dry run {})", attempt.file_name().and_then(|f| f.to_str()).unwrap_or(""));
    if plan.is_file() {
        render(
            root,
            workspace,
            "turn",
            &json!({"label":label,"plan":read_hex(&plan)?,
                "outcome":optional_hex(&attempt.join("refusal.frame"))?}),
            json_out,
        )?;
    } else if attempt.join("refusal.frame").is_file() {
        render(
            root,
            workspace,
            "why",
            &json!({"attempt":label,"frame":read_hex(&attempt.join("refusal.frame"))?}),
            json_out,
        )?;
    }
    match verdict {
        None => Ok(()),
        Some(line) => {
            // The Host refused: hand the frame back as the Host's decision, so
            // the shell ends `refused` (exit 3) and retains it like any other.
            if let Ok(encoded) = fs::read(attempt.join("refusal.frame")) {
                note_host_decision(HostDecision::RefusedFrame {
                    command: "dry-run".into(),
                    byte: 255,
                    encoded,
                    decoded: None,
                });
            }
            Err(line)
        }
    }
}

/// The refusal frames this workspace holds: each attempt's prepare refusal or
/// refused outcome, and (from the shell) HOME/refusals.
fn refusals(root: &Path, extra: Option<&Path>) -> Vec<(SystemTime, String, PathBuf, Option<PathBuf>)> {
    let mut found = Vec::new();
    let modified = |path: &Path| fs::metadata(path).and_then(|m| m.modified()).ok();
    if let Ok(entries) = fs::read_dir(root.join("attempts")) {
        for entry in entries.flatten() {
            let attempt = entry.path();
            let name = entry.file_name().to_string_lossy().into_owned();
            // A submit refused at planning (op 1). Dry-run frames (`refusal.frame`,
            // from `can`/`inspect turn`) are judgements, not attempts, and are skipped.
            let path = attempt.join("pre-submit-refusal.frame");
            if let Some(time) = modified(&path) {
                let intent = attempt.join("intent.json");
                found.push((time, name.clone(), path, intent.is_file().then_some(intent)));
            }
            // A submitted call's outcome, and each retry's (`retry-NNNN`), when refused.
            let mut outcomes = vec![attempt.join("outcome.bin")];
            if let Ok(files) = fs::read_dir(&attempt) {
                let mut retries: Vec<PathBuf> = files
                    .flatten()
                    .map(|f| f.path())
                    .filter(|p| {
                        let n = p.file_name().and_then(|f| f.to_str()).unwrap_or("");
                        n.starts_with("retry-") && n.ends_with(".bin")
                    })
                    .collect();
                retries.sort();
                outcomes.extend(retries);
            }
            for bin in outcomes {
                let decoded = bin.with_extension("json");
                if let (Some(time), Ok(value)) = (modified(&bin), bounded_json(&decoded)) {
                    if value["type"] == "refused" {
                        let intent = attempt.join("intent.json");
                        found.push((time, name.clone(), bin, intent.is_file().then_some(intent)));
                    }
                }
            }
        }
    }
    // The shell keeps its own copy of each refused frame (HOME/refusals); one
    // already held by an attempt is that attempt's, and is not listed twice.
    let held: Vec<Vec<u8>> = found
        .iter()
        .filter_map(|entry| fs::read(&entry.2).ok())
        .map(|mut bytes| {
            if bytes.first() == Some(&255) {
                bytes.remove(0);
            }
            bytes
        })
        .collect();
    if let Some(dir) = extra {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if fs::read(&path).is_ok_and(|bytes| held.contains(&bytes)) {
                    continue;
                }
                if path.extension().and_then(|e| e.to_str()) == Some("bin") {
                    if let Some(time) = modified(&path) {
                        let name = path.file_stem().and_then(|s| s.to_str()).unwrap_or("").to_owned();
                        found.push((time, name, path, None));
                    }
                }
            }
        }
    }
    found.sort_by(|a, b| a.0.cmp(&b.0).then(a.1.cmp(&b.1)));
    found
}

/// `why [ATTEMPT]`: the last refusal this workspace holds (or ATTEMPT's),
/// explained by the Lean view from the refusal frame alone. An `undisclosed`
/// refusal is a blind submission's by design; when the attempt kept its
/// intent, the same command is dry-run now (op 130, which judges only a
/// requester whose signed observation op 1 accepts) and its verdict shown.
fn why(root: &Path, workspace: &Value, attempt: Option<&str>, extra: Option<&Path>, json_out: bool) -> Result<()> {
    let found = refusals(root, extra);
    let chosen = match attempt {
        Some(name) => found.iter().rev().find(|entry| entry.1 == name),
        None => found.last(),
    };
    let Some((_, name, frame_path, intent)) = chosen else {
        return Err(match attempt {
            Some(name) => format!("no refusal is held for {name}"),
            None => "no refusal is held in this workspace".into(),
        });
    };
    let mut frame = fs::read(frame_path).map_err(|error| error.to_string())?;
    if frame_path.file_name().and_then(|f| f.to_str()) == Some("pre-submit-refusal.frame")
        && frame.first() == Some(&255)
    {
        frame.remove(0);
    }
    let mut input = json!({"attempt":name,"frame":hex(&frame)});
    let undisclosed = {
        let probe = render_quiet(root, workspace, &input)?;
        probe["reason"] == "undisclosed"
    };
    if undisclosed {
        if let Some(intent) = intent {
            let (dry, _) = new_attempt(root)?;
            let verdict = dry_run(
                &member_path(workspace, "host")?,
                &member_path(workspace, "config")?,
                intent,
                OsStr::new("intent"),
                &member_path(workspace, "key")?,
                &dry,
            )?;
            input["dryRun"] = match verdict {
                None => json!("admitted"),
                Some(_) if dry.join("refusal.frame").is_file() => {
                    json!(read_hex(&dry.join("refusal.frame"))?)
                }
                Some(_) => Value::Null,
            };
        }
    }
    render(root, workspace, "why", &input, json_out)?;
    Ok(())
}

/// The why view's JSON without printing it (to read the reason).
fn render_quiet(root: &Path, workspace: &Value, input: &Value) -> Result<Value> {
    let dir = root.join("inspect");
    if !dir.exists() {
        fs::create_dir_all(&dir).map_err(|error| format!("cannot create {}: {error}", dir.display()))?;
    }
    let stem = format!("{}-why-probe", random_nonce()?);
    let input_path = dir.join(format!("{stem}.json"));
    create_private(&input_path, &serde_json::to_vec(input).map_err(|error| error.to_string())?)?;
    inspect(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
        "why",
        &input_path,
        &dir.join(format!("{stem}.out.json")),
    )
}

pub(super) fn run(
    root: &Path,
    workspace: &Value,
    view: &str,
    name: Option<&str>,
    refusal_dir: Option<&Path>,
    json_out: bool,
) -> Result<()> {
    let need = |what: &str| name.ok_or_else(|| format!("inspect {view} needs --name {what}"));
    match view {
        "caps" => caps(root, workspace, name, json_out),
        "law" => law(root, workspace, need("REF")?, json_out),
        "receipt" => receipt(root, workspace, need("ATTEMPT")?, json_out),
        "turn" => turn(root, workspace, need("PROPOSAL")?, json_out),
        "why" => why(root, workspace, name, refusal_dir, json_out),
        _ => Err("--view must be caps, law, receipt, turn or why".into()),
    }
}
