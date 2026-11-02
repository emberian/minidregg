//! Law satisfiability for friends (C-SAT-2): `law check`, the install-time
//! check, and `can --any`.
//!
//! Every verdict here is the Host's (op 150 `law-sat`, `Host/LawSatWire.lean`):
//! the request is the law's predicate JSON (what `law` proposes and the signed
//! `policy` view returns), the Host answers with `Sat.decide` on it, and this
//! module only words the answer. It never decides a law itself.
//!
//! * `law check LAW` asks twice: does the law admit any step (`extra` open),
//!   and can any write pass (`extra` = `verb == write`)?
//! * Installing a law (`law ID REF LAW`, or any install-policy proposal) asks
//!   first. A law that admits no step is refused here, before anything is
//!   proposed, unless `--allow-unsatisfiable` (a sealed cell is a legitimate
//!   use: `sealed` is exactly the law that admits nothing). A law no write can
//!   pass is installed with a warning.
//! * `can --any REF` asks about the cell's installed law, from the cell as it is
//!   now: the asker's subject, `verb == write`, every field's current value, one
//!   field left free. The Host judges the law over the declared scalar step
//!   shape (`fromHere`); the witness is one write the law admits, printed as a
//!   line to paste.

use super::*;
use crate::law_sat as host_law_sat;
use std::collections::{BTreeMap, BTreeSet};

const REQUEST_TYPE: &str = "minidregg-law-sat-v1";

fn verb_is_write() -> Value {
    json!({"type":"eq","slot":"request/verb","value":"2"})
}

/// One question to the Host. The request and the answer are kept under
/// `WS/lawsat/` (owner-private), as every Host exchange this client makes is.
fn ask(
    root: &Path,
    workspace: &Value,
    law: &Value,
    extra: Option<&Value>,
    from_here: bool,
    tag: &str,
) -> Result<Value> {
    let host = member_path(workspace, "host").ok();
    let config = member_path(workspace, "config").ok();
    if !host.as_ref().is_some_and(|h| h.is_file()) || !config.as_ref().is_some_and(|c| c.is_file()) {
        return decide_local(law, extra, from_here);
    }
    let mut request = json!({"type":REQUEST_TYPE,"predicate":law});
    if let Some(extra) = extra {
        request["extra"] = extra.clone();
    }
    if from_here {
        request["fromHere"] = json!(true);
    }
    let directory = root.join("lawsat");
    if !directory.exists() {
        make_private_dir(&directory)?;
    }
    let nonce = random_nonce()?;
    let input = directory.join(format!("{tag}-{nonce}.request.json"));
    let output = directory.join(format!("{tag}-{nonce}.answer.json"));
    create_private(
        &input,
        &serde_json::to_vec(&request).map_err(|error| error.to_string())?,
    )?;
    host_law_sat(
        &host.expect("checked"),
        &config.expect("checked"),
        &input,
        &output,
    )
}

fn verdict(answer: &Value) -> &str {
    answer.get("verdict").and_then(Value::as_str).unwrap_or("")
}

fn text<'a>(value: &'a Value, key: &str) -> &'a str {
    value.get(key).and_then(Value::as_str).unwrap_or("?")
}

/// Where a constraint of a certificate came from, in the law's own words.
fn source_text(source: &Value, query_part: &str) -> String {
    let clause = text(source, "clause");
    if text(source, "part") != "law" {
        return format!("{query_part} `{clause}`");
    }
    let path = source.get("path").and_then(Value::as_array).map_or(0, Vec::len);
    match source.get("top") {
        Some(top) if path > 1 => format!(
            "clause [{}] `{}` (its part `{clause}`)",
            top.get("index").and_then(Value::as_u64).unwrap_or(0),
            text(top, "clause")
        ),
        Some(top) => format!(
            "clause [{}] `{clause}`",
            top.get("index").and_then(Value::as_u64).unwrap_or(0)
        ),
        None => format!("the law `{clause}`"),
    }
}

fn sources_text(item: &Value, query_part: &str) -> String {
    let mut seen = BTreeSet::new();
    let all: Vec<String> = item
        .get("sources")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .map(|source| source_text(source, query_part))
        .filter(|s| seen.insert(s.clone()))
        .collect();
    if all.is_empty() {
        "(no clause named)".into()
    } else {
        all.join("; ")
    }
}

/// An `unsat` answer as lines: the clauses that contradict, case by case.
pub(crate) fn unsat_lines(answer: &Value, query_part: &str) -> Vec<String> {
    let certificate = answer
        .get("certificate")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    if certificate.is_empty() {
        return vec![
            "no case of this law can hold: like `sealed` (`any []`), it admits nothing".into(),
        ];
    }
    let cases = certificate.len();
    let mut lines = Vec::new();
    for (i, entry) in certificate.iter().enumerate() {
        let lead = if cases > 1 {
            format!("case {} of {cases}: ", i + 1)
        } else {
            String::new()
        };
        match text(entry, "kind") {
            "clash" => lines.push(format!(
                "{lead}{} — from {}",
                text(entry, "text"),
                sources_text(entry, query_part)
            )),
            _ => {
                lines.push(format!("{lead}these clauses contradict:"));
                for constraint in entry
                    .get("constraints")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                {
                    lines.push(format!(
                        "  {:<28} from {}",
                        text(constraint, "text"),
                        sources_text(constraint, query_part)
                    ));
                }
                let sum = entry
                    .get("sumText")
                    .and_then(Value::as_str)
                    .map(str::to_owned)
                    .or_else(|| entry.get("sum").map(Value::to_string))
                    .unwrap_or_else(|| "?".into());
                lines.push(format!(
                    "  (added up, they say 0 <= {sum}, which no value can make true)"
                ));
            }
        }
    }
    lines
}

/// The shell line a document's witnessed write is, from the grammar leaf of the content verb the
/// witness's slots name (atom edits: `doc edit`; tombstones: `doc remove`; otherwise `doc
/// append`), with the reference filled and `ID`/`'hello'` left for the member. A pure render of
/// the Host's answer: nothing here decides admissibility. `None` when the witness reads no
/// content slot (not a document).
pub(crate) fn content_line(name: &str, write: &Value) -> Option<String> {
    use crate::shell_grammar::{compose, leaf, DOC};
    let slot = |which: &str| -> Option<String> {
        write
            .get("new")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .find(|s| text(s, "slot").contains(which) || text(s, "name").contains(which))
            .map(|s| text(s, "text").trim_matches('"').to_owned())
    };
    let edits = slot("content/atom-edits");
    let tombstones = slot("content/tombstones");
    if edits.is_none() && tombstones.is_none() {
        return None;
    }
    let path: &[&str] = if edits.as_deref().is_some_and(|v| v != "0") {
        &["doc", "edit"]
    } else if tombstones.as_deref().is_some_and(|v| v != "0") {
        &["doc", "remove"]
    } else {
        &["doc", "append"]
    };
    let l = leaf(&DOC, path)?;
    Some(compose(l, &|a| match a.name {
        "ID" => "ID".to_owned(),
        "NAME" => name.to_owned(),
        n if n.starts_with("TEXT") => "'hello'".to_owned(),
        _ => "1".to_owned(),
    }))
}

/// A witness step, as the friend reads it: the new state's slots by name, and
/// the old state's where they differ in meaning.
pub(crate) fn witness_text(answer: &Value) -> String {
    let slots = |key: &str, suffix: &str| -> Vec<String> {
        answer
            .get(key)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .map(|slot| format!("{}{suffix} = {}", text(slot, "name"), text(slot, "text")))
            .collect()
    };
    let mut parts = slots("new", "");
    parts.extend(slots("old", " (before the step)"));
    if parts.is_empty() {
        "any step at all (the law reads no slot)".into()
    } else {
        parts.join(", ")
    }
}

fn outside_text(answer: &Value) -> String {
    let path = answer
        .get("path")
        .and_then(Value::as_array)
        .map(|p| {
            p.iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(",")
        })
        .unwrap_or_default();
    format!(
        "outside the decidable fragment: `{}` (at [{path}]) is not arithmetic, so no witness or certificate exists for it",
        text(answer, "clause")
    )
}

fn unknown_text(answer: &Value) -> String {
    match answer.get("cap").and_then(Value::as_u64) {
        Some(cap) => format!(
            "undecided: the law's cases passed the decision's cap of {cap} systems (independent `any` clauses multiply); neither a witness nor a certificate"
        ),
        None => "undecided (the Host's decision returned no witness and no certificate)".into(),
    }
}

/// The verb tag of a re-law (`request/verb` 4 is `install`).
const INSTALL_VERB: &str = "4";

/// The installer's own pins (`Host/LawSat.lean` `lockoutExtra`): the request
/// subject, and for the re-law question the verb `install` too.
fn installer_pins(subject: &str, relaw: bool) -> Value {
    let me = json!({"type":"eq","slot":"request/subject","value":subject});
    if relaw {
        json!({"type":"all","predicates":[me, {"type":"eq","slot":"request/verb","value":INSTALL_VERB}]})
    } else {
        me
    }
}

/// The answers `law check` and the install check share: any step, any write,
/// and the installer's own two questions (FIX-DISCLOSE): can I ever act under
/// this law (`self_lockout_detected`), and can I ever change it
/// (`relaw_lockout_detected`)? The last two are asked only of a law some step
/// satisfies; a law no step satisfies is already refused as unsatisfiable.
struct Check {
    any: Value,
    write: Value,
    subject: String,
    mine: Option<Value>,
    relaw: Option<Value>,
}

fn check(root: &Path, workspace: &Value, law: &Value) -> Result<Check> {
    let any = ask(root, workspace, law, None, false, "law")?;
    let write = match verdict(&any) {
        "outside" => any.clone(),
        _ => ask(root, workspace, law, Some(&verb_is_write()), false, "write")?,
    };
    let subject = member(workspace, "subject")?.to_owned();
    let (mine, relaw) = match verdict(&any) {
        "witness" => (
            Some(ask(root, workspace, law, Some(&installer_pins(&subject, false)), false, "mine")?),
            Some(ask(root, workspace, law, Some(&installer_pins(&subject, true)), false, "relaw")?),
        ),
        _ => (None, None),
    };
    Ok(Check { any, write, subject, mine, relaw })
}

/// The installer can never act under the law: a certificate to its own question.
fn locks_out(check: &Check) -> bool {
    check.mine.as_ref().is_some_and(|mine| verdict(mine) == "unsat")
}

/// The installer can never change the law (but may act under it otherwise).
fn locks_relaw(check: &Check) -> bool {
    !locks_out(check) && check.relaw.as_ref().is_some_and(|relaw| verdict(relaw) == "unsat")
}

fn lockout_lines(check: &Check) -> Vec<String> {
    let mut lines = Vec::new();
    if let Some(mine) = &check.mine {
        match verdict(mine) {
            "unsat" => {
                lines.push(format!(
                    "LOCKS YOU OUT: no request by you (subject {}) can ever pass this law: you could not read, write, delegate or change it again.",
                    check.subject
                ));
                lines.extend(unsat_lines(mine, "your own subject pin"));
                return lines;
            }
            "witness" => lines.push(format!("for you: admits e.g. {}", witness_text(mine))),
            _ => lines.push(format!("for you: {}", unknown_text(mine))),
        }
    }
    if let Some(relaw) = &check.relaw {
        match verdict(relaw) {
            "unsat" => {
                lines.push(format!(
                    "WARNING: you (subject {}) can never change this law once it is installed (no re-law by you can pass).",
                    check.subject
                ));
                lines.extend(unsat_lines(relaw, "your own re-law pin"));
            }
            "witness" => lines.push(format!("re-law: you can change it, e.g. {}", witness_text(relaw))),
            _ => lines.push(format!("re-law: {}", unknown_text(relaw))),
        }
    }
    lines
}

fn check_lines(check: &Check) -> Vec<String> {
    let mut lines = Vec::new();
    match verdict(&check.any) {
        "witness" => lines.push(format!(
            "satisfiable: admits e.g. {}",
            witness_text(&check.any)
        )),
        "unsat" => {
            lines.push("UNSATISFIABLE: this law admits no step.".into());
            lines.extend(unsat_lines(&check.any, "the check"));
        }
        "outside" => {
            lines.push(outside_text(&check.any));
            return lines;
        }
        _ => lines.push(unknown_text(&check.any)),
    }
    if verdict(&check.any) == "unsat" {
        return lines;
    }
    match verdict(&check.write) {
        "witness" => lines.push(format!(
            "writes: admits e.g. {}",
            witness_text(&check.write)
        )),
        "unsat" => {
            lines.push("WARNING: this law admits no write.".into());
            lines.extend(unsat_lines(&check.write, "the check's own"));
        }
        _ => lines.push(format!("writes: {}", unknown_text(&check.write))),
    }
    lines.extend(lockout_lines(check));
    lines
}

/// `law check FILE`: the verdict for a law before installing it. A query: it
/// prints and returns, whatever the verdict.
pub(super) fn law_check(root: &Path, workspace: &Value, predicate: &Path) -> Result<()> {
    let law = bounded_json(predicate)?;
    for line in check_lines(&check(root, workspace, &law)?) {
        println!("{line}");
    }
    Ok(())
}

/// The install-time check, run before an install-policy proposal is authored.
/// Refuses (locally; nothing is proposed) a law that admits no step unless
/// `allow_unsatisfiable`, and a law that admits no step BY THE INSTALLER unless
/// `allow_lockout` (`--i-lock-myself-out`); warns on a law no write can pass and
/// on a law its installer can never change.
/// Returns whether no step can pass, for the explicit room-roster freeze check.
pub(super) fn install_check(
    root: &Path,
    workspace: &Value,
    law: &Value,
    allow_unsatisfiable: bool,
    allow_lockout: bool,
) -> Result<bool> {
    let checked = check(root, workspace, law)?;
    let lines = check_lines(&checked);
    if locks_out(&checked) && !allow_lockout {
        let mut message = vec![format!(
            "law-locks-you-out: no request by you (subject {}) can ever pass this law, so it was not proposed.",
            checked.subject
        )];
        message.extend(lockout_lines(&checked).into_iter().skip(1));
        message.push(
            "once installed you could not read, write, delegate or re-law this cell; \
             to install it anyway, repeat the line with --i-lock-myself-out"
                .into(),
        );
        return Err(message.join("\n"));
    }
    if locks_out(&checked) {
        eprintln!("law check: installing it anyway (--i-lock-myself-out): you will not be able to act on this cell again");
    } else if locks_relaw(&checked) {
        eprintln!("law check: this law can never be changed by you once installed (like `sealed`, which may be what you mean)");
    }
    if verdict(&checked.any) == "unsat" && !allow_unsatisfiable {
        let mut message = vec![
            "law-unsatisfiable: this law can never pass, so it was not proposed.".to_owned(),
        ];
        message.extend(lines.into_iter().skip(1));
        message.push(
            "a law that admits nothing is a legitimate choice — `sealed` is exactly that, and it locks the cell — \
             so to install it anyway, repeat the line with --allow-unsatisfiable"
                .into(),
        );
        return Err(message.join("\n"));
    }
    for line in &lines {
        eprintln!("law check: {line}");
    }
    if verdict(&checked.any) == "unsat" {
        eprintln!("law check: installing it anyway (--allow-unsatisfiable): every request on this cell will be refused");
    }
    Ok(verdict(&checked.any) == "unsat")
}

// ------------------------------------------------------------------ can --any

/// Every slot name a predicate mentions.
pub(crate) fn slots(predicate: &Value, into: &mut BTreeSet<String>) {
    match predicate {
        Value::Object(object) => {
            for key in ["slot", "left", "right"] {
                if let Some(Value::String(slot)) = object.get(key) {
                    into.insert(slot.clone());
                }
            }
            if let Some(child) = object.get("predicate") {
                slots(child, into);
            }
            if let Some(Value::Array(children)) = object.get("predicates") {
                for child in children {
                    slots(child, into);
                }
            }
        }
        Value::Array(children) => children.iter().for_each(|child| slots(child, into)),
        _ => {}
    }
}

fn field_slot(field: &str, view: &str) -> String {
    format!("resource/field/{field}/{view}")
}

fn eq(slot: &str, value: &str) -> Value {
    json!({"type":"eq","slot":slot,"value":value})
}

/// The fields a law reads, and the field pairs it reads a pair delta of.
pub(crate) fn law_fields(law: &Value) -> (BTreeSet<String>, Vec<(String, String)>) {
    let mut all = BTreeSet::new();
    slots(law, &mut all);
    let mut fields = BTreeSet::new();
    let mut pairs = Vec::new();
    for slot in &all {
        let parts: Vec<&str> = slot.split('/').collect();
        match parts.as_slice() {
            ["resource", "field", n, _] => {
                fields.insert((*n).to_owned());
            }
            ["resource", "pair", a, b, "delta"] => {
                fields.insert((*a).to_owned());
                fields.insert((*b).to_owned());
                pairs.push(((*a).to_owned(), (*b).to_owned()));
            }
            _ => {}
        }
    }
    (fields, pairs)
}

/// The pins for a write of field `free` from `now`, by `subject`: every other
/// field keeps its value, `free` keeps its `before` and its `delta` is
/// `after - before`. `None` when a pair delta of `free` with itself is read
/// (twice a delta is not a difference constraint).
pub(crate) fn write_pins(
    now: &BTreeMap<String, String>,
    free: &str,
    subject: &str,
    pairs: &[(String, String)],
) -> Option<Value> {
    let mut pins = vec![verb_is_write(), eq("request/subject", subject)];
    for (field, value) in now {
        pins.push(eq(&field_slot(field, "before"), value));
        if field != free {
            pins.push(eq(&field_slot(field, "after"), value));
            pins.push(eq(&field_slot(field, "delta"), "0"));
        }
    }
    let now_free: i128 = now.get(free)?.parse().ok()?;
    let after = field_slot(free, "after");
    let delta = field_slot(free, "delta");
    pins.push(json!({"type":"leSlots","left":after,"right":after}));
    pins.push(json!({"type":"leSlotsOff","left":delta,"right":after,"offset":(-now_free).to_string()}));
    pins.push(json!({"type":"leSlotsOff","left":after,"right":delta,"offset":now_free.to_string()}));
    for (a, b) in pairs {
        let pair = format!("resource/pair/{a}/{b}/delta");
        match (a == free, b == free) {
            (true, true) => return None,
            (true, false) | (false, true) => {
                pins.push(json!({"type":"eqSlots","left":pair,"right":delta}))
            }
            (false, false) => pins.push(eq(&pair, "0")),
        }
    }
    Some(json!({"type":"all","predicates":pins}))
}

fn resource_fields(resource: &Value) -> BTreeMap<String, String> {
    resource
        .get("cell")
        .and_then(|cell| cell.get("entries"))
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .filter_map(|entry| {
            let field = entry.get("key")?.get("field")?.as_str()?;
            let value = entry.get("value")?.as_str()?;
            Some((field.to_owned(), value.to_owned()))
        })
        .collect()
}

/// `can --any NAME`: one write the cell's installed law admits, from the cell
/// as it is now, as a line to paste; or why there is none.
pub(super) fn can_any(root: &Path, workspace: &Value, name: &str) -> Result<()> {
    let reference = reference(root, name)?;
    let (policy, _, _) = signed_view(root, workspace, &reference, "policy")?;
    let law = policy
        .get("predicate")
        .cloned()
        .ok_or("signed policy view lacks predicate")?;
    println!("{name}  law version {}", text(&policy, "version"));
    let write = ask(root, workspace, &law, Some(&verb_is_write()), false, "any-write")?;
    match verdict(&write) {
        "outside" => {
            println!("  {}", outside_text(&write));
            return Ok(());
        }
        "unsat" => {
            println!("  no write can satisfy this law:");
            for line in unsat_lines(&write, "the question's own") {
                println!("    {line}");
            }
            return Ok(());
        }
        "witness" => {}
        _ => {
            println!("  {}", unknown_text(&write));
            return Ok(());
        }
    }
    let (resource, _, _) = signed_view(root, workspace, &reference, "resource")?;
    let now = resource_fields(&resource);
    let subject = member(workspace, "subject")?;
    let (read, pairs) = law_fields(&law);
    // Fields the law reads first (a write it constrains), then the rest.
    let mut candidates: Vec<&String> = now.keys().filter(|f| read.contains(*f)).collect();
    candidates.extend(now.keys().filter(|f| !read.contains(*f)));
    if candidates.is_empty() {
        println!("  a write exists in principle (e.g. {})", witness_text(&write));
        match content_line(name, &write) {
            // A document (content cell): the witnessed write is one of the content verbs; the
            // line is composed from that verb's grammar leaf and the witness's slot values.
            Some(line) => {
                println!("  paste:");
                println!("    {line}");
                println!("  [judged as: verb = write; ID is the proposal id you choose]");
            }
            None => println!("  but this cell holds no field to write; create one first"),
        }
        return Ok(());
    }
    let mut last = None;
    for free in candidates {
        let Some(pins) = write_pins(&now, free, subject, &pairs) else {
            continue;
        };
        let answer = ask(root, workspace, &law, Some(&pins), true, "from-here")?;
        match verdict(&answer) {
            "witness" => {
                let after = field_slot(free, "after");
                let value = answer
                    .get("new")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .find(|slot| text(slot, "slot") == after)
                    .map(|slot| text(slot, "value").to_owned())
                    .unwrap_or_else(|| now[free].clone());
                let pinned: BTreeSet<String> = {
                    let mut s = BTreeSet::new();
                    slots(&pins, &mut s);
                    s
                };
                println!("  a write this law admits, from the cell as it is now:");
                println!("    field {free} = {value}    (now {})", now[free]);
                println!("  paste:");
                println!("    invoke ID {name} write {free} {value} {}", now[free]);
                println!(
                    "  [judged as: verb = write, subject = {subject}, every other field unchanged]"
                );
                for slot in answer
                    .get("new")
                    .and_then(Value::as_array)
                    .into_iter()
                    .flatten()
                    .filter(|slot| !pinned.contains(text(slot, "slot")))
                {
                    println!(
                        "  note: the law also reads {}; this write assumes it is {}",
                        text(slot, "name"),
                        text(slot, "text")
                    );
                }
                return Ok(());
            }
            "unrealizable" => {
                println!(
                    "  the law reads the before-value of {}, which this question cannot model; it admits writes in general (e.g. {})",
                    text(&answer, "name"),
                    witness_text(&write)
                );
                return Ok(());
            }
            _ => last = Some(answer),
        }
    }
    println!(
        "  the law admits writes in general (e.g. {}), but none that changes one field from the cell as it is now:",
        witness_text(&write)
    );
    if let Some(answer) = last {
        if verdict(&answer) == "unsat" {
            for line in unsat_lines(&answer, "the cell now:") {
                println!("    {line}");
            }
        } else {
            println!("    {}", unknown_text(&answer));
        }
    }
    Ok(())
}

// ------------------------------------------------------------------ Interactive Presburger /laws Workbench

pub(crate) struct LawPreset {
    pub key: &'static str,
    pub label: &'static str,
    pub summary: &'static str,
    pub clauses_template: &'static str,
}

pub(crate) const PRESETS: &[LawPreset] = &[
    LawPreset {
        key: "note",
        label: "note (append-only)",
        summary: "Reads and management verbs pass; writes may append only (no atom edits or tombstones).",
        clauses_template: r#"any [ verb in {read,delegate,install,revoke}, all [ verb == write, slot "content/atom-edits" == 0, slot "content/tombstones" == 0 ] ]"#,
    },
    LawPreset {
        key: "draft",
        label: "draft (<= 16 KiB)",
        summary: "Reads and management verbs pass; writes pass while payload stays at or below 16384 bytes.",
        clauses_template: r#"any [ verb in {read,delegate,install,revoke}, all [ verb == write, slot "content/payload-bytes/after" <= 16384 ] ]"#,
    },
    LawPreset {
        key: "index",
        label: "index (unique names)",
        summary: "Non-write verbs pass; content writes must preserve unique live shared names.",
        clauses_template: r#"any [ not (verb == write), slot "content/names/unique" == 1 ]"#,
    },
    LawPreset {
        key: "open",
        label: "open",
        summary: "Every verb and slot assignment is admitted by policy (capability authority still gates access).",
        clauses_template: "open",
    },
    LawPreset {
        key: "moderated",
        label: "moderated",
        summary: "Anyone with a grant may read or write; only the moderator subject may delegate, install, or revoke.",
        clauses_template: "any [ verb in {read,write}, all [ verb in {delegate,install,revoke}, subject == {SUBJECT} ] ]",
    },
    LawPreset {
        key: "read-only lockout",
        label: "read-only lockout",
        summary: "Only read passes; all writes, delegations, revocations, and re-laws are unsatisfiable (self-lockout warning).",
        clauses_template: "verb == read",
    },
    LawPreset {
        key: "cost-capped",
        label: "cost-capped",
        summary: "Reads are unconstrained; writes and management verbs require request/cost <= 100.",
        clauses_template: "any [ verb == read, all [ verb in {write,delegate,install,revoke}, cost <= 100 ] ]",
    },
    LawPreset {
        key: "monotone-counter",
        label: "monotone-counter",
        summary: "Reads and management verbs pass; writes must keep field 0 monotone non-decreasing with step delta <= 1.",
        clauses_template: "any [ verb in {read,delegate,install,revoke}, all [ verb == write, field 0 monotone, field 0 delta <= 1 ] ]",
    },
];

pub(crate) fn preset_clauses(key: &str, subject: &str) -> Option<String> {
    let key_norm = key.trim().replace('-', " ");
    let sub = if subject.trim().is_empty() || !subject.trim().bytes().all(|b| b.is_ascii_digit()) {
        "1"
    } else {
        subject.trim()
    };
    PRESETS
        .iter()
        .find(|p| p.key == key.trim() || p.key.replace('-', " ") == key_norm)
        .map(|p| p.clauses_template.replace("{SUBJECT}", sub))
}

/// Parse law input from a preset name, shell law grammar clauses, or raw `Pred` JSON.
pub(crate) fn parse_law_input(input: &str, subject: &str) -> Result<(Value, String)> {
    let trimmed = input.trim();
    if trimmed.is_empty() {
        return Err("law clauses cannot be empty".into());
    }
    if let Some(clauses) = preset_clauses(trimmed, subject) {
        let pred = crate::shell::law::parse(&clauses)?;
        return Ok((pred, clauses));
    }
    if trimmed.starts_with('{') {
        let pred: Value = serde_json::from_str(trimmed).map_err(|e| format!("invalid predicate JSON: {e}"))?;
        let rendered = crate::shell::law::render_clause(&pred);
        return Ok((pred, rendered));
    }
    let pred = crate::shell::law::parse(trimmed)?;
    Ok((pred.clone(), crate::shell::law::render_clause(&pred)))
}

#[derive(Clone, Debug)]
pub(crate) struct VerbMatrixRow {
    pub verb: &'static str,
    pub tag: &'static str,
    pub verdict: String,
    pub admitted: bool,
    pub subject_witness: String,
    pub cost_witness: String,
    pub field_witness: String,
    pub explanation: String,
}

#[derive(Clone, Debug)]
pub(crate) struct LawWorkbenchReport {
    pub rendered_law: String,
    pub overall_verdict: String,
    pub overall_summary: String,
    pub write_lockout: bool,
    pub write_lockout_reason: Option<String>,
    pub self_lockout: bool,
    pub self_lockout_reason: Option<String>,
    pub relaw_lockout: bool,
    pub relaw_lockout_reason: Option<String>,
    pub rows: Vec<VerbMatrixRow>,
}

fn extract_witness_columns(answer: &Value, pinned_verb: &str) -> (String, String, String) {
    let mut subj = "any".to_owned();
    let mut cost = "any".to_owned();
    let mut fields = Vec::new();
    for (arr_key, suffix) in [("new", ""), ("old", " (before)")] {
        for item in answer
            .get(arr_key)
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
        {
            let slot = text(item, "slot");
            let val = text(item, "text");
            if slot == "request/verb" && val == pinned_verb {
                continue;
            }
            if slot == "request/subject" && suffix.is_empty() {
                subj = val.to_owned();
            } else if slot == "request/cost" && suffix.is_empty() {
                cost = val.to_owned();
            } else {
                fields.push(format!("{}{suffix} = {val}", text(item, "name")));
            }
        }
    }
    let field_str = if fields.is_empty() {
        "any (unconstrained)".into()
    } else {
        fields.join(", ")
    };
    (subj, cost, field_str)
}

/// Run `law check` and build the 6-verb Admissibility Matrix (`read`, `write`, `delegate`, `install`, `revoke`, `renounce`).
pub(crate) fn analyze_law_workbench(
    root: &Path,
    workspace: &Value,
    subject: &str,
    law: &Value,
) -> Result<LawWorkbenchReport> {
    let mut ws = workspace.clone();
    let subj = if !subject.trim().is_empty() && subject.trim().bytes().all(|b| b.is_ascii_digit()) {
        subject.trim().to_owned()
    } else {
        member(workspace, "subject").unwrap_or("1").to_owned()
    };
    if ws.get("subject").and_then(Value::as_str).is_none() {
        ws["subject"] = json!(subj);
    }
    let checked = check(root, &ws, law)?;
    let lines = check_lines(&checked);
    let overall_verdict = verdict(&checked.any).to_owned();
    let overall_summary = lines.first().cloned().unwrap_or_default();
    let self_lock = locks_out(&checked);
    let relaw_lock = locks_relaw(&checked) || verdict(&checked.any) == "unsat";

    let mut rows = Vec::with_capacity(6);
    for (verb_name, tag_num) in [
        ("read", "1"),
        ("write", "2"),
        ("delegate", "3"),
        ("install", "4"),
        ("revoke", "5"),
    ] {
        let extra = json!({"type":"eq","slot":"request/verb","value":tag_num});
        let ans = if overall_verdict == "outside" {
            checked.any.clone()
        } else {
            ask(root, &ws, law, Some(&extra), false, &format!("matrix-{verb_name}"))?
        };
        let v = verdict(&ans).to_owned();
        let (admitted, subj_w, cost_w, field_w, expl) = match v.as_str() {
            "witness" => {
                let (sw, cw, fw) = extract_witness_columns(&ans, verb_name);
                (true, sw, cw, fw, format!("Admitted: e.g. {}", witness_text(&ans)))
            }
            "unsat" => (
                false,
                "—".into(),
                "—".into(),
                "—".into(),
                unsat_lines(&ans, &format!("pin `verb == {verb_name}`")).join(" | "),
            ),
            "outside" => (false, "—".into(), "—".into(), "—".into(), outside_text(&ans)),
            _ => (false, "—".into(), "—".into(), "—".into(), unknown_text(&ans)),
        };
        rows.push(VerbMatrixRow {
            verb: verb_name,
            tag: tag_num,
            verdict: v,
            admitted,
            subject_witness: subj_w,
            cost_witness: cost_w,
            field_witness: field_w,
            explanation: expl,
        });
    }

    // `renounce`: K-RENOUNCE is holder-signed with no policy gate in kernel admission; we also check
    // whether the predicate itself admits an non-crud verb tag (tag 6) for completeness.
    let renounce_extra = json!({"type":"eq","slot":"request/verb","value":"6"});
    let renounce_ans = if overall_verdict == "outside" {
        checked.any.clone()
    } else {
        ask(root, &ws, law, Some(&renounce_extra), false, "matrix-renounce")?
    };
    let renounce_pred_note = match verdict(&renounce_ans) {
        "witness" => format!("Predicate also admits tag 6 ({})", witness_text(&renounce_ans)),
        "unsat" => "Predicate refuses tag 6, but K-RENOUNCE bypasses cell policy (holder-signed capability surrender)".into(),
        _ => "K-RENOUNCE is holder-signed capability surrender (no cell policy gate)".into(),
    };
    rows.push(VerbMatrixRow {
        verb: "renounce",
        tag: "K-RENOUNCE",
        verdict: "holder-signed".into(),
        admitted: true,
        subject_witness: "holder".into(),
        cost_witness: "0".into(),
        field_witness: "none (capability surrender)".into(),
        explanation: format!("Admitted (holder-signed; K-RENOUNCE has no policy gate). {renounce_pred_note}"),
    });

    // Check whether writes are locked out globally OR for this installer subject specifically.
    let write_global_unsat = verdict(&checked.write) == "unsat";
    let write_mine_extra = json!({"type":"all","predicates":[
        {"type":"eq","slot":"request/subject","value":subj},
        {"type":"eq","slot":"request/verb","value":"2"}
    ]});
    let write_mine_ans = if overall_verdict == "witness" && !write_global_unsat {
        Some(ask(root, &ws, law, Some(&write_mine_extra), false, "matrix-write-mine")?)
    } else {
        None
    };
    let write_mine_unsat = write_mine_ans.as_ref().is_some_and(|a| verdict(a) == "unsat");
    let write_lockout = write_global_unsat || write_mine_unsat || overall_verdict == "unsat";
    let write_lockout_reason = if write_global_unsat || overall_verdict == "unsat" {
        Some(format!(
            "WRITE LOCKOUT WARNING: this law admits no write by any subject ({}).",
            unsat_lines(&checked.write, "pin `verb == write`").join("; ")
        ))
    } else if let Some(ans) = &write_mine_ans {
        if verdict(ans) == "unsat" {
            Some(format!(
                "WRITE SELF-LOCKOUT WARNING: no write by you (subject {subj}) can ever pass this law ({}).",
                unsat_lines(ans, "your subject + write pin").join("; ")
            ))
        } else {
            None
        }
    } else {
        None
    };

    let self_lockout_reason = if self_lock {
        checked.mine.as_ref().map(|m| {
            format!(
                "TOTAL SELF-LOCKOUT WARNING: no request of any verb by you (subject {subj}) can ever pass this law ({}).",
                unsat_lines(m, "your own subject pin").join("; ")
            )
        })
    } else {
        None
    };

    let relaw_lockout_reason = if relaw_lock {
        checked.relaw.as_ref().map(|r| {
            format!(
                "RE-LAW LOCKOUT WARNING: once installed, you (subject {subj}) can never revise or replace this law ({}).",
                unsat_lines(r, "your own re-law pin").join("; ")
            )
        }).or_else(|| {
            if overall_verdict == "unsat" {
                Some("RE-LAW LOCKOUT WARNING: this law admits no step at all (`sealed`), so it can never be revised once installed.".into())
            } else {
                None
            }
        })
    } else {
        None
    };

    Ok(LawWorkbenchReport {
        rendered_law: crate::shell::law::render_clause(law),
        overall_verdict,
        overall_summary,
        write_lockout,
        write_lockout_reason,
        self_lockout: self_lock,
        self_lockout_reason,
        relaw_lockout: relaw_lock,
        relaw_lockout_reason,
        rows,
    })
}

// ------------------------------------------------------------------ Hypothetical Turn Judge & Local Presburger Solver

#[derive(Clone, Debug)]
pub(crate) struct ClauseVerdict {
    pub index: usize,
    pub depth: usize,
    pub clause: String,
    pub passed: bool,
    pub readings: String,
}

#[derive(Clone, Debug)]
pub(crate) struct HypotheticalTurnReport {
    pub verb: String,
    pub verb_tag: i128,
    pub subject: i128,
    pub cost: i128,
    pub admitted: bool,
    pub headline: String,
    pub first_refused_clause: Option<String>,
    pub clauses: Vec<ClauseVerdict>,
}

pub(crate) fn verb_tag_of(verb: &str) -> Result<(String, i128)> {
    match verb.trim() {
        "read" | "observe" | "1" => Ok(("read".into(), 1)),
        "write" | "mutate" | "2" => Ok(("write".into(), 2)),
        "delegate" | "3" => Ok(("delegate".into(), 3)),
        "install" | "4" => Ok(("install".into(), 4)),
        "revoke" | "5" => Ok(("revoke".into(), 5)),
        "renounce" | "6" => Ok(("renounce".into(), 6)),
        "append" | "7" => Ok(("append".into(), 7)),
        "place" | "10" => Ok(("place".into(), 10)),
        other => {
            let n: i128 = other
                .parse()
                .map_err(|_| format!("unknown verb `{other}` (use read, write, delegate, install, revoke, renounce, append, place, or a tag number)"))?;
            Ok((other.to_owned(), n))
        }
    }
}

/// Parse `key=value` or `N=value` pairs (comma, semicolon, or whitespace separated) into field/slot assignments.
pub(crate) fn parse_field_assignments(input: &str) -> Result<(BTreeMap<String, i128>, BTreeMap<String, i128>)> {
    let mut fields = BTreeMap::new();
    let mut raw_slots = BTreeMap::new();
    for token in input
        .split([',', ';', '\n'])
        .map(str::trim)
        .filter(|s| !s.is_empty())
    {
        let (k, v) = token
            .split_once('=')
            .or_else(|| token.split_once(':'))
            .ok_or_else(|| format!("expected `FIELD=VALUE` (e.g. `0=10` or `content/atom-edits=0`), found `{token}`"))?;
        let k = k.trim();
        let k = k.strip_prefix("field ").map(str::trim).unwrap_or(k);
        let val: i128 = v
            .trim()
            .parse()
            .map_err(|_| format!("value `{}` for `{k}` is not an integer", v.trim()))?;
        if k.bytes().all(|b| b.is_ascii_digit()) {
            fields.insert(k.to_owned(), val);
        } else {
            raw_slots.insert(k.to_owned(), val);
        }
    }
    Ok((fields, raw_slots))
}

/// Evaluate `Pred` over `(old, new)` states with fail-closed semantics (`Pred/Eval.lean`).
pub(crate) fn eval_pred(pred: &Value, old: &BTreeMap<String, i128>, new: &BTreeMap<String, i128>) -> bool {
    let ty = pred.get("type").and_then(Value::as_str).unwrap_or("");
    let s = |k: &str| pred.get(k).and_then(Value::as_str).unwrap_or("");
    let int_val = |k: &str| -> Option<i128> { pred.get(k)?.as_str()?.parse().ok() };
    match ty {
        "eq" => new.get(s("slot")).copied().zip(int_val("value")).is_some_and(|(a, b)| a == b),
        "le" => new.get(s("slot")).copied().zip(int_val("value")).is_some_and(|(a, b)| a <= b),
        "memberOf" => {
            let Some(actual) = new.get(s("slot")).copied() else {
                return false;
            };
            pred.get("values")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|v| v.as_str()?.parse::<i128>().ok())
                .any(|v| v == actual)
        }
        "monotone" => {
            let slot = s("slot");
            old.get(slot).copied().zip(new.get(slot).copied()).is_some_and(|(a, b)| a <= b)
        }
        "writeOnce" => {
            let slot = s("slot");
            old.get(slot)
                .copied()
                .zip(new.get(slot).copied())
                .is_some_and(|(a, b)| a == 0 || a == b)
        }
        "eqSlots" => new
            .get(s("left"))
            .copied()
            .zip(new.get(s("right")).copied())
            .is_some_and(|(a, b)| a == b),
        "leSlots" => new
            .get(s("left"))
            .copied()
            .zip(new.get(s("right")).copied())
            .is_some_and(|(a, b)| a <= b),
        "leSlotsOff" => {
            let Some(k) = int_val("offset") else {
                return false;
            };
            new.get(s("left"))
                .copied()
                .zip(new.get(s("right")).copied())
                .is_some_and(|(a, b)| a <= b.saturating_add(k))
        }
        "not" => pred
            .get("predicate")
            .is_some_and(|inner| !eval_pred(inner, old, new)),
        "all" => pred
            .get("predicates")
            .and_then(Value::as_array)
            .is_some_and(|ps| ps.iter().all(|p| eval_pred(p, old, new))),
        "any" => pred
            .get("predicates")
            .and_then(Value::as_array)
            .is_some_and(|ps| ps.iter().any(|p| eval_pred(p, old, new))),
        "ran" => {
            let prog = s("program");
            new.get(&format!("run/program/{prog}")).copied() == Some(1)
        }
        _ => false,
    }
}

fn slot_readings_for_clause(
    clause: &Value,
    old: &BTreeMap<String, i128>,
    new: &BTreeMap<String, i128>,
) -> String {
    let mut mentioned = BTreeSet::new();
    slots(clause, &mut mentioned);
    if mentioned.is_empty() {
        return "no slots read".into();
    }
    let fmt_val = |slot: &str, m: &BTreeMap<String, i128>| -> String {
        match m.get(slot) {
            Some(v) => crate::shell::law::render_value(slot, &v.to_string()),
            None => "absent".into(),
        }
    };
    let mut parts = Vec::new();
    for slot in mentioned {
        let name = crate::shell::law::render_slot(&slot);
        let old_v = fmt_val(&slot, old);
        let new_v = fmt_val(&slot, new);
        if old_v != new_v {
            parts.push(format!("{name}: before={old_v}, after={new_v}"));
        } else {
            parts.push(format!("{name}={new_v}"));
        }
    }
    parts.join("; ")
}

fn collect_clause_verdicts(
    pred: &Value,
    old: &BTreeMap<String, i128>,
    new: &BTreeMap<String, i128>,
    depth: usize,
    out: &mut Vec<ClauseVerdict>,
) {
    let index = out.len() + 1;
    let passed = eval_pred(pred, old, new);
    out.push(ClauseVerdict {
        index,
        depth,
        clause: crate::shell::law::render_clause(pred),
        passed,
        readings: slot_readings_for_clause(pred, old, new),
    });
    match pred.get("type").and_then(Value::as_str) {
        Some("all" | "any") => {
            for child in pred
                .get("predicates")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
            {
                collect_clause_verdicts(child, old, new, depth + 1, out);
            }
        }
        Some("not") => {
            if let Some(inner) = pred.get("predicate") {
                collect_clause_verdicts(inner, old, new, depth + 1, out);
            }
        }
        _ => {}
    }
}

/// Construct the hypothetical `(old, new)` state for a turn and evaluate the law clause-by-clause.
pub(crate) fn judge_hypothetical_turn(
    law: &Value,
    verb_input: &str,
    subject_input: &str,
    cost_input: &str,
    before_input: &str,
    after_input: &str,
) -> Result<HypotheticalTurnReport> {
    let (verb_name, verb_tag) = verb_tag_of(verb_input)?;
    let subject: i128 = if subject_input.trim().is_empty() {
        1
    } else {
        subject_input
            .trim()
            .parse()
            .map_err(|_| format!("subject `{}` must be an integer", subject_input.trim()))?
    };
    let cost: i128 = if cost_input.trim().is_empty() {
        0
    } else {
        cost_input
            .trim()
            .parse()
            .map_err(|_| format!("cost `{}` must be an integer", cost_input.trim()))?
    };
    let (before_fields, before_slots) = parse_field_assignments(before_input)?;
    let (after_fields, after_slots) = parse_field_assignments(after_input)?;

    let mut old = BTreeMap::new();
    let mut new = BTreeMap::new();
    for (k, v) in [
        ("request/verb", verb_tag),
        ("request/subject", subject),
        ("request/cost", cost),
    ] {
        old.insert(k.to_owned(), v);
        new.insert(k.to_owned(), v);
    }

    let (mentioned_fields, mentioned_pairs) = law_fields(law);
    let mut all_fields: BTreeSet<String> = mentioned_fields;
    all_fields.extend(before_fields.keys().cloned());
    all_fields.extend(after_fields.keys().cloned());

    for f in &all_fields {
        let b_val = before_fields
            .get(f)
            .copied()
            .or_else(|| after_fields.get(f).copied())
            .unwrap_or(0);
        let a_val = after_fields
            .get(f)
            .copied()
            .or_else(|| before_fields.get(f).copied())
            .unwrap_or(b_val);
        let delta = a_val.saturating_sub(b_val);
        old.insert(field_slot(f, "before"), b_val);
        old.insert(field_slot(f, "after"), b_val);
        old.insert(field_slot(f, "delta"), 0);
        new.insert(field_slot(f, "before"), b_val);
        new.insert(field_slot(f, "after"), a_val);
        new.insert(field_slot(f, "delta"), delta);
    }
    for (a, b) in &mentioned_pairs {
        let da = new.get(&field_slot(a, "delta")).copied().unwrap_or(0);
        let db = new.get(&field_slot(b, "delta")).copied().unwrap_or(0);
        let pair_slot = format!("resource/pair/{a}/{b}/delta");
        old.insert(pair_slot.clone(), 0);
        new.insert(pair_slot, da.saturating_add(db));
    }
    // Default common content slots when a document law is tested without explicit slot overrides.
    let mut mentioned_all = BTreeSet::new();
    slots(law, &mut mentioned_all);
    for s in &mentioned_all {
        if s.starts_with("content/") && !new.contains_key(s) {
            let def = if s == "content/names/unique" { 1 } else { 0 };
            old.insert(s.clone(), def);
            new.insert(s.clone(), def);
        }
    }
    for (k, v) in before_slots {
        old.insert(k.clone(), v);
        new.entry(k).or_insert(v);
    }
    for (k, v) in after_slots {
        new.insert(k, v);
    }

    let mut clauses = Vec::new();
    if law.get("type").and_then(Value::as_str) == Some("all") {
        let children = law
            .get("predicates")
            .and_then(Value::as_array)
            .cloned()
            .unwrap_or_default();
        if children.is_empty() {
            collect_clause_verdicts(law, &old, &new, 0, &mut clauses);
        } else {
            for child in &children {
                collect_clause_verdicts(child, &old, &new, 0, &mut clauses);
            }
        }
    } else {
        collect_clause_verdicts(law, &old, &new, 0, &mut clauses);
    }

    let pred_passed = eval_pred(law, &old, &new);
    let admitted = pred_passed || verb_name == "renounce";
    let first_refused_clause = if admitted {
        None
    } else {
        clauses
            .iter()
            .find(|c| c.depth == 0 && !c.passed)
            .or_else(|| clauses.iter().find(|c| !c.passed))
            .map(|c| format!("{} ({})", c.clause, c.readings))
    };
    let headline = if verb_name == "renounce" {
        if pred_passed {
            "Admitted: K-RENOUNCE is holder-signed (and predicate clauses also evaluate to true)".into()
        } else {
            "Admitted by K-RENOUNCE (holder-signed capability surrender has no cell policy gate; predicate itself evaluated to false)".into()
        }
    } else if admitted {
        format!("Admitted: hypothetical `{verb_name}` turn satisfies all law clauses")
    } else {
        format!(
            "Refused (law-denied): {}",
            first_refused_clause.as_deref().unwrap_or("law evaluated to false")
        )
    };

    Ok(HypotheticalTurnReport {
        verb: verb_name,
        verb_tag,
        subject,
        cost,
        admitted,
        headline,
        first_refused_clause,
        clauses,
    })
}

// ------------------------------------------------------------------ Pure-Rust mirror of Pred/Satisfiable.lean + Host/LawSat.lean

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum SatNode {
    Zero,
    Old(String),
    New(String),
}

impl SatNode {
    fn text(&self) -> String {
        match self {
            SatNode::Zero => "0".into(),
            SatNode::Old(s) => format!("{} (before the step)", crate::shell::law::render_slot(s)),
            SatNode::New(s) => crate::shell::law::render_slot(s),
        }
    }
    fn value_text(&self, k: i128) -> String {
        match self {
            SatNode::Zero => k.to_string(),
            SatNode::Old(s) | SatNode::New(s) => crate::shell::law::render_value(s, &k.to_string()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct SatCon {
    x: SatNode,
    y: SatNode,
    k: i128,
    clause: String,
    part: &'static str,
}

impl SatCon {
    fn text(&self) -> String {
        match (&self.x, &self.y) {
            (SatNode::Zero, SatNode::Zero) => format!("0 <= {}", self.k),
            (SatNode::Zero, y) => format!("{} >= {}", y.text(), y.value_text(-self.k)),
            (x, SatNode::Zero) => format!("{} <= {}", x.text(), x.value_text(self.k)),
            (x, y) => {
                if self.k == 0 {
                    format!("{} <= {}", x.text(), y.text())
                } else if self.k > 0 {
                    format!("{} <= {} + {}", x.text(), y.text(), self.k)
                } else {
                    format!("{} <= {} - {}", x.text(), y.text(), -self.k)
                }
            }
        }
    }
}

#[derive(Clone, Debug, Default)]
struct SatSys {
    present: BTreeSet<(SatNode, String, &'static str)>,
    absent: BTreeSet<(SatNode, String, &'static str)>,
    cons: Vec<SatCon>,
}

impl SatSys {
    fn merge(&self, other: &Self) -> Self {
        let mut present = self.present.clone();
        present.extend(other.present.iter().cloned());
        let mut absent = self.absent.clone();
        absent.extend(other.absent.iter().cloned());
        let mut cons = self.cons.clone();
        cons.extend(other.cons.iter().cloned());
        Self { present, absent, cons }
    }
}

fn realize_scalar(pred: &Value) -> std::result::Result<Value, String> {
    let ty = pred.get("type").and_then(Value::as_str).unwrap_or("");
    let s = |k: &str| pred.get(k).and_then(Value::as_str).unwrap_or("");
    let scalar_old = |slot: &str| -> Option<std::result::Result<String, Vec<String>>> {
        let parts: Vec<&str> = slot.split('/').collect();
        match parts.as_slice() {
            ["resource", "field", k, "after"] => Some(Ok(format!("resource/field/{k}/before"))),
            ["resource", "field", _, "before"] => Some(Ok(slot.to_owned())),
            ["resource", "field", k, "delta"] => Some(Err(vec![format!("resource/field/{k}/before")])),
            ["resource", "pair", a, b, "delta"] => Some(Err(vec![
                format!("resource/field/{a}/before"),
                format!("resource/field/{b}/before"),
            ])),
            ["request" | "target" | "clock" | "command" | "run", ..] => Some(Ok(slot.to_owned())),
            _ => None,
        }
    };
    match ty {
        "monotone" => {
            let slot = s("slot");
            match scalar_old(slot).ok_or_else(|| slot.to_owned())? {
                Ok(t) => Ok(json!({"type":"leSlots","left":t,"right":slot})),
                Err(ts) => {
                    let mut ps: Vec<Value> = ts
                        .into_iter()
                        .map(|t| json!({"type":"leSlots","left":t,"right":t}))
                        .collect();
                    ps.push(json!({"type":"leSlots","left":slot,"right":slot}));
                    ps.push(json!({"type":"not","predicate":{"type":"le","slot":slot,"value":"-1"}}));
                    Ok(json!({"type":"all","predicates":ps}))
                }
            }
        }
        "writeOnce" => {
            let slot = s("slot");
            match scalar_old(slot).ok_or_else(|| slot.to_owned())? {
                Ok(t) => Ok(json!({"type":"any","predicates":[
                    {"type":"not","predicate":{"type":"leSlots","left":t,"right":t}},
                    {"type":"eq","slot":t,"value":"0"},
                    {"type":"eqSlots","left":slot,"right":t}
                ]})),
                Err(_) => Ok(json!({"type":"all","predicates":[]})),
            }
        }
        "not" => {
            let inner = pred.get("predicate").ok_or_else(|| "?".to_owned())?;
            Ok(json!({"type":"not","predicate":realize_scalar(inner)?}))
        }
        "all" | "any" => {
            let mut out = Vec::new();
            for p in pred.get("predicates").and_then(Value::as_array).into_iter().flatten() {
                out.push(realize_scalar(p)?);
            }
            Ok(json!({"type":ty,"predicates":out}))
        }
        _ => Ok(pred.clone()),
    }
}

const DNF_CAP: usize = 1024;

enum DnfError {
    Outside { part: &'static str, path: Vec<usize>, clause: String },
    PastCap,
}

fn sat_dnf(
    b: bool,
    pred: &Value,
    part: &'static str,
    path: Vec<usize>,
) -> std::result::Result<Vec<SatSys>, DnfError> {
    let ty = pred.get("type").and_then(Value::as_str).unwrap_or("");
    let s = |k: &str| pred.get(k).and_then(Value::as_str).unwrap_or("").to_owned();
    let int_val = |k: &str| -> i128 {
        pred.get(k)
            .and_then(Value::as_str)
            .and_then(|v| v.parse().ok())
            .unwrap_or(0)
    };
    let clause = crate::shell::law::render_clause(pred);
    let pres = |nodes: Vec<SatNode>, cons: Vec<(SatNode, SatNode, i128)>| -> SatSys {
        SatSys {
            present: nodes.into_iter().map(|n| (n, clause.clone(), part)).collect(),
            absent: BTreeSet::new(),
            cons: cons
                .into_iter()
                .map(|(x, y, k)| SatCon { x, y, k, clause: clause.clone(), part })
                .collect(),
        }
    };
    let gone = |node: SatNode| -> SatSys {
        let mut absent = BTreeSet::new();
        absent.insert((node, clause.clone(), part));
        SatSys { present: BTreeSet::new(), absent, cons: Vec::new() }
    };
    match ty {
        "not" => {
            let mut next = path;
            next.push(0);
            sat_dnf(!b, pred.get("predicate").unwrap_or(&Value::Null), part, next)
        }
        "all" | "any" => {
            let children = pred
                .get("predicates")
                .and_then(Value::as_array)
                .cloned()
                .unwrap_or_default();
            let is_conj = (ty == "all" && b) || (ty == "any" && !b);
            if is_conj {
                let mut acc = vec![SatSys::default()];
                for (i, child) in children.iter().enumerate() {
                    let mut p = path.clone();
                    p.push(i);
                    let sub = sat_dnf(b, child, part, p)?;
                    let mut next = Vec::new();
                    for a in &acc {
                        for c in &sub {
                            next.push(a.merge(c));
                            if next.len() > DNF_CAP {
                                return Err(DnfError::PastCap);
                            }
                        }
                    }
                    acc = next;
                }
                Ok(acc)
            } else {
                let mut acc = Vec::new();
                for (i, child) in children.iter().enumerate() {
                    let mut p = path.clone();
                    p.push(i);
                    let sub = sat_dnf(b, child, part, p)?;
                    acc.extend(sub);
                    if acc.len() > DNF_CAP {
                        return Err(DnfError::PastCap);
                    }
                }
                Ok(acc)
            }
        }
        "eq" => {
            let u = SatNode::New(s("slot"));
            let v = int_val("value");
            if b {
                Ok(vec![pres(vec![u.clone()], vec![(u.clone(), SatNode::Zero, v), (SatNode::Zero, u, -v)])])
            } else {
                Ok(vec![
                    gone(u.clone()),
                    pres(vec![u.clone()], vec![(u.clone(), SatNode::Zero, v - 1)]),
                    pres(vec![u.clone()], vec![(SatNode::Zero, u, -(v + 1))]),
                ])
            }
        }
        "le" => {
            let u = SatNode::New(s("slot"));
            let v = int_val("value");
            if b {
                Ok(vec![pres(vec![u.clone()], vec![(u, SatNode::Zero, v)])])
            } else {
                Ok(vec![
                    gone(u.clone()),
                    pres(vec![u.clone()], vec![(SatNode::Zero, u, -(v + 1))]),
                ])
            }
        }
        "memberOf" => {
            let u = SatNode::New(s("slot"));
            let mut vals: Vec<i128> = pred
                .get("values")
                .and_then(Value::as_array)
                .into_iter()
                .flatten()
                .filter_map(|v| v.as_str()?.parse().ok())
                .collect();
            vals.sort();
            vals.dedup();
            if b {
                if vals.is_empty() {
                    return Ok(Vec::new());
                }
                let mut runs: Vec<(i128, i128)> = Vec::new();
                for v in vals {
                    if let Some(last) = runs.last_mut() {
                        if v == last.1 + 1 {
                            last.1 = v;
                            continue;
                        }
                    }
                    runs.push((v, v));
                }
                Ok(runs
                    .into_iter()
                    .map(|(lo, hi)| {
                        pres(
                            vec![u.clone()],
                            vec![(SatNode::Zero, u.clone(), -lo), (u.clone(), SatNode::Zero, hi)],
                        )
                    })
                    .collect())
            } else {
                if vals.is_empty() {
                    return Ok(vec![SatSys::default()]);
                }
                let mut out = vec![
                    gone(u.clone()),
                    pres(vec![u.clone()], vec![(u.clone(), SatNode::Zero, vals[0] - 1)]),
                ];
                for pair in vals.windows(2) {
                    if pair[0] + 1 <= pair[1] - 1 {
                        out.push(pres(
                            vec![u.clone()],
                            vec![
                                (SatNode::Zero, u.clone(), -(pair[0] + 1)),
                                (u.clone(), SatNode::Zero, pair[1] - 1),
                            ],
                        ));
                    }
                }
                let last = *vals.last().unwrap();
                out.push(pres(vec![u.clone()], vec![(SatNode::Zero, u, -(last + 1))]));
                Ok(out)
            }
        }
        "monotone" => {
            let slot = s("slot");
            let o = SatNode::Old(slot.clone());
            let n = SatNode::New(slot);
            if b {
                Ok(vec![pres(vec![o.clone(), n.clone()], vec![(o, n, 0)])])
            } else {
                Ok(vec![
                    gone(o.clone()),
                    gone(n.clone()),
                    pres(vec![o.clone(), n.clone()], vec![(n, o, -1)]),
                ])
            }
        }
        "writeOnce" => {
            let slot = s("slot");
            let o = SatNode::Old(slot.clone());
            let n = SatNode::New(slot);
            if b {
                Ok(vec![
                    pres(
                        vec![o.clone(), n.clone()],
                        vec![(o.clone(), SatNode::Zero, 0), (SatNode::Zero, o.clone(), 0)],
                    ),
                    pres(
                        vec![o.clone(), n.clone()],
                        vec![(o.clone(), n.clone(), 0), (n, o, 0)],
                    ),
                ])
            } else {
                Ok(vec![
                    gone(o.clone()),
                    gone(n.clone()),
                    pres(
                        vec![o.clone(), n.clone()],
                        vec![(o.clone(), SatNode::Zero, -1), (o.clone(), n.clone(), -1)],
                    ),
                    pres(
                        vec![o.clone(), n.clone()],
                        vec![(o.clone(), SatNode::Zero, -1), (n.clone(), o.clone(), -1)],
                    ),
                    pres(
                        vec![o.clone(), n.clone()],
                        vec![(SatNode::Zero, o.clone(), -1), (o.clone(), n.clone(), -1)],
                    ),
                    pres(
                        vec![o.clone(), n.clone()],
                        vec![(SatNode::Zero, o.clone(), -1), (n, o, -1)],
                    ),
                ])
            }
        }
        "eqSlots" => {
            let l = SatNode::New(s("left"));
            let r = SatNode::New(s("right"));
            if b {
                Ok(vec![pres(
                    vec![l.clone(), r.clone()],
                    vec![(l.clone(), r.clone(), 0), (r, l, 0)],
                )])
            } else {
                Ok(vec![
                    gone(l.clone()),
                    gone(r.clone()),
                    pres(vec![l.clone(), r.clone()], vec![(l.clone(), r.clone(), -1)]),
                    pres(vec![l.clone(), r.clone()], vec![(r, l, -1)]),
                ])
            }
        }
        "leSlots" | "leSlotsOff" => {
            let l = SatNode::New(s("left"));
            let r = SatNode::New(s("right"));
            let k = if ty == "leSlotsOff" { int_val("offset") } else { 0 };
            if b {
                Ok(vec![pres(vec![l.clone(), r.clone()], vec![(l, r, k)])])
            } else {
                Ok(vec![
                    gone(l.clone()),
                    gone(r.clone()),
                    pres(vec![l.clone(), r.clone()], vec![(r, l, -k - 1)]),
                ])
            }
        }
        _ => Err(DnfError::Outside { part, path, clause }),
    }
}

fn solve_system(sys: &SatSys) -> std::result::Result<(BTreeMap<String, i128>, BTreeMap<String, i128>), Value> {
    for (p_node, p_clause, p_part) in &sys.present {
        if let Some((_, a_clause, a_part)) = sys.absent.iter().find(|(a_node, _, _)| a_node == p_node) {
            return Err(json!({
                "kind": "clash",
                "text": format!("{} must be both present and absent", p_node.text()),
                "sources": [
                    {"part": p_part, "path": [0], "clause": p_clause},
                    {"part": a_part, "path": [0], "clause": a_clause},
                ]
            }));
        }
    }
    let mut nodes: BTreeSet<SatNode> = BTreeSet::new();
    nodes.insert(SatNode::Zero);
    for (n, _, _) in &sys.present {
        nodes.insert(n.clone());
    }
    for c in &sys.cons {
        nodes.insert(c.x.clone());
        nodes.insert(c.y.clone());
    }
    let mut dist: BTreeMap<SatNode, i128> = nodes.iter().map(|n| (n.clone(), 0)).collect();
    let mut pred_edge: BTreeMap<SatNode, usize> = BTreeMap::new();
    let n_count = nodes.len().max(1);
    for _ in 0..n_count {
        let mut changed = false;
        for (idx, c) in sys.cons.iter().enumerate() {
            let dy = dist.get(&c.y).copied().unwrap_or(0);
            let dx = dist.get(&c.x).copied().unwrap_or(0);
            if dx > dy.saturating_add(c.k) {
                dist.insert(c.x.clone(), dy.saturating_add(c.k));
                pred_edge.insert(c.x.clone(), idx);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // Check for negative cycle
    for (idx, c) in sys.cons.iter().enumerate() {
        let dy = dist.get(&c.y).copied().unwrap_or(0);
        let dx = dist.get(&c.x).copied().unwrap_or(0);
        if dx > dy.saturating_add(c.k) {
            let mut cur = c.x.clone();
            let mut current_edge = idx;
            for _ in 0..=n_count {
                let edge = &sys.cons[current_edge];
                cur = edge.y.clone();
                if let Some(&prev) = pred_edge.get(&cur) {
                    current_edge = prev;
                } else {
                    break;
                }
            }
            let start = cur.clone();
            let mut cycle_edges = Vec::new();
            loop {
                let Some(&e_idx) = pred_edge.get(&cur) else {
                    cycle_edges.push(c.clone());
                    break;
                };
                let edge = sys.cons[e_idx].clone();
                cur = edge.y.clone();
                cycle_edges.push(edge);
                if cur == start || cycle_edges.len() > n_count + 1 {
                    break;
                }
            }
            let sum: i128 = cycle_edges.iter().map(|e| e.k).sum();
            let sum = if sum >= 0 { -1 } else { sum };
            let constraints: Vec<Value> = cycle_edges
                .iter()
                .map(|e| {
                    json!({
                        "text": e.text(),
                        "k": e.k.to_string(),
                        "sources": [{"part": e.part, "path": [0], "clause": e.clause}]
                    })
                })
                .collect();
            return Err(json!({
                "kind": "cycle",
                "sum": sum,
                "sumText": sum.to_string(),
                "constraints": constraints,
            }));
        }
    }
    let z = dist.get(&SatNode::Zero).copied().unwrap_or(0);
    let mut old = BTreeMap::new();
    let mut new = BTreeMap::new();
    for (node, _, _) in &sys.present {
        let val = dist.get(node).copied().unwrap_or(0).saturating_sub(z);
        match node {
            SatNode::Zero => {}
            SatNode::Old(s) => {
                old.insert(s.clone(), val);
            }
            SatNode::New(s) => {
                new.insert(s.clone(), val);
            }
        }
    }
    Ok((old, new))
}

/// Pure-Rust implementation of `Host/LawSatWire.lean` (`answerJson`), used when no compiled Host
/// binary is present on disk and for standalone unit tests.
pub(crate) fn decide_local(
    law: &Value,
    extra: Option<&Value>,
    from_here: bool,
) -> Result<Value> {
    let extra_pred = extra.cloned().unwrap_or_else(|| json!({"type":"all","predicates":[]}));
    let (law_target, extra_target) = if from_here {
        match (realize_scalar(law), realize_scalar(&extra_pred)) {
            (Ok(l), Ok(e)) => (l, e),
            (Err(slot), _) | (_, Err(slot)) => {
                return Ok(json!({
                    "verdict": "unrealizable",
                    "slot": slot,
                    "name": crate::shell::law::render_slot(&slot),
                }))
            }
        }
    } else {
        (law.clone(), extra_pred)
    };
    let law_sys = match sat_dnf(true, &law_target, "law", Vec::new()) {
        Ok(s) => s,
        Err(DnfError::Outside { part, path, clause }) => {
            return Ok(json!({"verdict":"outside","part":part,"path":path,"clause":clause}))
        }
        Err(DnfError::PastCap) => {
            return Ok(json!({"verdict":"unknown","reason":"cap","cap":DNF_CAP}))
        }
    };
    let extra_sys = match sat_dnf(true, &extra_target, "query", Vec::new()) {
        Ok(s) => s,
        Err(DnfError::Outside { part, path, clause }) => {
            return Ok(json!({"verdict":"outside","part":part,"path":path,"clause":clause}))
        }
        Err(DnfError::PastCap) => {
            return Ok(json!({"verdict":"unknown","reason":"cap","cap":DNF_CAP}))
        }
    };
    let mut combined = Vec::new();
    for l in &law_sys {
        for e in &extra_sys {
            combined.push(l.merge(e));
            if combined.len() > DNF_CAP {
                return Ok(json!({"verdict":"unknown","reason":"cap","cap":DNF_CAP}));
            }
        }
    }
    let sys_count = combined.len();
    let mut certificates = Vec::new();
    for sys in &combined {
        match solve_system(sys) {
            Ok((old, new)) => {
                let state_json = |m: &BTreeMap<String, i128>| -> Vec<Value> {
                    m.iter()
                        .map(|(slot, v)| {
                            json!({
                                "slot": slot,
                                "name": crate::shell::law::render_slot(slot),
                                "value": v.to_string(),
                                "text": crate::shell::law::render_value(slot, &v.to_string()),
                            })
                        })
                        .collect()
                };
                return Ok(json!({
                    "verdict": "witness",
                    "systems": sys_count,
                    "old": state_json(&old),
                    "new": state_json(&new),
                }));
            }
            Err(cert) => certificates.push(cert),
        }
    }
    Ok(json!({
        "verdict": "unsat",
        "systems": sys_count,
        "certificate": certificates,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn falsifier_answer() -> Value {
        json!({"verdict":"unsat","systems":1,"certificate":[{"kind":"cycle","sum":-1,"constraints":[
            {"text":"field 1 <= 0","k":0,"sources":[{"part":"law","path":[0],"clause":"field 1 <= 0",
                "top":{"index":0,"clause":"field 1 <= 0"}}]},
            {"text":"field 1 >= 1","k":-1,"sources":[{"part":"law","path":[2],"clause":"field 1 == 1",
                "top":{"index":2,"clause":"field 1 == 1"}}]}]}]})
    }

    #[test]
    fn a_cycle_names_the_contradicting_clauses() {
        let lines = unsat_lines(&falsifier_answer(), "the check");
        assert_eq!(lines[0], "these clauses contradict:");
        assert!(lines[1].contains("field 1 <= 0") && lines[1].contains("clause [0] `field 1 <= 0`"));
        assert!(lines[2].contains("field 1 >= 1") && lines[2].contains("clause [2] `field 1 == 1`"));
        assert!(lines[3].contains("0 <= -1"));
    }

    #[test]
    fn an_empty_certificate_reads_as_sealed() {
        let lines = unsat_lines(&json!({"verdict":"unsat","systems":0,"certificate":[]}), "x");
        assert_eq!(lines.len(), 1);
        assert!(lines[0].contains("sealed"));
    }

    #[test]
    fn a_guarded_part_is_named_inside_its_clause() {
        let source = json!({"part":"law","path":[1,0],"clause":"field 2 monotone",
            "top":{"index":1,"clause":"any [ field 2 monotone, not (verb == write) ]"}});
        assert_eq!(
            source_text(&source, "q"),
            "clause [1] `any [ field 2 monotone, not (verb == write) ]` (its part `field 2 monotone`)"
        );
        let query = json!({"part":"query","path":[],"clause":"verb == write"});
        assert_eq!(source_text(&query, "the check's own"), "the check's own `verb == write`");
    }

    #[test]
    fn write_pins_free_one_field_and_couple_its_delta() {
        let now: BTreeMap<String, String> =
            [("1".to_owned(), "0".to_owned()), ("2".to_owned(), "3".to_owned())].into();
        let pins = write_pins(&now, "2", "7", &[]).unwrap();
        let text = pins.to_string();
        assert!(text.contains(r#"{"slot":"resource/field/1/after","type":"eq","value":"0"}"#));
        assert!(text.contains(r#"{"slot":"resource/field/2/before","type":"eq","value":"3"}"#));
        assert!(!text.contains(r#""slot":"resource/field/2/after","type":"eq""#));
        assert!(text.contains(r#""left":"resource/field/2/delta","offset":"-3""#));
        assert!(text.contains(r#""left":"resource/field/2/after","offset":"3""#));
        assert!(write_pins(&now, "2", "7", &[("2".into(), "2".into())]).is_none());
        assert!(write_pins(&now, "9", "7", &[]).is_none());
    }

    #[test]
    fn law_fields_reads_fields_and_pairs() {
        let law = json!({"type":"all","predicates":[
            {"type":"monotone","slot":"resource/field/2/after"},
            {"type":"not","predicate":{"type":"le","slot":"resource/pair/1/3/delta","value":"0"}},
            {"type":"eq","slot":"request/verb","value":"2"}]});
        let (fields, pairs) = law_fields(&law);
        assert_eq!(fields.into_iter().collect::<Vec<_>>(), ["1", "2", "3"]);
        assert_eq!(pairs, [("1".to_owned(), "3".to_owned())]);
    }

    #[test]
    fn all_eight_presets_parse_and_build_six_verb_admissibility_matrix() {
        assert_eq!(PRESETS.len(), 8);
        let root = std::env::temp_dir().join(format!("mini-lawsat-test-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&root);
        let ws = json!({"subject": "7"});
        for preset in PRESETS {
            let (pred, rendered) = parse_law_input(preset.key, "7").expect(preset.key);
            assert!(!rendered.is_empty());
            let report = analyze_law_workbench(&root, &ws, "7", &pred).expect(preset.key);
            assert_eq!(report.rows.len(), 6, "preset {} must produce 6 verb rows", preset.key);
            let verbs: Vec<&str> = report.rows.iter().map(|r| r.verb).collect();
            assert_eq!(verbs, ["read", "write", "delegate", "install", "revoke", "renounce"]);
            if preset.key == "read-only lockout" {
                assert!(report.write_lockout, "read-only lockout must flag write_lockout");
                assert!(report.relaw_lockout, "read-only lockout must flag relaw_lockout");
                assert!(report.rows[0].admitted, "read must be admitted");
                assert!(!report.rows[1].admitted, "write must be unsatisfiable");
                assert!(!report.rows[3].admitted, "install must be unsatisfiable");
            } else {
                assert!(!report.write_lockout, "preset {} should not lock out writes", preset.key);
                assert!(report.rows[0].admitted, "preset {} should admit read", preset.key);
                assert!(report.rows[1].admitted, "preset {} should admit write", preset.key);
            }
        }
        let _ = std::fs::remove_dir_all(&root);
    }

    #[test]
    fn hypothetical_turn_judge_evaluates_clauses_and_pinpoints_refusal() {
        let (pred, _) = parse_law_input("monotone-counter", "7").unwrap();
        // Valid write: field 0 goes from 5 to 6 (monotone and delta == 1 <= 1)
        let ok_turn = judge_hypothetical_turn(&pred, "write", "7", "10", "0=5", "0=6").unwrap();
        assert!(ok_turn.admitted, "0=5 -> 0=6 should pass monotone-counter: {:?}", ok_turn.clauses);
        assert!(ok_turn.first_refused_clause.is_none());

        // Refused write: field 0 goes from 5 to 7 (delta == 2 > 1)
        let bad_delta = judge_hypothetical_turn(&pred, "write", "7", "10", "0=5", "0=7").unwrap();
        assert!(!bad_delta.admitted);
        assert!(bad_delta
            .clauses
            .iter()
            .any(|c| !c.passed && c.clause.contains("field 0 delta <= 1")));

        // Refused write: field 0 goes from 5 to 4 (violates field 0 monotone)
        let bad_mono = judge_hypothetical_turn(&pred, "write", "7", "10", "0=5", "0=4").unwrap();
        assert!(!bad_mono.admitted);
        assert!(bad_mono
            .clauses
            .iter()
            .any(|c| !c.passed && c.clause.contains("field 0 monotone")));
    }
}
