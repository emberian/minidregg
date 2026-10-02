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
    private_file(
        &input,
        &serde_json::to_vec(&request).map_err(|error| error.to_string())?,
    )?;
    host_law_sat(
        &member_path(workspace, "host")?,
        &member_path(workspace, "config")?,
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
        println!("  a write exists in principle (e.g. {}), but this cell holds no field to write; create one first", witness_text(&write));
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
}
