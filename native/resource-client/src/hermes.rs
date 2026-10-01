//! Hermes in a room (PLACE §2.7, §2.10, §5 row 7): `summon ROOM as ROLE
//! --budget N`, `ask ROOM TEXT`, `dismiss ROOM`.
//!
//! Hermes is a participant like any friend: an enrolled subject `H` that holds
//! only what it is given and pays for its turns from an account. `summon` is
//! the founder's verb, because everything it hands out is the founder's to
//! hand out:
//!
//! 1. the room's till `ROOM-till` (born, founder-owned, when the room has none):
//!    Hermes's turns pay `tariff.hermes/turn` into it;
//! 2. Hermes's budget account `ROOM-hermes` (`A_P`), owned by `H` and funded
//!    with N from the founder's own account at its birth (a posting: the
//!    founder's balance moves by N plus the birth fee);
//! 3. Hermes on the roster, exactly as `chat invite` puts a friend there: a
//!    grant under the room (the role's verbs), Hermes's own stream born `--in`
//!    the room under Hermes's author law, the roster row;
//! 4. the role's documents (`grants.json` `docs`): born when absent, or given
//!    the role's law when present (a `law` install by their owner), and
//!    delegated to `H` with the role's verbs;
//! 5. the role's program as a DOCUMENT in the room (`ROOM-hermes-ROLE`): the
//!    template text with the room's names filled in, one append; every member
//!    reads it (it is under the room) and only the founder writes it;
//! 6. the room cell's fields `hermes` (= H) and `hermes/account` (= A_P), so
//!    any member's `ask` finds Hermes from a signed read of the room;
//! 7. the hand-off for Hermes's controller in `HOME/outbox/H/`: the account
//!    handoff, the invitation, the delegated references and `summon-ROOM.json`.
//!
//! `ask ROOM TEXT` is `say --to H` in the room. `dismiss ROOM` revokes the
//! room grant and every role delegation this founder made to H (the
//! founder's own revocations; holder renunciation is K-RENOUNCE, another
//! branch), zeroes the room's `hermes` fields and leaves a `dismiss-ROOM.json`
//! naming the founder's account: the budget account is Hermes's own, so the
//! remainder comes back as a transfer Hermes's controller signs on its next
//! attach. Nothing here is admission: the Host judges every grant, birth,
//! install and write; what a role "may" do is exactly the grants it holds.
use crate::chat::{self, Done};
use crate::shell::Session;
use crate::workspace::{self, member};
use serde_json::{json, Value};
use std::fs;
use std::path::{Path, PathBuf};

/// The role templates, compiled in (the files are the roles).
const LIBRARIAN_GRANTS: &str = include_str!("../../../deploy/shell/templates/hermes/librarian/grants.json");
const LIBRARIAN_PROGRAM: &str = include_str!("../../../deploy/shell/templates/hermes/librarian/program.md");
const LIBRARIAN_BUDGET: &str = include_str!("../../../deploy/shell/templates/hermes/librarian/budget.json");
const RUNNER_GRANTS: &str = include_str!("../../../deploy/shell/templates/hermes/runner/grants.json");
const RUNNER_BUDGET: &str = include_str!("../../../deploy/shell/templates/hermes/runner/budget.json");

/// Where the node's Hermes subject is written by the operator (once per node:
/// enrolling the hosted Hermes key is the operator's, PLACE §6.1). `--hermes
/// SUBJECT` overrides it.
pub(crate) const NODE_FILE: &str = "hermes/node.json";

pub(crate) const VERBS: &[crate::shell::Verb] = &[
    crate::shell::Verb { name: "summon", usage: "summon ROOM as librarian|runner [--budget N] [--every N] [--program @FILE] [--hermes SUBJECT] [--i-know]", operation: "founder: the till (if none), Hermes's budget account funded N from mine, Hermes on the roster (chat invite), the role's documents and grants, the program document ROOM-hermes-ROLE, the room's hermes fields, the hand-off in HOME/outbox/H" },
    crate::shell::Verb { name: "ask", usage: "ask [ROOM] TEXT", operation: "say --to HERMES in the room (Hermes is the room cell's `hermes` field, a signed read)" },
    crate::shell::Verb { name: "dismiss", usage: "dismiss ROOM", operation: "founder: revoke the room grant and the role's delegations to Hermes, zero the room's hermes fields, ask Hermes to return the unspent budget (HOME/outbox/H/dismiss-ROOM.json)" },
];

#[derive(Debug, PartialEq, Clone)]
pub(crate) enum Line {
    Summon {
        room: String,
        role: String,
        budget: Option<String>,
        every: Option<String>,
        program: Option<String>,
        hermes: Option<String>,
        i_know: bool,
    },
    Ask { room: Option<String>, text: String },
    Dismiss { room: String },
}

/// Map `summon`/`ask`/`dismiss` lines; `None` for any other verb.
pub(crate) fn plan(verb: &str, rest: &str) -> Option<Result<Line, String>> {
    let usage = |name: &str| VERBS.iter().find(|v| v.name == name).map(|v| v.usage).unwrap_or("").to_owned();
    Some(match verb {
        "summon" => parse_summon(rest).map_err(|e| if e.is_empty() { usage("summon") } else { e }),
        "ask" => {
            let (first, after) = match chat::split(rest) {
                Some(pair) => pair,
                None => return Some(Err(usage("ask"))),
            };
            // `ask ROOM TEXT` when the first word is a room this session
            // holds; otherwise the whole line is the text, in the current room.
            Ok(if crate::chat::ref_name(first, "room").is_ok() && !chat::free_text(after).is_empty() {
                Line::Ask { room: Some(first.to_owned()), text: chat::free_text(after) }
            } else {
                Line::Ask { room: None, text: chat::free_text(rest) }
            })
        }
        "dismiss" => {
            let words: Vec<&str> = rest.split_whitespace().collect();
            match words.as_slice() {
                [room] => chat::ref_name(room, "room name").map(|()| Line::Dismiss { room: (*room).to_owned() }),
                _ => Err(usage("dismiss")),
            }
        }
        _ => return None,
    })
}

fn parse_summon(rest: &str) -> Result<Line, String> {
    let words: Vec<&str> = rest.split_whitespace().collect();
    let (room, role, options) = match words.as_slice() {
        [room, "as", role, options @ ..] => (*room, *role, options),
        _ => return Err(String::new()),
    };
    chat::ref_name(room, "room name")?;
    if !matches!(role, "librarian" | "gm" | "runner") {
        return Err("the roles are librarian, gm and runner".into());
    }
    let (mut budget, mut every, mut program, mut hermes, mut i_know) = (None, None, None, None, false);
    let mut i = 0;
    while i < options.len() {
        let value = || options.get(i + 1).map(|v| (*v).to_owned()).ok_or_else(|| format!("{} needs a value", options[i]));
        match options[i] {
            "--budget" => {
                let v = value()?;
                chat::decimal(&v, "--budget")?;
                budget = Some(v);
                i += 1;
            }
            "--every" => {
                let v = value()?;
                chat::decimal(&v, "--every")?;
                every = Some(v);
                i += 1;
            }
            "--hermes" => {
                let v = value()?;
                chat::decimal(&v, "--hermes")?;
                hermes = Some(v);
                i += 1;
            }
            "--program" => {
                let v = value()?;
                let file = v.strip_prefix('@').ok_or("--program takes @FILE (a plain name in HOME/requests)")?;
                if file.is_empty() || file.contains('/') || file.starts_with('.') {
                    return Err("--program takes @FILE (a plain name in HOME/requests)".into());
                }
                program = Some(file.to_owned());
                i += 1;
            }
            "--i-know" => i_know = true,
            _ => return Err(String::new()),
        }
        i += 1;
    }
    Ok(Line::Summon { room: room.to_owned(), role: role.to_owned(), budget, every, program, hermes, i_know })
}

pub(crate) fn run(session: &Session, line: Line) -> Result<(), Done> {
    match line {
        Line::Summon { room, role, budget, every, program, hermes, i_know } => {
            summon(session, &room, &role, budget, every, program, hermes, i_know)
        }
        Line::Ask { room, text } => ask(session, room, text),
        Line::Dismiss { room } => dismiss(session, &room),
    }
}

// ---------------------------------------------------------------- templates

/// One role's template, parsed from its `grants.json` and `budget.json`.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Role {
    pub name: String,
    /// Verbs of Hermes's grant under the room (the roster grant).
    pub room_verbs: Vec<String>,
    /// Documents the role writes: name pattern, verbs, law (the shell's
    /// one-line grammar, `{FOUNDER}`/`{H}` filled in).
    pub docs: Vec<RoleDoc>,
    pub program_name: String,
    pub program_law: String,
    pub fund: String,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RoleDoc {
    pub name: String,
    pub verbs: Vec<String>,
    pub law: Option<String>,
}

fn strings(value: &Value, key: &str) -> Result<Vec<String>, String> {
    value
        .get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| format!("role template: {key} absent"))?
        .iter()
        .map(|v| v.as_str().map(str::to_owned).ok_or_else(|| format!("role template: {key} holds a non-string")))
        .collect()
}

pub(crate) fn role(name: &str) -> Result<Role, String> {
    let (grants, budget) = match name {
        "librarian" => (LIBRARIAN_GRANTS, LIBRARIAN_BUDGET),
        "runner" => (RUNNER_GRANTS, RUNNER_BUDGET),
        "gm" => {
            return Err("summon as gm: the gm role writes a story's state and scene documents, which the story verbs (P-STORY) and MUD-GM own; its template is deploy/shell/templates/hermes/gm, marked for MUD-GM".into())
        }
        _ => return Err(format!("no role {name}")),
    };
    let grants: Value = serde_json::from_str(grants).map_err(|e| format!("role template {name}: {e}"))?;
    let budget: Value = serde_json::from_str(budget).map_err(|e| format!("role budget {name}: {e}"))?;
    if grants.get("type").and_then(Value::as_str) != Some("mini-hermes-role-grants-v2") {
        return Err(format!("role template {name} is not mini-hermes-role-grants-v2"));
    }
    let mut docs = Vec::new();
    for doc in grants.get("docs").and_then(Value::as_array).into_iter().flatten() {
        docs.push(RoleDoc {
            name: member(doc, "name").map_err(|e| e.to_string())?.to_owned(),
            verbs: strings(doc, "verbs")?,
            law: doc.get("law").and_then(Value::as_str).map(str::to_owned),
        });
    }
    let program = grants.get("program").ok_or("role template: program absent")?;
    Ok(Role {
        name: name.to_owned(),
        room_verbs: strings(&grants, "room")?,
        docs,
        program_name: member(program, "name").map_err(|e| e.to_string())?.to_owned(),
        program_law: member(program, "law").map_err(|e| e.to_string())?.to_owned(),
        fund: member(&budget, "fund").map_err(|e| e.to_string())?.to_owned(),
    })
}

/// Fill a template's `{UPPER}` words.
pub(crate) fn fill(text: &str, values: &[(&str, &str)]) -> String {
    let mut out = text.to_owned();
    for (key, value) in values {
        out = out.replace(&format!("{{{key}}}"), value);
    }
    out
}

/// A runner's program names its cells on two lines (`runner/program.md`):
/// `- **Inputs** (read, never write): a, b` and `- **Outputs** …: c`.
pub(crate) fn runner_cells(program: &str) -> Result<(Vec<String>, Vec<String>), String> {
    let list = |label: &str| -> Vec<String> {
        program
            .lines()
            .find(|line| line.trim_start().starts_with(&format!("- **{label}**")))
            .and_then(|line| line.split_once(':').map(|(_, cells)| cells))
            .map(|cells| cells.split(',').map(|c| c.trim().trim_matches('`').to_owned()).filter(|c| !c.is_empty()).collect())
            .unwrap_or_default()
    };
    let (inputs, outputs) = (list("Inputs"), list("Outputs"));
    if outputs.is_empty() {
        return Err("a runner's program names its outputs (`- **Outputs** …: CELL, …`); a runner with no outputs is not summoned".into());
    }
    for cell in inputs.iter().chain(&outputs) {
        chat::ref_name(cell, "a program's cell name")?;
    }
    Ok((inputs, outputs))
}

// ---------------------------------------------------------------- summon

fn err(message: impl std::fmt::Display) -> Done {
    (crate::shell::EXIT_CLIENT, format!("error: {message}\n"))
}

fn usage(message: impl Into<String>) -> Done {
    (crate::shell::EXIT_USAGE, format!("usage: {}\n", message.into()))
}

/// The summon's resumable state (`HOME/hermes/ROOM.json`): the steps done.
fn state_path(session: &Session, room: &str) -> PathBuf {
    session.home.join("hermes").join(format!("{room}.json"))
}

fn outbox(session: &Session, hermes: &str) -> PathBuf {
    session.home.join("outbox").join(hermes)
}

fn put(path: &Path, value: &Value) -> Result<(), Done> {
    chat::put_json(path, value).map_err(err)
}

/// The node's Hermes subject: `--hermes`, else `HOME/hermes/node.json`.
fn hermes_subject(session: &Session, explicit: Option<String>) -> Result<String, Done> {
    if let Some(subject) = explicit {
        return Ok(subject);
    }
    let path = session.home.join(NODE_FILE);
    let value = chat::get_json(&path).ok_or_else(|| {
        err(format!("this node names no Hermes ({} is absent; the operator enrolls the node's Hermes and writes it there), or pass --hermes SUBJECT", path.display()))
    })?;
    let subject = member(&value, "subject").map_err(err)?.to_owned();
    chat::decimal(&subject, "the node's Hermes subject").map_err(err)?;
    Ok(subject)
}

/// Is this room private? PRIVACY B6: a hosted Hermes in a private room makes
/// the room readable on the box, so `summon` refuses without `--i-know`.
/// SEAM: private rooms (`room new --private`, the room key) are on branch
/// `priv-rooms`; this base has no private flag, so no room is private here.
fn room_is_private(_session: &Session, _room: &str) -> bool {
    false
}

fn propose_submit(session: &Session, prefix: &str, request: &Value) -> Result<Value, Done> {
    chat::propose_submit(session, prefix, request)
}

/// Delegate `verbs` on reference `name` to `recipient`, publish it, and return
/// the recipient reference (what Hermes imports).
fn delegate(session: &Session, name: &str, recipient: &str, verbs: &[String]) -> Result<Value, Done> {
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate","name":name,
        "recipient":recipient,"verbs":verbs,"maxCost":"50000"});
    let done = propose_submit(session, "hermes-grant", &request)?;
    let id = done["id"].as_str().unwrap_or_default().to_owned();
    let ws = &session.workspace;
    chat::client(
        "workspace",
        &[
            ("action", chat::os("publish-delegation")),
            ("dir", chat::os(ws)),
            ("proposal-id", chat::os(&id)),
            ("attempt", chat::os(ws.join("attempts").join(&id))),
        ],
    )?;
    chat::get_json(&ws.join("proposals").join(&id).join("recipient-reference.json"))
        .ok_or_else(|| err("the published delegation left no recipient-reference.json"))
}

fn law_of(text: &str) -> Result<Value, Done> {
    crate::shell::law::parse(text).map_err(|e| err(format!("role law: {e}")))
}

/// Give document `name` (held by this workspace) the law `law`: born `--in
/// ROOM` when absent, else installed over its current law by its owner.
fn ensure_doc(session: &Session, room: &str, name: &str, law: &Value) -> Result<&'static str, Done> {
    if chat::reference(session, name).is_err() {
        chat::create_cell(session, name, "content", law, Some(room), None)?;
        return Ok("born");
    }
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":name,"predicate":law});
    propose_submit(session, "hermes-law", &request)?;
    Ok("law installed")
}

/// One document append, proposed and submitted.
fn append_doc(session: &Session, name: &str, text: &str) -> Result<Value, Done> {
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"document","actions":[{"type":"append","text":text}]}}]});
    propose_submit(session, "hermes-program", &request)
}

fn target(session: &Session, name: &str) -> Result<String, Done> {
    let reference = chat::reference(session, name).map_err(err)?;
    Ok(member(&reference, "target").map_err(err)?.to_owned())
}

#[allow(clippy::too_many_arguments)]
fn summon(
    session: &Session,
    room: &str,
    role_name: &str,
    budget: Option<String>,
    every: Option<String>,
    program_file: Option<String>,
    hermes: Option<String>,
    i_know: bool,
) -> Result<(), Done> {
    let role = role(role_name).map_err(|e| (crate::shell::EXIT_CLIENT, format!("not here: {e}\n")))?;
    let me = chat::me(session)?;
    let chat_room = chat::load_room(session, room).map_err(err)?;
    let record = chat::get_json(&session.home.join("chat").join("rooms").join(format!("{room}.json"))).unwrap_or_default();
    if record.get("founder").and_then(Value::as_str) != Some(me.as_str()) {
        return Err(usage(format!(
            "only the founder of {room} summons Hermes: its grants, its documents' laws and the room's hermes fields are the founder's"
        )));
    }
    crate::shell::hosted_private_invite(room_is_private(session, room), true, i_know).map_err(usage)?;
    let h = hermes_subject(session, hermes)?;
    let root = session.workspace.clone();
    let ws = workspace::load(&root).map_err(err)?;
    let fund = budget.unwrap_or_else(|| role.fund.clone());
    let every = every.unwrap_or_else(|| "3".into());
    let state_file = state_path(session, room);
    let mut state = chat::get_json(&state_file).unwrap_or_else(|| json!({"type":"mini-hermes-summon-state-v1","room":room,"steps":{}}));
    if let Some(prior) = state.get("hermes").and_then(Value::as_str) {
        if prior != h || state.get("role").and_then(Value::as_str) != Some(role_name) {
            return Err(usage(format!("{room} already has Hermes {prior} as {}; dismiss it first", state["role"].as_str().unwrap_or("?"))));
        }
    }
    if state["steps"].get("dismissed").is_some() {
        return Err(usage(format!("Hermes was dismissed from {room}; a new summon starts from a fresh room record (remove {})", state_file.display())));
    }
    state["hermes"] = json!(h);
    state["role"] = json!(role_name);
    let done = |state: &Value, step: &str| state["steps"].get(step).is_some();
    let out = outbox(session, &h);
    let mut tariff = crate::credit::room(&root, &ws, room).map_err(err)?;
    // 1. the till
    if tariff.fields.get("till").is_none() {
        let permit = root.join("sources").join("credit-permit-all.json");
        crate::credit::write_permit(&permit).map_err(err)?;
        let till_name = format!("{room}-till");
        if chat::reference(session, &till_name).is_err() {
            workspace::create(&root, &ws, &till_name, "declared", &permit, None, "account", None, None, None).map_err(err)?;
        }
        let till = target(session, &till_name)?;
        crate::credit::set_fields(&root, &ws, room, &tariff, &[("till", till.clone())]).map_err(err)?;
        println!("{room}: born its till {till_name} ({till}); Hermes's turns pay into it");
        tariff = crate::credit::room(&root, &ws, room).map_err(err)?;
    }
    let turn = tariff.fields.get("hermes/turn").cloned().unwrap_or_else(|| "0".into());
    // 2. the budget account
    let account_name = format!("{room}-hermes");
    if !done(&state, "account") {
        let handoff = workspace::create_funded_account(&root, &ws, &account_name, &json!({"type":"all","predicates":[]}), &h, &fund)
            .map_err(err)?;
        put(&out.join(format!("{account_name}.json")), &handoff)?;
        state["steps"]["account"] = json!(member(&handoff, "target").map_err(err)?);
        put(&state_file, &state)?;
        println!("{room}: Hermes's account {account_name} ({}) holds {fund}, from your account", state["steps"]["account"].as_str().unwrap_or(""));
    }
    let account = state["steps"]["account"].as_str().unwrap_or_default().to_owned();
    // 3. Hermes on the roster
    if !done(&state, "invite") {
        let invited = chat::invite(session, room, &h, Some("hermes"), &role.room_verbs)?;
        put(&out.join(format!("{room}-invite.json")), &invited.invitation)?;
        state["steps"]["invite"] = json!(invited.stream);
        put(&state_file, &state)?;
        println!("{room}: Hermes is on the roster (grant {} under {room}; its stream {})", role.room_verbs.join(","), invited.stream);
    }
    // 4. the role's documents and grants
    let mut docs: Vec<RoleDoc> = role.docs.clone();
    let mut program_text = match role_name {
        "librarian" => LIBRARIAN_PROGRAM.to_owned(),
        _ => {
            let file = program_file.ok_or_else(|| usage("summon ROOM as runner --program @FILE: the program names its inputs, outputs and task"))?;
            let path = session.home.join("requests").join(&file);
            fs::read_to_string(&path).map_err(|e| err(format!("cannot read {}: {e}", path.display())))?
        }
    };
    if role_name == "runner" {
        let (inputs, outputs) = runner_cells(&program_text).map_err(usage)?;
        for cell in outputs {
            docs.push(RoleDoc { name: cell, verbs: vec!["observe".into(), "mutate".into()], law: None });
        }
        for cell in inputs {
            docs.push(RoleDoc { name: cell, verbs: vec!["observe".into()], law: None });
        }
    }
    let values = [("ROOM", room), ("FOUNDER", me.as_str()), ("H", h.as_str())];
    let mut granted = Vec::new();
    for doc in &docs {
        let name = fill(&doc.name, &values);
        let key = format!("doc:{name}");
        if !done(&state, &key) {
            if let Some(law) = &doc.law {
                let how = ensure_doc(session, room, &name, &law_of(&fill(law, &values))?)?;
                println!("{room}: {name} {how} (its law admits you and Hermes)");
            }
            let reference = delegate(session, &name, &h, &doc.verbs)?;
            put(&out.join(format!("{name}.json")), &reference)?;
            state["steps"][&key] = json!(target(session, &name)?);
            put(&state_file, &state)?;
            println!("{room}: Hermes holds {} on {name}", doc.verbs.join(","));
        }
        granted.push(json!({"name":name,"target":state["steps"][&key],"verbs":doc.verbs}));
    }
    // 5. the program document
    let program_name = fill(&role.program_name, &values);
    program_text = fill(
        &program_text,
        &[
            ("ROOM", room),
            ("H", h.as_str()),
            ("ACCOUNT", account_name.as_str()),
            ("N", every.as_str()),
            ("P", "hermes"),
        ],
    );
    if !done(&state, "program") {
        if chat::reference(session, &program_name).is_err() {
            chat::create_cell(session, &program_name, "content", &law_of(&fill(&role.program_law, &values))?, Some(room), None)?;
        }
        append_doc(session, &program_name, program_text.trim_end())?;
        state["steps"]["program"] = json!(target(session, &program_name)?);
        put(&state_file, &state)?;
        println!("{room}: the program is the document {program_name} (members read it; you edit it)");
    }
    // 6. the room's hermes fields
    if !done(&state, "fields") {
        let current = crate::credit::room(&root, &ws, room).map_err(err)?;
        crate::credit::set_fields(&root, &ws, room, &current, &[("hermes", h.clone()), ("hermes/account", account.clone())]).map_err(err)?;
        state["steps"]["fields"] = json!(true);
        put(&state_file, &state)?;
    }
    // 7. the hand-off for Hermes's controller
    let my_account = crate::credit::my_account(&root, &ws, None).map_err(err)?;
    let founder_account = target(session, &my_account)?;
    let manifest = json!({"type":"mini-hermes-summon-v1","room":room,"roomCell":target(session, &chat_room.name)?,
        "role":role_name,"hermes":h,"founder":me,"founderAccount":founder_account,
        "account":{"name":account_name,"target":account},"stream":state["steps"]["invite"],
        "program":{"name":program_name,"target":state["steps"]["program"]},"docs":granted,
        "every":every,"tariff":{"hermes/turn":turn,"till":tariff.fields.get("till")},
        "authority":"hint-only: every use is a signed request the Host judges"});
    put(&out.join(format!("summon-{room}.json")), &manifest)?;
    state["manifest"] = manifest.clone();
    put(&state_file, &state)?;
    println!(
        "summoned Hermes ({h}) into {room} as {role_name}: budget {fund} in {account_name}, {turn} a turn into the till; hand-off in {}",
        out.display()
    );
    Ok(())
}

// ---------------------------------------------------------------- ask, dismiss

/// Hermes in `room`, from a signed read of the room cell's `hermes` field.
fn room_hermes(session: &Session, room: &str) -> Result<Option<String>, Done> {
    let root = session.workspace.clone();
    let ws = workspace::load(&root).map_err(err)?;
    let current = crate::credit::room(&root, &ws, room).map_err(err)?;
    Ok(current.fields.get("hermes").filter(|h| h.as_str() != "0").cloned())
}

fn ask(session: &Session, room: Option<String>, text: String) -> Result<(), Done> {
    let room = match room {
        Some(room) => room,
        None => chat::current_room(session).map_err(err)?.name,
    };
    let h = room_hermes(session, &room)?.ok_or_else(|| usage(format!("there is no Hermes in {room} (its founder summons one)")))?;
    let line = chat::Line::Say { room: Some(room), to: Some(h), re: None, text: chat::Text::Inline(text), via: None };
    match chat::run(session, line) {
        (0, _) => Ok(()),
        done => Err(done),
    }
}

fn dismiss(session: &Session, room: &str) -> Result<(), Done> {
    let me = chat::me(session)?;
    let state_file = state_path(session, room);
    let mut state = chat::get_json(&state_file).ok_or_else(|| usage(format!("you did not summon Hermes into {room}")))?;
    if state["steps"].get("dismissed").is_some() {
        return Err(usage(format!("Hermes was already dismissed from {room}")));
    }
    let h = state["hermes"].as_str().ok_or_else(|| err("the summon record names no Hermes"))?.to_owned();
    let mut revoked = Vec::new();
    let mut names = vec![room.to_owned()];
    for doc in state["manifest"]["docs"].as_array().into_iter().flatten() {
        if let Some(name) = doc["name"].as_str() {
            names.push(name.to_owned());
        }
    }
    for name in names {
        let key = format!("revoked:{name}");
        if state["steps"].get(&key).is_none() {
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"revoke","name":name,"recipient":h});
            let done = propose_submit(session, "hermes-revoke", &request)?;
            state["steps"][&key] = done["outcome"]["transactionId"].clone();
            put(&state_file, &state)?;
        }
        revoked.push(name);
    }
    let root = session.workspace.clone();
    let ws = workspace::load(&root).map_err(err)?;
    let current = crate::credit::room(&root, &ws, room).map_err(err)?;
    crate::credit::set_fields(&root, &ws, room, &current, &[("hermes", "0".into()), ("hermes/account", "0".into())]).map_err(err)?;
    let notice = json!({"type":"mini-hermes-dismiss-v1","room":room,"hermes":h,"founder":me,
        "returnTo":state["manifest"]["founderAccount"],"account":state["manifest"]["account"],
        "revoked":revoked});
    put(&outbox(session, &h).join(format!("dismiss-{room}.json")), &notice)?;
    state["steps"]["dismissed"] = json!(true);
    put(&state_file, &state)?;
    println!(
        "dismissed Hermes ({h}) from {room}: revoked its grants on {}; its stream and history stay; it returns the unspent budget to your account {} on its next attach",
        revoked.join(", "),
        state["manifest"]["founderAccount"].as_str().unwrap_or("?")
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hermes_lines_parse() {
        assert_eq!(
            plan("summon", " lab as librarian --budget 100").unwrap().unwrap(),
            Line::Summon { room: "lab".into(), role: "librarian".into(), budget: Some("100".into()), every: None, program: None, hermes: None, i_know: false }
        );
        assert_eq!(
            plan("summon", " lab as runner --program @prog.md --hermes 42 --i-know").unwrap().unwrap(),
            Line::Summon { room: "lab".into(), role: "runner".into(), budget: None, every: None, program: Some("prog.md".into()), hermes: Some("42".into()), i_know: true }
        );
        assert!(plan("summon", " lab librarian").unwrap().is_err());
        assert!(plan("summon", " lab as poet").unwrap().is_err());
        assert!(plan("summon", " lab as librarian --budget lots").unwrap().is_err());
        assert!(plan("summon", " lab as runner --program prog.md").unwrap().is_err());
        assert_eq!(
            plan("ask", " lab what changed since 12").unwrap().unwrap(),
            Line::Ask { room: Some("lab".into()), text: "what changed since 12".into() }
        );
        assert_eq!(plan("ask", " hello?").unwrap().unwrap(), Line::Ask { room: None, text: "hello?".into() });
        assert_eq!(plan("dismiss", " lab").unwrap().unwrap(), Line::Dismiss { room: "lab".into() });
        assert!(plan("dismiss", " lab now").unwrap().is_err());
        assert!(plan("tail", "").is_none());
    }

    #[test]
    fn role_templates_parse_and_their_laws_compile() {
        let librarian = role("librarian").unwrap();
        assert_eq!(librarian.room_verbs, vec!["observe", "append"]);
        let names: Vec<_> = librarian.docs.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["{ROOM}-index", "{ROOM}-digest"]);
        for doc in &librarian.docs {
            assert_eq!(doc.verbs, vec!["observe", "mutate"]);
            let law = fill(doc.law.as_ref().unwrap(), &[("FOUNDER", "7"), ("H", "42")]);
            assert!(crate::shell::law::parse(&law).is_ok(), "{law}");
        }
        assert!(crate::shell::law::parse(&fill(&librarian.program_law, &[("FOUNDER", "7")])).is_ok());
        assert_eq!(librarian.fund, "100");
        let runner = role("runner").unwrap();
        assert!(runner.docs.is_empty());
        assert!(role("gm").unwrap_err().contains("MUD-GM"));
    }

    #[test]
    fn a_librarian_holds_no_verb_that_bears_or_grants() {
        // The librarian reads the room and speaks on its own stream; it
        // writes only its two documents. No place, no delegate, anywhere.
        let librarian = role("librarian").unwrap();
        for verb in librarian.room_verbs.iter().chain(librarian.docs.iter().flat_map(|d| d.verbs.iter())) {
            assert!(matches!(verb.as_str(), "observe" | "append" | "mutate"), "{verb}");
        }
        assert!(!librarian.room_verbs.iter().any(|v| v == "mutate"));
    }

    #[test]
    fn the_program_template_fills_every_placeholder() {
        let text = fill(LIBRARIAN_PROGRAM, &[("ROOM", "lab"), ("H", "42"), ("ACCOUNT", "lab-hermes"), ("N", "3"), ("P", "hermes")]);
        assert!(!text.contains('{'), "unfilled placeholder in the librarian program");
        assert!(text.contains("lab-index") && text.contains("lab-digest"));
    }

    #[test]
    fn a_runner_program_names_inputs_and_outputs() {
        let program = "- **Inputs** (read, never write): lab-data, lab-paper\n- **Outputs** (the only cells you write): lab-summary\n";
        assert_eq!(runner_cells(program).unwrap(), (vec!["lab-data".into(), "lab-paper".into()], vec!["lab-summary".into()]));
        assert!(runner_cells("- **Inputs** (read): a\n").is_err());
        assert!(runner_cells("- **Outputs** (write): bad/name\n").is_err());
    }
}
