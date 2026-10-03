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

/// Legacy operator record, used only when no resident registry is advertised.
/// Current selection is scoped to the actual source room cell.
pub(crate) const NODE_FILE: &str = "hermes/node.json";

pub(crate) const VERBS: &[crate::shell::Verb] = &[
    crate::shell::Verb { name: "summon", usage: "summon ROOM as librarian|runner [--budget N] [--every N] [--program @FILE] [--hermes SUBJECT] [--i-know]", operation: "founder: the till (if none), Hermes's budget account funded N from mine, Hermes on the roster (chat invite), the role's documents and grants, the program document ROOM-hermes-ROLE, the room's hermes fields, the hand-off in HOME/outbox/H" },
    crate::shell::Verb { name: "ask", usage: "ask [ROOM] TEXT", operation: "say --to HERMES in the room (Hermes is the room cell's `hermes` field, a signed read)" },
    crate::shell::Verb { name: "hermes", usage: "hermes status [ROOM] | hermes cancel N [ROOM]", operation: "status: a signed read of the room's streams; each of my requests to Hermes with Hermes's latest typed status for it | cancel: append {\"type\":\"withdraw\"} replying to my request #N, addressed to Hermes (it cancels the request only while it is still queued)" },
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
    Status { room: Option<String> },
    Cancel { room: Option<String>, number: u64 },
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
        "hermes" => {
            let words: Vec<&str> = rest.split_whitespace().collect();
            let room = |name: Option<&&str>| -> Result<Option<String>, String> {
                name.map(|n| chat::ref_name(n, "room name").map(|()| (*n).to_owned())).transpose()
            };
            match words.as_slice() {
                ["status", rest @ ..] if rest.len() <= 1 => room(rest.first()).map(|room| Line::Status { room }),
                ["cancel", n, rest @ ..] if rest.len() <= 1 => match n.parse::<u64>() {
                    Ok(number) if number > 0 => room(rest.first()).map(|room| Line::Cancel { room, number }),
                    _ => Err(usage("hermes")),
                },
                _ => Err(usage("hermes")),
            }
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
        Line::Status { room } => status(session, room),
        Line::Cancel { room, number } => cancel(session, room, number),
    }
}

// ---------------------------------------------------------------- status, cancel

/// One of a member's requests to Hermes, as the room's signed streams show it.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct RequestRow {
    /// Feed entry number of the request (`#N` in this read).
    pub number: usize,
    pub cell: String,
    pub sequence: u64,
    pub height: u64,
    /// `unacknowledged` until Hermes publishes a status; then its latest
    /// status, where a terminal status (completed, refused, cancelled) is final.
    pub status: String,
    pub detail: String,
    /// The author appended a `withdraw` for it.
    pub withdrawn: bool,
}

impl RequestRow {
    pub(crate) fn json(&self) -> Value {
        json!({"number":self.number,"cell":self.cell,"sequence":self.sequence,"height":self.height,
            "status":self.status,"detail":self.detail,"withdrawn":self.withdrawn,
            "cancellable":self.cancellable()})
    }
    /// Only a request Hermes has not started may be withdrawn.
    pub(crate) fn cancellable(&self) -> bool {
        !self.withdrawn && matches!(self.status.as_str(), "unacknowledged" | "queued")
    }
}

fn terminal(status: &str) -> bool {
    matches!(status, "completed" | "refused" | "cancelled")
}

/// THE request-status classifier: `hermes status`, `hermes cancel` and the
/// `home` row all use it. Only entries authored by `hermes` count as status;
/// only entries authored by `me` count as requests and withdrawals.
pub(crate) fn request_rows(feed: &chat::Feed, me: &str, hermes: &str) -> Vec<RequestRow> {
    let mut rows: Vec<RequestRow> = feed.feed.iter().enumerate()
        .filter(|(_, e)| e.author == me && e.to.as_deref() == Some(hermes)
            && matches!(chat::kind_of(e), chat::Kind::Say { .. }))
        .map(|(i, e)| RequestRow { number: i + 1, cell: e.cell.clone(), sequence: e.sequence, height: e.height,
            status: "unacknowledged".into(), detail: String::new(), withdrawn: false })
        .collect();
    for e in &feed.feed {
        let Some((cell, sequence)) = &e.re else { continue };
        let Some(row) = rows.iter_mut().find(|r| r.cell == *cell && r.sequence == *sequence) else { continue };
        match chat::kind_of(e) {
            chat::Kind::RequestStatus { status, text } if e.author == hermes && !terminal(&row.status) => {
                row.status = status;
                row.detail = text;
            }
            chat::Kind::Withdraw if e.author == me => row.withdrawn = true,
            _ => {}
        }
    }
    rows
}

fn requests_cache(session: &Session, room: &str) -> PathBuf {
    chat::chat_dir(session).join("rooms").join(format!("{room}.requests.json"))
}

fn room_rows(session: &Session, room: &str) -> Result<(Vec<RequestRow>, Vec<String>), Done> {
    let me = chat::me(session)?;
    let h = room_hermes(session, room)?.ok_or_else(|| usage(format!("there is no Hermes in {room}")))?;
    let (feed, missing) = chat::room_feed(session, room)?;
    let rows = request_rows(&feed, &me, &h);
    // The home row reads this last signed classification (discovery only).
    put(&requests_cache(session, room), &json!({"type":"mini-hermes-request-status-v1","room":room,"hermes":h,
        "height":feed.feed.last().map(|e| e.height),"requests":rows.iter().map(RequestRow::json).collect::<Vec<_>>()}))?;
    Ok((rows, missing))
}

fn status(session: &Session, room: Option<String>) -> Result<(), Done> {
    let room = match room { Some(room) => room, None => chat::current_room(session).map_err(err)?.name };
    let (rows, missing) = room_rows(session, &room)?;
    if rows.is_empty() {
        println!("you have no requests to Hermes in {room}");
    }
    for row in &rows {
        let withdrawn = if row.withdrawn && !terminal(&row.status) { " (withdraw requested)" } else { "" };
        let detail = if row.detail.is_empty() { String::new() } else { format!(": {}", row.detail) };
        println!("#{} {}{withdrawn}{detail}", row.number, row.status);
    }
    for line in missing {
        println!("  (unread: {line})");
    }
    Ok(())
}

fn cancel(session: &Session, room: Option<String>, number: u64) -> Result<(), Done> {
    let room = match room { Some(room) => room, None => chat::current_room(session).map_err(err)?.name };
    let (rows, _) = room_rows(session, &room)?;
    let row = rows.iter().find(|r| r.number as u64 == number)
        .ok_or_else(|| usage(format!("#{number} is not one of your requests to Hermes in {room} (hermes status)")))?;
    if !row.cancellable() {
        return Err(usage(format!("#{number} is {}{}: only a request Hermes has not started can be withdrawn",
            row.status, if row.withdrawn { " and already withdrawn" } else { "" })));
    }
    let h = room_hermes(session, &room)?.ok_or_else(|| usage(format!("there is no Hermes in {room}")))?;
    let result = chat::append_reply(session, &room, json!({"type":"withdraw"}), &h, (row.cell.clone(), row.sequence))?;
    println!("withdraw of #{number} appended ({}); Hermes cancels it if it is still queued",
        result.get("transactionId").and_then(Value::as_str).unwrap_or("submitted"));
    Ok(())
}

/// The `home` row for a room: the last `hermes status` classification this
/// member made, never a claim about the resident's process.
pub(crate) fn home_request_status(chat_home: &Path, room: &str) -> Value {
    let path = chat_home.join("chat").join("rooms").join(format!("{room}.requests.json"));
    match chat::get_json(&path) {
        Some(value) if value["type"] == "mini-hermes-request-status-v1" => json!({
            "status": value["requests"].as_array().and_then(|r| r.last()).map(|r| r["status"].clone()).unwrap_or(json!("none")),
            "requests": value["requests"], "height": value["height"],
            "origin": "last-signed-hermes-status-read", "refresh": format!("hermes status {room}")}),
        _ => json!({"status":"unavailable","refresh":format!("hermes status {room}")}),
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

/// Run `f` with this process's stdout pointed at /dev/null: the in-process
/// client operations summon composes (births, field writes) print their JSON
/// for scripts; a friend's terminal gets summon's own lines instead. Errors
/// still reach stderr.
fn quietly<T>(f: impl FnOnce() -> T) -> T {
    use std::io::Write;
    unsafe extern "C" {
        fn dup(fd: i32) -> i32;
        fn dup2(from: i32, to: i32) -> i32;
        fn close(fd: i32) -> i32;
    }
    let _ = std::io::stdout().flush();
    let null = fs::OpenOptions::new().write(true).open("/dev/null");
    let saved = unsafe { dup(1) };
    let gagged = match (&null, saved >= 0) {
        (Ok(file), true) => {
            use std::os::unix::io::AsRawFd;
            unsafe { dup2(file.as_raw_fd(), 1) >= 0 }
        }
        _ => false,
    };
    let result = f();
    let _ = std::io::stdout().flush();
    if gagged {
        unsafe {
            dup2(saved, 1);
        }
    }
    if saved >= 0 {
        unsafe {
            close(saved);
        }
    }
    result
}

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

/// Resolve one operator-advertised registration before any grants or funding.
/// A display alias is never a custody coordinate; tasks are room-bound.
fn registration(session: &Session, explicit: Option<String>, room_cell: &str) -> Result<Value, Done> {
    let registry = match registry_file(&session.home.join("hermes/registry.json")).map_err(err)? {
        Some(registry) => Some(registry),
        None => registry_file(Path::new("/etc/mini/hermes-residents.json")).map_err(err)?,
    };
    let default = if registry.is_none() { registry_file(&session.home.join(NODE_FILE)).map_err(err)? } else { None };
    select_registration(registry.as_ref(), default.as_ref(), explicit.as_deref(), room_cell).map_err(err)
}

/// Only absence allows fallback. An existing broken advertisement must not
/// silently resurrect another recipient from a legacy operator record.
fn registry_file(path: &Path) -> Result<Option<Value>, String> {
    match fs::symlink_metadata(path) {
        Ok(_) => crate::hermes_handoff::json_file(path).map(Some)
            .map_err(|error| format!("invalid resident registry {}: {error}", path.display())),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(format!("cannot inspect resident registry {}: {error}", path.display())),
    }
}

fn select_registration(
    registry: Option<&Value>, legacy: Option<&Value>, explicit: Option<&str>, room_cell: &str,
) -> Result<Value, String> {
    let records: Vec<&Value> = match registry {
        Some(registry) => {
            if registry["type"] != "mini-hermes-registry-v1" {
                return Err("resident registry type differs".into());
            }
            registry["residents"].as_array().ok_or("resident registry entries absent")?
                .iter().collect()
        }
        None => legacy.into_iter().collect(),
    };
    let matches: Vec<_> = records.into_iter().filter(|v|
        v["roomCell"] == room_cell && explicit.is_none_or(|subject| v["subject"] == subject)
    ).collect();
    if explicit.is_none() && matches.len() > 1 {
        return Err("multiple registered Hermes residents for this room; select --hermes SUBJECT".into());
    }
    let [record] = matches.as_slice() else {
        return Err("Hermes subject and room must select exactly one registered task".into());
    };
    for k in ["subject", "task", "roomCell"] {
        chat::decimal(member(record, k)?, k)?;
    }
    let enc = member(record, "encryptionKey")?;
    if enc.len() != 64 || !enc.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("registered Hermes encryptionKey must be 64 hex digits".into());
    }
    let record = (**record).clone();
    Ok(record)
}
fn room_is_private(session: &Session, room: &str) -> bool {chat::room_is_private(session, room)}

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
    let private = room_is_private(session, room);
    crate::workspace::roomkey::hosted_private_invite(private, true, i_know).map_err(usage)?;
    let room_cell=target(session,&chat_room.name)?;
    let resident=registration(session,hermes,&room_cell)?;
    let h=member(&resident,"subject").map_err(err)?.to_owned();
    let task=member(&resident,"task").map_err(err)?.to_owned();
    let enc=private.then(||resident["encryptionKey"].as_str().unwrap().to_owned());
    let root = session.workspace.clone();
    let ws = workspace::load(&root).map_err(err)?;
    let fund = budget.unwrap_or_else(|| role.fund.clone());
    let every = every.unwrap_or_else(|| "3".into());
    let state_file = state_path(session, &room_cell);
    let mut state = chat::get_json(&state_file).unwrap_or_else(|| json!({"type":"mini-hermes-summon-state-v1","room":room,"steps":{}}));
    if state["steps"].get("dismissed").is_some() {
        let retained=session.home.join("hermes/history").join(format!("room-{room_cell}-assignment-{}.json",state["assignment"].as_str().unwrap_or("0")));
        put(&retained,&state)?;
        state=json!({"type":"mini-hermes-summon-state-v1","room":room,"steps":{}});
    }
    if let Some(prior)=state.get("hermes").and_then(Value::as_str) {
        if prior!=h || state["role"]!=role_name || state["task"]!=task {
            return Err(usage(format!("{room} already has a different registered assignment; dismiss it first")));
        }
    }
    if state["assignment"].is_null() {state["assignment"]=json!(workspace::random_nonce().map_err(err)?);}
    state["roomCell"]=json!(room_cell);state["task"]=json!(task);
    put(&state_file,&state)?;
    state["hermes"] = json!(h);
    state["role"] = json!(role_name);
    let done = |state: &Value, step: &str| state["steps"].get(step).is_some();
    let assignment=state["assignment"].as_str().unwrap().to_owned();
    let out = outbox(session, &h).join(format!("room-{room_cell}")).join(format!("assignment-{assignment}"));
    let mut tariff = quietly(|| crate::credit::room(&root, &ws, room)).map_err(err)?;
    // 1. the till
    if tariff.fields.get("till").is_none() {
        let permit = root.join("sources").join("credit-permit-all.json");
        crate::credit::write_permit(&permit).map_err(err)?;
        let till_name = format!("{room}-till");
        if chat::reference(session, &till_name).is_err() {
            quietly(|| workspace::create(&root, &ws, &till_name, "declared", &permit, None, "account", None, None, None)).map_err(err)?;
        }
        let till = target(session, &till_name)?;
        quietly(|| crate::credit::set_fields(&root, &ws, room, &tariff, &[("till", till.clone())])).map_err(err)?;
        println!("{room}: born its till {till_name} ({till}); Hermes's turns pay into it");
        tariff = quietly(|| crate::credit::room(&root, &ws, room)).map_err(err)?;
    }
    let turn = tariff.fields.get("hermes/turn").cloned().unwrap_or_else(|| "0".into());
    // 2. the budget account
    if state["accountName"].is_null(){state["accountName"]=json!(format!("h-a{assignment}-hermes"));put(&state_file,&state)?;}
    let account_name=state["accountName"].as_str().unwrap().to_owned();
    if !done(&state, "account") {
        let handoff = quietly(|| workspace::create_funded_account(&root, &ws, &account_name, &json!({"type":"all","predicates":[]}), &h, &fund))
            .map_err(err)?;
        put(&out.join(format!("{account_name}.json")), &handoff)?;
        state["steps"]["account"] = json!(member(&handoff, "target").map_err(err)?);
        put(&state_file, &state)?;
        println!("{room}: Hermes's account {account_name} ({}) holds {fund}, from your account", state["steps"]["account"].as_str().unwrap_or(""));
    }
    let account = state["steps"]["account"].as_str().unwrap_or_default().to_owned();
    // 3. Hermes on the roster
    if !done(&state, "invite") {
        let invited = chat::invite(session, room, &h, Some("hermes"), enc.as_deref(), &role.room_verbs)?;
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
            put(&out.join(format!("{}.json",workspace::ref_file(&name))), &reference)?;
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
        let current = quietly(|| crate::credit::room(&root, &ws, room)).map_err(err)?;
        let origin=quietly(|| crate::credit::set_fields_exact(&root,&ws,room,&current,
            &[("hermes",h.clone()),("hermes/account",account.clone()),("hermes/assignment",assignment.clone())],&format!("summon-{assignment}"))).map_err(err)?;
        state["steps"]["fields"] = json!(origin.to_string_lossy());
        put(&state_file, &state)?;
    }
    // 7. the hand-off for Hermes's controller
    let my_account = quietly(|| crate::credit::my_account(&root, &ws, None)).map_err(err)?;
    let founder_account = target(session, &my_account)?;
    let manifest = json!({"type":"mini-hermes-summon-v1","room":room,"roomCell":target(session, &chat_room.name)?,
        "role":role_name,"hermes":h,"task":task,"assignment":assignment,"encryptionKey":resident["encryptionKey"],"founder":me,"founderAccount":founder_account,
        "account":{"name":account_name,"target":account},"stream":state["steps"]["invite"],
        "program":{"name":program_name,"target":state["steps"]["program"]},"docs":granted,
        "every":every,"tariff":{"hermes/turn":turn,"till":tariff.fields.get("till")},
        "authority":"hint-only: every use is a signed request the Host judges"});
    put(&out.join(format!("summon-{room}.json")), &manifest)?;
    let origin=PathBuf::from(state["steps"]["fields"].as_str().ok_or_else(||err("summon origin missing"))?);
    crate::hermes_handoff::seal(&root,&ws,&out,&manifest,&origin,&task).map_err(err)?;
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
    let current = quietly(|| crate::credit::room(&root, &ws, room)).map_err(err)?;
    Ok(current.fields.get("hermes").filter(|h| h.as_str() != "0").cloned())
}

fn ask(session: &Session, room: Option<String>, text: String) -> Result<(), Done> {
    let room = match room {
        Some(room) => room,
        None => chat::current_room(session).map_err(err)?.name,
    };
    let h = room_hermes(session, &room)?.ok_or_else(|| usage(format!("there is no Hermes in {room} (its founder summons one)")))?;
    let line = chat::Line::Say { room: Some(room), to: Some(h), re: None, text: chat::Text::Inline(text), via: None, operation_record: None, expected_reply: None, status: None };
    match chat::run(session, line) {
        (0, _) => Ok(()),
        done => Err(done),
    }
}

fn dismiss(session: &Session, room: &str) -> Result<(), Done> {
    let me = chat::me(session)?;
    let room_cell=target(session,room)?;
    let state_file = state_path(session, &room_cell);
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
    let current = quietly(|| crate::credit::room(&root, &ws, room)).map_err(err)?;
    let assignment=state["assignment"].as_str().ok_or_else(||err("assignment absent"))?;
    let origin=quietly(||crate::credit::set_fields_exact(&root,&ws,room,&current,&[("hermes","0".into()),("hermes/account","0".into()),("hermes/assignment","0".into())],&format!("dismiss-{assignment}"))).map_err(err)?;
    let out=outbox(session,&h).join(format!("room-{room_cell}")).join(format!("assignment-{assignment}"));
    crate::hermes_handoff::seal_dismiss(&ws,&out,&origin).map_err(err)?;
    let notice = json!({"type":"mini-hermes-dismiss-v1","room":room,"hermes":h,"founder":me,
        "returnTo":state["manifest"]["founderAccount"],"account":state["manifest"]["account"],
        "revoked":revoked});
    put(&outbox(session,&h).join(format!("room-{room_cell}")).join(format!("assignment-{}",state["assignment"].as_str().unwrap())).join(format!("dismiss-{room}.json")), &notice)?;
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
    fn only_missing_registry_allows_fallback() {
        let root = std::env::temp_dir().join(format!("mini-registry-presence-{}-{}",
            std::process::id(), workspace::random_nonce().unwrap()));
        fs::create_dir(&root).unwrap();
        let path = root.join("registry.json");
        assert!(registry_file(&path).unwrap().is_none());
        fs::write(&path, b"{").unwrap();
        assert!(registry_file(&path).unwrap_err().starts_with("invalid resident registry"));
        fs::remove_file(&path).unwrap();
        fs::create_dir(&path).unwrap();
        assert!(registry_file(&path).is_err());
        fs::remove_dir(&path).unwrap();
        std::os::unix::fs::symlink(root.join("missing"), &path).unwrap();
        assert!(registry_file(&path).is_err());
        fs::remove_file(&path).unwrap();
        let registry = json!({"type":"mini-hermes-registry-v1","residents":[]});
        fs::write(&path, serde_json::to_vec(&registry).unwrap()).unwrap();
        assert_eq!(registry_file(&path).unwrap(), Some(registry));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn summon_selects_only_the_actual_rooms_sole_registration_without_node_file() {
        let first = json!({"subject":"8","task":"71","roomCell":"70","encryptionKey":"ab".repeat(32)});
        let unrelated = json!({"subject":"9","task":"72","roomCell":"80","encryptionKey":"cd".repeat(32)});
        let registry = json!({"type":"mini-hermes-registry-v1","residents":[first,unrelated]});
        assert_eq!(select_registration(Some(&registry), None, None, "70").unwrap(), first);
        assert_eq!(select_registration(Some(&registry), None, None, "80").unwrap(), unrelated);
        assert!(select_registration(Some(&registry), None, Some("9"), "70").is_err());
        assert!(select_registration(Some(&registry), None, None, "90").is_err());
        // A stale node record cannot override a current advertised room choice.
        assert_eq!(select_registration(Some(&registry), Some(&unrelated), None, "70").unwrap(), first);
        let empty = json!({"type":"mini-hermes-registry-v1","residents":[]});
        assert!(select_registration(Some(&empty), Some(&first), None, "70").is_err());
    }

    #[test]
    fn summon_requires_explicit_choice_for_multiple_room_residents() {
        let first = json!({"subject":"8","task":"71","roomCell":"70","encryptionKey":"ab".repeat(32)});
        let second = json!({"subject":"9","task":"72","roomCell":"70","encryptionKey":"cd".repeat(32)});
        let registry = json!({"type":"mini-hermes-registry-v1","residents":[first,second]});
        assert!(select_registration(Some(&registry), Some(&first), None, "70").unwrap_err().contains("select --hermes"));
        assert_eq!(select_registration(Some(&registry), None, Some("8"), "70").unwrap(), first);
        assert_eq!(select_registration(Some(&registry), None, Some("9"), "70").unwrap(), second);
        let duplicate = json!({"type":"mini-hermes-registry-v1","residents":[first,first]});
        assert!(select_registration(Some(&duplicate), None, Some("8"), "70").is_err());
        assert_eq!(select_registration(None, Some(&first), None, "70").unwrap(), first);
    }

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

    fn entry(height: u64, author: &str, cell: &str, sequence: u64, to: Option<&str>, re: Option<(&str, u64)>, payload: Value) -> chat::Entry {
        chat::Entry { height, author: author.into(), cell: cell.into(), sequence, topic: String::new(),
            to: to.map(str::to_owned), re: re.map(|(c, s)| (c.to_owned(), s)),
            payload: chat::Payload::Verified(payload.to_string()), owner: author.into() }
    }

    /// One classifier: only Hermes's entries are statuses, only the
    /// author's own entries are requests and withdrawals, and a terminal
    /// status is final whatever arrives later.
    #[test]
    fn request_rows_take_status_only_from_hermes_and_keep_terminal_final() {
        let say = |text: &str| json!({"type":"say","text":text});
        let st = |s: &str, t: &str| json!({"type":"request-status","status":s,"text":t});
        let feed = chat::merge(vec![
            entry(1, "7", "70", 1, Some("9"), None, say("first")),
            entry(2, "7", "70", 2, Some("9"), None, say("second")),
            entry(3, "8", "80", 1, Some("9"), None, say("not mine")),
            entry(4, "7", "70", 3, Some("8"), None, say("not to hermes")),
            entry(5, "9", "90", 1, Some("7"), Some(("70", 1)), st("queued", "1 ahead")),
            entry(6, "8", "80", 2, Some("7"), Some(("70", 1)), st("completed", "forged by a member")),
            entry(7, "9", "90", 2, Some("7"), Some(("70", 1)), st("started", "")),
            entry(8, "9", "90", 3, Some("7"), Some(("70", 1)), st("completed", "replied #12")),
            entry(9, "9", "90", 4, Some("7"), Some(("70", 1)), st("started", "late duplicate")),
            entry(10, "7", "70", 4, Some("9"), Some(("70", 2)), json!({"type":"withdraw"})),
            entry(11, "8", "80", 3, Some("9"), Some(("70", 1)), json!({"type":"withdraw"})),
            entry(12, "9", "90", 5, Some("7"), None, st("cancelled", "no ref: not a status")),
        ], Some("7".into()));
        let rows = request_rows(&feed, "7", "9");
        assert_eq!(rows.len(), 2);
        assert_eq!((rows[0].number, rows[0].status.as_str(), rows[0].detail.as_str(), rows[0].withdrawn),
                   (1, "completed", "replied #12", false));
        assert!(!rows[0].cancellable());
        assert_eq!((rows[1].number, rows[1].status.as_str(), rows[1].withdrawn), (2, "unacknowledged", true));
        assert!(!rows[1].cancellable(), "already withdrawn");
        let other = request_rows(&feed, "8", "9");
        assert_eq!(other.len(), 1);
        assert!(other[0].cancellable());
    }

    #[test]
    fn hermes_status_and_cancel_parse_and_refuse_malformed_lines() {
        assert_eq!(plan("hermes", " status").unwrap().unwrap(), Line::Status { room: None });
        assert_eq!(plan("hermes", " status lab").unwrap().unwrap(), Line::Status { room: Some("lab".into()) });
        assert_eq!(plan("hermes", " cancel 4 lab").unwrap().unwrap(), Line::Cancel { room: Some("lab".into()), number: 4 });
        for bad in [" cancel", " cancel 0", " cancel x", " status a b", " restart", " cancel 3 lab extra"] {
            assert!(plan("hermes", bad).unwrap().is_err(), "{bad}");
        }
    }

    /// The home row reports the last signed classification, or unavailable.
    #[test]
    fn home_row_reads_the_classifier_output_never_runtime_liveness() {
        let home = std::env::temp_dir().join(format!("mini-hermes-home-{}", std::process::id()));
        let rooms = home.join("chat").join("rooms");
        fs::create_dir_all(&rooms).unwrap();
        assert_eq!(home_request_status(&home, "lab")["status"], "unavailable");
        let row = RequestRow { number: 3, cell: "70".into(), sequence: 1, height: 5, status: "queued".into(),
            detail: String::new(), withdrawn: false };
        fs::write(rooms.join("lab.requests.json"), json!({"type":"mini-hermes-request-status-v1","room":"lab",
            "hermes":"9","height":5,"requests":[row.json()]}).to_string()).unwrap();
        let value = home_request_status(&home, "lab");
        assert_eq!(value["status"], "queued");
        assert_eq!(value["requests"][0]["cancellable"], true);
        assert_eq!(value["origin"], "last-signed-hermes-status-read");
        fs::remove_dir_all(home).unwrap();
    }

    #[test]
    fn request_status_say_is_typed_and_needs_its_request_and_author() {
        let parsed = chat::plan("say --to 7 --re 4 --status queued 1 ahead").unwrap().unwrap();
        assert!(matches!(parsed, chat::Line::Say { status: Some(ref s), re: Some(4), .. } if s == "queued"));
        assert!(chat::plan("say --to 7 --status queued hi").unwrap().is_err());
        assert!(chat::plan("say --re 4 --status queued hi").unwrap().is_err());
        assert!(chat::plan("say --to 7 --re 4 --status running hi").unwrap().is_err());
        let status = entry(1, "9", "90", 1, Some("7"), Some(("70", 1)), json!({"type":"request-status","status":"started"}));
        assert_eq!(chat::kind_of(&status), chat::Kind::RequestStatus { status: "started".into(), text: String::new() });
        let unbound = entry(1, "9", "90", 1, Some("7"), None, json!({"type":"withdraw"}));
        assert!(matches!(chat::kind_of(&unbound), chat::Kind::Raw(_)));
    }
}
