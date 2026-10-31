//! `mini shell`: a line-oriented session bound to one participant workspace.
//!
//! Every verb is exactly one client-contract operation, dispatched in-process
//! through the same `run` that the `mini` command line uses, with the argument
//! vector a caller of `mini` would have written. The shell owns syntax only:
//! splitting a line into words, confining file names to the session home, and
//! spelling the documented proposal request shapes. Every decision is the
//! Host's. A Host decision is recognised from the data the client retained
//! when the Host answered (`HostDecision`), never from error prose.
//!
//! Session layout (all owner-private):
//!   WORKSPACE            the `mini workspace` directory this session operates
//!   HOME/keys/           keys made by `keygen`
//!   HOME/enroll/NAME/    enrollment attempts this session sponsors
//!   HOME/keys/NAME.pub   a newcomer's public key, when they keep the secret
//!   HOME/requests/       proposal requests and predicates spelled by the shell
//!   HOME/inbox/          delegated references received with `import`
//!   HOME/refusals/       exact Host refusal frames and the Host's decoding
//!   HOME/provision/      the birth context the sponsor's `provision` wrote for
//!                        this subject, delivered by the operator; `init` binds it
//!   HOME/namespace/      this session's identifier namespace (made by `init`)
//!
//! Exit codes: 0 done, 1 client error (the Host was not asked or did not
//! answer), 2 shell usage, 3 refused by the Host, 4 the Host returned an
//! outcome that is not a decision (uncertain, contention, unavailable, absent).

use super::{Args, HostDecision, Result};
use serde_json::{json, Value};
use std::ffi::OsString;
use std::fs;
use std::io::{self, BufRead, IsTerminal, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

pub(crate) mod law;
mod template;
mod doc_render;
pub(crate) mod session_fs;

pub(crate) const EXIT_OK: i32 = 0;
pub(crate) const EXIT_CLIENT: i32 = 1;
pub(crate) const EXIT_USAGE: i32 = 2;
pub(crate) const EXIT_REFUSED: i32 = 3;
pub(crate) const EXIT_UNDECIDED: i32 = 4;

/// One row of the verb table: what the friend types and which client
/// operation it is.
pub(crate) struct Verb {
    pub name: &'static str,
    pub usage: &'static str,
    pub operation: &'static str,
}

pub(crate) const VERBS: &[Verb] = &[
    Verb { name: "app", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "home", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "private-compute", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "whoami", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "keygen", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "key-status", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "adopt-next-key", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "rotate-key", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "init", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "enroll", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "provision", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "refs", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "read", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "can", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "inspect", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "why", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "describe", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "import", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "kind", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "program", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "instance", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "create", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "propose", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "invoke", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "delegate", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "law", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "apps", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "market", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "bid", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "reveal", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "bids", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "submit", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "lookup", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "retry", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "attempt", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "publish", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "revoke", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "renounce", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    // `doc` is the first verb whose grammar is data (shell_grammar::DOC): its usage and operation
    // are rendered from it by `command_catalog`; this row only holds its place in the order.
    Verb { name: "doc", usage: "", operation: "" },
    Verb { name: "forget", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    // `room` is grammar data (shell_grammar::ROOM); the row holds its place, see `rendered_row`.
    Verb { name: "room", usage: "", operation: "" },
    Verb { name: "board", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "job", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "jobs", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "bend", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "inbox", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "export", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "pay", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "credit", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "tariff", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "topup", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "key", usage: "", operation: "" },  // grammar data (shell_grammar::KEY), rendered by `rendered_row`
    Verb { name: "history", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "help", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
    Verb { name: "exit", usage: "", operation: "" },  // grammar data (shell_grammar), rendered by `rendered_row`
];

/// One command catalog for help, completion and member action discovery.
/// The owning modules keep their actual grammars; callers use this iterator.
pub(crate) fn command_catalog() -> impl Iterator<Item = &'static Verb> {
    VERBS.iter().chain(crate::chat::VERBS).chain(crate::hermes::VERBS).chain(crate::story::VERBS).map(rendered_row)
}

/// A verb whose grammar is data (`shell_grammar::GRAMMARS`) shows the usage and operation rendered
/// from it, once per process; every other verb shows its hand-written row.
fn rendered_row(verb: &'static Verb) -> &'static Verb {
    static ROWS: std::sync::OnceLock<Vec<Verb>> = std::sync::OnceLock::new();
    let Some(_) = crate::shell_grammar::grammar(verb.name) else { return verb };
    let rows = ROWS.get_or_init(|| {
        crate::shell_grammar::GRAMMARS
            .iter()
            .map(|g| Verb {
                name: g.verb,
                usage: Box::leak(crate::shell_grammar::usage(g).into_boxed_str()),
                operation: Box::leak(crate::shell_grammar::operation(g).into_boxed_str()),
            })
            .collect()
    });
    rows.iter().find(|r| r.name == verb.name).unwrap_or(verb)
}

/// Subcommands spelled by the command's actual usage, without another table.
fn subcommands(verb: &str) -> Vec<String> {
    subcommands_after(verb,&format!("{verb} "))
}

/// The words that may follow `prefix` (`"doc "`, `"doc app-export "`): the next path word of every
/// grammar leaf under it, and the literal choices of a leaf's first argument when the leaf's path
/// is the prefix itself (`doc app-export publish|status|recover ID`). Read from the grammar, never
/// scraped from prose.
fn subcommands_after(verb: &str, prefix: &str) -> Vec<String> {
    let mut names = std::collections::BTreeSet::new();
    let words: Vec<&str> = prefix.split_whitespace().collect();
    if let Some(grammar) = crate::shell_grammar::grammar(verb) {
        for leaf in grammar.leaves {
            if leaf.path.len() < words.len() || !leaf.path.iter().zip(&words).all(|(p, w)| p == w) {
                continue;
            }
            if let Some(next) = leaf.path.get(words.len()) {
                names.insert((*next).to_owned());
            } else if let Some(crate::shell_grammar::Arg { kind: crate::shell_grammar::Kind::Choice(options), .. }) = leaf.args.first() {
                names.extend(options.iter().map(|o| (*o).to_owned()));
            }
        }
    }
    names.into_iter().collect()
}

/// What this shell is, stated as data: printed verbatim at the top of `help`
/// and when an interactive session starts. Nothing classifies it.
pub(crate) const HOSTED_CUSTODY_BANNER: &str = "hosted shell: your signing key is a file on this box; root can read and sign; for a key that never leaves your machine use `mini --remote` (see FRIENDS.md)";

/// Where the deployment installs the friends' guide (`deploy/shell/FRIENDS.md`).
pub(crate) const FRIENDS_GUIDE: &str = "/usr/local/lib/mini/FRIENDS.md";

/// Document laws a `doc new` chooses from. A cell has one law and it judges
/// every verb (reads and delegations carry no `content/*` slot), so each
/// content clause sits under `request/verb == 2` (mutate) and the other verbs
/// (observe 1, delegate 3, installPolicy 4, revoke 5) pass.
pub(crate) fn document_law(template: &str) -> Option<Value> {
    if template == "index" { return Some(crate::workspace::shared_names::index_law()); }
    let mutate = match template {
        // A bounded draft: anyone holding mutate may append and edit.
        "draft" => json!([{"type":"le","slot":"content/payload-bytes/after","value":"16384"}]),
        // An append-only note: no line is ever edited or struck.
        "note" => json!([{"type":"eq","slot":"content/atom-edits","value":"0"},
            {"type":"eq","slot":"content/tombstones","value":"0"}]),
        _ => return None,
    };
    let mut clauses = vec![json!({"type":"eq","slot":"request/verb","value":"2"})];
    clauses.extend(mutate.as_array().expect("array").iter().cloned());
    Some(json!({"type":"any","predicates":[
        {"type":"memberOf","slot":"request/verb","values":["1","3","4","5"]},
        {"type":"all","predicates":clauses}]}))
}

/// A room's law (K-ROOM 3c). The room cell's law judges every request that
/// names the room, and the birth gate asks it about every `place` (tag 10):
/// bearing a new cell into the room. `open` admits every member's placement
/// (holding a grant under the room is the gate); `realm` admits a placement
/// only by the founder and the named referees, so nobody else can birth an
/// account (a would-be realm asset) into the realm. Every other verb passes
/// the realm clause. What a room HOLDS is a template's business
/// (`room new NAME --template T`), not its law's.
fn room_law(law: &str, founder: &str, referees: &[String]) -> Option<Value> {
    match law {
        "open" => Some(json!({"type":"all","predicates":[]})),
        // A private room's own cell: what an open room has (every member
        // places); its keys cell carries the private law (`roomkey::keys_law`).
        "private" => Some(crate::workspace::roomkey::room_law()),
        "realm" => {
            let mut placers = vec![json!(founder)];
            placers.extend(referees.iter().map(|referee| json!(referee)));
            Some(json!({"type":"any","predicates":[
                {"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"10"}},
                {"type":"memberOf","slot":"request/subject","values":placers}]}))
        }
        _ => None,
    }
}

/// A template's lines with its placeholders bound, each line planned now:
/// a line that would be a usage error, or that would itself apply a template,
/// refuses the template before its first line runs.
fn template_plan(
    session: &Session,
    label: String,
    text: &str,
    vars: &[(&str, &str)],
) -> std::result::Result<Plan, String> {
    let lines = template::bind(&label, text, vars)?;
    if lines.is_empty() {
        return Err(format!("template {label} has no lines"));
    }
    for (number, line) in &lines {
        match plan(session, line) {
            Err(why) => return Err(format!("template {label} line {number}: {line}\n  {why}")),
            Ok(Plan::Template { .. }) => {
                return Err(format!("template {label} line {number}: {line}\n  a template line may not apply a template"))
            }
            Ok(_) => {}
        }
    }
    Ok(Plan::Template { label, lines })
}

/// Run a template's lines as the session's own typed lines, in order. The
/// first line that does not end `Done` stops the rest; the lines before it
/// stand (each was its own Host decision), and stderr names the line.
fn run_template(session: &Session, label: &str, lines: &[(usize, String)]) -> (i32, bool) {
    let total = lines.len();
    for (index, (number, text)) in lines.iter().enumerate() {
        eprintln!("{label} {}/{total} (line {number}): {text}", index + 1);
        let (code, more) = line(session, text);
        if code != EXIT_OK {
            eprintln!(
                "template {label} stopped at line {number}: {text}\n  lines after it were not run; the {index} line(s) before it stand"
            );
            return (code, true);
        }
        if !more {
            return (EXIT_OK, false);
        }
    }
    eprintln!("template {label}: {total} line(s) done");
    (EXIT_OK, true)
}


/// `room …`: each form is one client operation.
fn room_plan(session: &Session, w: &[String], _u: &str) -> std::result::Result<Plan, String> {
    use crate::shell_grammar::{parse, ROOM};
    let ws = session.workspace.clone();
    // The grammar names the leaf and checks every word's kind and count; each arm keeps its
    // semantics (private rooms, templates, the concierge).
    let p = parse(&ROOM, w)?;
    let id = p.arg(0);
    Ok(match p.leaf.path {
        ["room", action @ ("index" | "bind" | "rename" | "unbind")] => {
            let mut out = vec![flag("action", "shared-name"), flag("dir", ws),
                flag("op", if *action == "index" { "attach" } else { action }),
                flag("room", p.arg(1)), flag("id", id)];
            if *action == "index" { out.push(flag("to", p.arg(2))); }
            else {
                out.push(flag("name", p.arg(2)));
                if let Some(to) = p.opt(3) { out.push(flag("to", to)); }
            }
            Plan::Client { command: "workspace".into(), flags: out, writes: vec![] }
        }
        ["room", "resolve"] => Plan::Client { command: "workspace".into(), flags: vec![flag("action", "shared-name"),
            flag("dir", ws), flag("op", "resolve"), flag("room", p.arg(0))], writes: vec![] },
        ["room", "new"] => {
            let name = p.arg(0);
            let private = p.has("--private");
            let given = |f: &str| p.flag(f).flatten();
            if private && ["--law", "--template", "--concierge", "--period"].iter().any(|f| p.has(f)) {
                return Err("--private is the private room's law (its keys cell, your wrap); it takes no --law, --template or --concierge".into());
            }
            // `--concierge SUBJECT [--period N]`: the room's lines, then one
            // `room concierge` line (P-CREDIT): the room is born first, then
            // its till, runner account and the concierge's grants.
            if let Some(concierge) = given("--concierge") {
                workspace_name(name, "a room with a concierge (its lines name proposals after it)")?;
                let mut first = format!("room new {name}");
                for (flag_name, value) in &p.flags {
                    if let Some(value) = value {
                        if *flag_name != "--concierge" && *flag_name != "--period" {
                            first.push_str(&format!(" {flag_name} {value}"));
                        }
                    }
                }
                let mut last = format!("room concierge {name} {concierge}");
                if let Some(period) = given("--period") {
                    last.push_str(&format!(" --period {period}"));
                }
                let founder = session_subject(session)?;
                let text = match given("--template") {
                    Some(spec) => {
                        let (_, text) = template::source(&session.home, spec, template::Part::Room)?;
                        format!("{text}\n{last}\n")
                    }
                    None => format!("{first}\n{last}\n"),
                };
                let label = format!("room {name} with a concierge");
                return template_plan(session, label, &text, &[("ROOM", name), ("ME", &founder)]);
            }
            if p.has("--period") {
                return Err("--period is the concierge's week (--concierge SUBJECT --period N)".into());
            }
            if let Some(spec) = given("--template") {
                if p.flags.len() != 1 {
                    return Err("--template is the whole room: its first line births the room with its law (room template show T); give no other option".into());
                }
                workspace_name(name, "a templated room's name (its lines name proposals after it)")?;
                let founder = session_subject(session)?;
                let (label, text) = template::source(&session.home, spec, template::Part::Room)?;
                return template_plan(session, label, &text, &[("ROOM", name), ("ME", &founder)]);
            }
            let law_name = if private { "private" } else { given("--law").unwrap_or("open") };
            let referees: Vec<String> = p.values("--referee").into_iter().map(str::to_owned).collect();
            if !referees.is_empty() && law_name != "realm" {
                return Err("--referee names a realm's referee (--law realm)".into());
            }
            let founder = session_subject(session)?;
            let law = room_law(law_name, &founder, &referees)
                .ok_or_else(|| "a room's law is open, realm or private (--private)".to_owned())?;
            let path = session.home.join("requests").join(format!("room-{}.json", ref_file(name)));
            let mut flags_out = vec![
                flag("action", "create"),
                flag("dir", ws),
                flag("name", name),
                flag("storage", "declared"),
                flag("predicate", path.clone()),
                flag("room-template", law_name),
                flag("fields", crate::credit::room_declared_fields()),
            ];
            if let Some(parent) = given("--in") {
                flags_out.push(flag("in", parent));
            }
            Plan::Client { command: "workspace".into(), flags: flags_out, writes: vec![request_file(path, &law)] }
        }
        ["room", "welcome"] => {
            let spec = p.required("--template");
            let founder = session_subject(session)?;
            let (label, text) = template::source(&session.home, spec, template::Part::Member)?;
            return template_plan(session, label, &text, &[("ROOM", p.arg(0)), ("ME", &founder), ("MEMBER", p.arg(1))]);
        }
        ["room", "template", "list"] => Plan::Text(template::list()),
        ["room", "template", "show"] => {
            let part = if p.arg(1) == "member" { template::Part::Member } else { template::Part::Room };
            Plan::Text(template::show(&session.home, p.arg(0), part)?)
        }
        ["room", "invite"] => {
            let (name, invitee) = (p.arg(1), p.arg(2));
            let private = room_is_private(session, name);
            let enc = p.opt(3);
            let past = p.has("--past");
            let i_know = p.has("--i-know");
            if !private && (enc.is_some() || past || i_know) {
                return Err(format!("{name} is not a private room: DECLARATION, --past and --i-know are a private room's"));
            }
            if private && enc.is_none() {
                return Err(format!("{name} is private (devnet quality; privacy not audited): name the invitee's signed key declaration (its `room-key --op recipient-record` output, or @FILE in HOME/requests), or the 32-byte key id `whoami` prints if the invitee already published its record (`room register`)"));
            }
            let verbs: Vec<&str> = p.flag("--verbs").flatten().unwrap_or("observe,place").split(',').collect();
            let max_cost = p.flag("--max-cost").flatten().unwrap_or("50000");
            let mut request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                "name":name,"recipient":invitee,"verbs":verbs,"maxCost":max_cost,"room":true});
            if let Some(fields) = p.flag("--fields").flatten() {
                let fields: Vec<&str> = fields.split(',').collect();
                request["fields"] = json!(fields);
            }
            if let Some(bounds) = p.flag("--max-delta").flatten() {
                let mut out = Vec::new();
                for bound in bounds.split(',') {
                    let (field, max) = bound.split_once('=').ok_or_else(|| "--max-delta is FIELD=N[,FIELD=N...]".to_owned())?;
                    decimal(max, "max delta")?;
                    out.push(json!({"field":field,"max":max}));
                }
                request["maxDelta"] = json!(out);
            }
            match enc {
                None => proposal(session, id, &request),
                Some(enc) => {
                    let enc = enc_argument(session, enc)?;
                    let path = session.home.join("requests").join(format!("{id}.json"));
                    let flags = crate::workspace::roomkey::invite_flags("invite", Path::new(&ws), name,
                        invitee, &enc, id, Some(&path), past, i_know);
                    Plan::Client { command: "workspace".into(), flags, writes: vec![request_file(path, &request)] }
                }
            }
        }
        ["room", "kick"] => {
            let (name, member) = (p.arg(1), p.arg(2));
            if room_is_private(session, name) {
                // Revoke, then rotate and rewrap, both submitted: the kicked
                // member keeps the past and gets nothing new.
                return Ok(Plan::Client { command: "workspace".into(), flags: vec![flag("action", "room-key"), flag("op", "kick"),
                    flag("dir", ws), flag("name", name), flag("member", member), flag("proposal-id", id)], writes: vec![] });
            }
            // Every standing grant SUBJECT holds under the room, from the
            // Host's signed who view: one revoke each; `submit ID` submits all.
            Plan::Client { command: "workspace".into(), flags: vec![flag("action", "room-kick"), flag("dir", ws),
                flag("name", name), flag("member", member), flag("proposal-id", id)], writes: vec![] }
        }
        ["room", "seal"] => {
            // A room's law is where its roster is enforced: sealing it freezes
            // membership forever. Said out loud, and only on --freeze-roster.
            let name = p.arg(1);
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"install-policy",
                "name":name,"predicate":{"type":"any","predicates":[]}});
            let mut plan = proposal(session, id, &request);
            if let Plan::Client { flags, .. } = &mut plan {
                flags.push(flag("freeze-roster", "true"));
                flags.push(flag("room-cell", "true"));
            }
            plan
        }
        ["room", op @ ("rotate" | "register")] => Plan::Client { command: "workspace".into(), flags: vec![flag("action", "room-key"), flag("op", *op),
            flag("dir", ws), flag("name", p.arg(1)), flag("proposal-id", id)], writes: vec![] },
        ["room", "transition"] => {
            // room transition ID NAME NEXTFILE: hand a private room I founded to my NEXT
            // signing key, BEFORE `rotate-key NEXTFILE` (which refuses a founder until then).
            Plan::Client { command: "workspace".into(), flags: vec![flag("action", "room-key"), flag("op", "transition"), flag("dir", ws),
                flag("name", p.arg(1)), flag("proposal-id", id), flag("next-key", session.home.join("keys").join(p.arg(2)))], writes: vec![] }
        }
        ["room", "rewrap"] => Plan::Client { command: "workspace".into(), flags: vec![flag("action", "room-key"), flag("op", "rewrap"), flag("dir", ws),
            flag("name", p.arg(1)), flag("member", p.arg(2)), flag("proposal-id", id)], writes: vec![] },
        ["room", "keys"] => Plan::Client { command: "workspace".into(), flags: vec![flag("action", "room-key"), flag("op", "list"), flag("dir", ws), flag("name", p.arg(0))], writes: vec![] },
        ["room", "leave"] => {
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"renounce","name":p.arg(1),"leave":true});
            proposal(session, id, &request)
        }
        ["room", action @ ("members" | "law")] => Plan::Client { command: "workspace".into(), flags: vec![
            flag("action", if *action == "members" { "who" } else { "describe" }), flag("dir", ws), flag("name", p.arg(0))], writes: vec![] },
        ["room", "list"] => Plan::Rooms,
        ["room", "status"] => Plan::Client { command: "credit".into(), flags: vec![flag("action", "status"), flag("dir", ws),
            flag("room", p.arg(0)), flag("inbox", session.home.join("inbox"))], writes: vec![] },
        ["room", "renew"] => {
            let mut out = vec![flag("action", "renew"), flag("dir", ws), flag("room", p.arg(0)), flag("subject", p.arg(1)), flag("outbox", session.home.join("outbox"))];
            match (p.flag("--for").flatten(), p.flag("--until").flatten()) {
                (Some(n), None) => out.push(flag("for", n)),
                (None, Some(h)) => out.push(flag("not-after", h)),
                (None, None) => {}
                _ => return Err("room renew takes --for N or --until H".into()),
            }
            Plan::Client { command: "credit".into(), flags: out, writes: vec![] }
        }
        ["room", "concierge"] => {
            let mut out = vec![flag("action", "install"), flag("dir", ws), flag("room", p.arg(0)), flag("concierge", p.arg(1)),
                flag("outbox", session.home.join("outbox")), flag("program", session.home.join("concierge").join(format!("{}.json", p.arg(0))))];
            for key in ["period", "fund"] {
                if let Some(value) = p.flag(&format!("--{key}")).flatten() {
                    out.push(flag(key, value));
                }
            }
            Plan::Client { command: "credit".into(), flags: out, writes: vec![] }
        }
        // `room ls` is the chat verb's (chat.rs intercepts it before this arm).
        _ => return Err(crate::shell_grammar::usage(&ROOM)),
    })
}

/// The board law (docs/PLACE.md §2.2): task `n` has its state in field `2n+2`
/// (0 todo, 1 doing, 2 done) and its owner in field `2n+3`. A state never
/// goes backwards (a present delta is never negative; a field created in this
/// turn has no delta) and an owner, once taken, is never replaced. The law
/// names tasks 0 and 1, and `board new` declares exactly their fields (2-5,
/// K-FIELD-CLOSURE), so the Host refuses any other field by name.
fn board_law() -> Value {
    let mut clauses = vec![json!({"type":"eq","slot":"request/verb","value":"2"})];
    for task in 0..2u32 {
        clauses.push(json!({"type":"not","predicate":
            {"type":"le","slot":format!("resource/field/{}/delta", 2 * task + 2),"value":"-1"}}));
        clauses.push(json!({"type":"writeOnce","slot":format!("resource/field/{}/after", 2 * task + 3)}));
    }
    json!({"type":"any","predicates":[
        {"type":"memberOf","slot":"request/verb","values":["1","3","4","5"]},
        {"type":"all","predicates":clauses}]})
}

fn board_state(value: &str) -> &'static str {
    // The grammar admits exactly these three words.
    match value {
        "todo" => "0",
        "doing" => "1",
        _ => "2",
    }
}

/// Text for a document line: a literal word, or `@FILE` from HOME/requests.
fn text_argument(session: &Session, word: &str) -> std::result::Result<String, String> {
    let text = if let Some(file) = word.strip_prefix('@') {
        session_file(file, "text file")?;
        let path = session.home.join("requests").join(file);
        let bytes = session_fs::read(&session.home, &path, 4097)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        String::from_utf8(bytes).map_err(|_| "text file is not UTF-8".to_owned())?
    } else {
        word.to_owned()
    };
    if text.is_empty() || text.len() > 4096 {
        return Err("document text must be 1..4096 bytes".into());
    }
    Ok(text)
}

fn document_proposal(session: &Session, id: &str, name: &str, action: Value) -> Plan {
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"document","actions":[action]}}]});
    proposal(session, id, &request)
}

fn scalar_proposal(session: &Session, id: &str, name: &str, action: Value) -> Plan {
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"scalar","actions":[action]}}]});
    proposal(session, id, &request)
}

/// This session's subject, from its workspace pin.
fn session_subject(session: &Session) -> std::result::Result<String, String> {
    read_json(&session.workspace.join("workspace.json"))
        .and_then(|pin| pin.get("subject").and_then(Value::as_str).map(str::to_owned))
        .ok_or_else(|| "this session has no workspace yet (init first)".to_owned())
}

/// Whether a room reference in this session's workspace is a private room.
fn room_is_private(session: &Session, room: &str) -> bool {
    read_json(&session.workspace.join("refs").join(format!("{room}.json")))
        .is_some_and(|value| value.get("private").is_some())
}

/// Remove every `word` from `words`; whether it was there.
fn take_switch(words: &mut Vec<String>, word: &str) -> bool {
    let before = words.len();
    words.retain(|w| w != word);
    words.len() != before
}

/// A signed recipient declaration (hex or JSON), or an existing-record public-key selector.
fn enc_argument(session: &Session, word: &str) -> std::result::Result<String, String> {
    let text = match word.strip_prefix('@') {
        Some(file) => {
            session_file(file, "encryption key file")?;
            let path = session.home.join("requests").join(file);
            String::from_utf8(session_fs::read(&session.home, &path, 8192)?).map_err(|error| error.to_string())?
        }
        None => word.to_owned(),
    };
    crate::workspace::roomkey::recipient_argument(&text)
}

/// The birth options of a `create` or `doc new` line, removed from it:
/// `--in ROOM` (born in the room a reference names; the Host's birth gate
/// decides) and, on `create`, `--owner SUBJECT` (born owned by another
/// subject: a room founder birthing a member's stream, docs/PLACE.md §2.3 (a)). Each
/// is a pair of words after the name, in any order.
#[derive(Debug, Default, PartialEq)]
struct Birth {
    room: Option<String>,
    owner: Option<String>,
    from: Option<String>,
}

fn take_birth(words: &mut Vec<String>) -> std::result::Result<Birth, String> {
    let verb = (words.first().map(String::as_str), words.get(1).map(String::as_str));
    let create = matches!(verb.0, Some("create"));
    let first = match verb {
        (Some("create"), _) => 2,
        (Some("doc"), Some("new")) | (Some("kind"), Some("create")) | (Some("program"), Some("create")) => 3,
        _ => return Ok(Birth::default()),
    };
    let mut birth = Birth::default();
    let mut i = first;
    while i < words.len() {
        let slot = match words[i].as_str() {
            "--in" => &mut birth.room,
            "--owner" if create => &mut birth.owner,
            "--from" if create => &mut birth.from,
            _ => {
                i += 1;
                continue;
            }
        };
        let flag = words[i].clone();
        let value = words
            .get(i + 1)
            .cloned()
            .ok_or_else(|| format!("{flag} needs a value"))?;
        if slot.replace(value).is_some() {
            return Err(format!("{flag} given twice"));
        }
        words.drain(i..i + 2);
    }
    if let Some(room) = &birth.room {
        ref_name(room, "room name")?;
    }
    if let Some(from) = &birth.from { ref_name(from, "kind reference")?; }
    if let Some(owner) = &birth.owner {
        decimal(owner, "owner")?;
    }
    Ok(birth)
}

pub(crate) struct Session {
    pub workspace: PathBuf,
    pub home: PathBuf,
    pub host: PathBuf,
    pub config: PathBuf,
}

/// What a line means, before anything runs.
#[derive(Debug, PartialEq)]
pub(crate) enum Plan {
    /// One client-contract call. `writes` are files the shell spells first
    /// (request JSON), each created exactly once.
    Client {
        command: String,
        flags: Vec<(String, OsString)>,
        writes: Vec<(PathBuf, Vec<u8>)>,
    },
    Whoami,
    Inbox,
    Guide,
    /// The verb exists in the place's grammar but this store cannot express
    /// it; the text names what is missing. Nothing is signed or sent.
    NotHere(String),
    Export(PathBuf),
    /// Local: the workspace references that are rooms (founded here, or an
    /// imported room invite). Discovery only.
    Rooms,
    /// Shell lines from a template, substituted, each planned once already
    /// (a line that does not plan refuses the whole template before anything
    /// runs). They run in order, as typed lines; the first that does not end
    /// `Done` stops the rest.
    Template { label: String, lines: Vec<(usize, String)> },
    /// Local text for stdout.
    Text(String),
    History { all: bool },
    Help(Option<String>),
    /// A chat verb (`crate::chat`): it composes several client operations.
    Chat(crate::chat::Line),
    /// A story verb (`crate::story`): the table, its law, a player's moves.
    Story(crate::story::Line),
    Exit,
    Nothing,
}

// ---------------------------------------------------------------- words

/// Split a line into words. Whitespace separates; `'…'` is literal; `"…"`
/// honours `\"` and `\\`; a word that starts with `{` or `[` is one JSON
/// value up to its balancing bracket; `#` at the start of a word begins a
/// comment. There is no expansion, substitution or globbing.
pub(crate) fn words(line: &str) -> std::result::Result<Vec<String>, String> {
    let chars: Vec<char> = line.chars().collect();
    let mut out = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        while i < chars.len() && chars[i].is_whitespace() {
            i += 1;
        }
        if i >= chars.len() || chars[i] == '#' {
            break;
        }
        let mut word = String::new();
        if chars[i] == '{' || chars[i] == '[' {
            let mut depth = 0usize;
            let mut in_string = false;
            let mut escaped = false;
            loop {
                let Some(&c) = chars.get(i) else {
                    return Err("unbalanced JSON word".into());
                };
                word.push(c);
                i += 1;
                if in_string {
                    if escaped {
                        escaped = false;
                    } else if c == '\\' {
                        escaped = true;
                    } else if c == '"' {
                        in_string = false;
                    }
                    continue;
                }
                match c {
                    '"' => in_string = true,
                    '{' | '[' => depth += 1,
                    '}' | ']' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
            }
            if i < chars.len() && !chars[i].is_whitespace() {
                return Err("a JSON word must be followed by a space or the end of the line".into());
            }
            out.push(word);
            continue;
        }
        while i < chars.len() && !chars[i].is_whitespace() {
            match chars[i] {
                '\'' => {
                    i += 1;
                    loop {
                        match chars.get(i) {
                            None => return Err("unterminated single quote".into()),
                            Some('\'') => break,
                            Some(&c) => word.push(c),
                        }
                        i += 1;
                    }
                    i += 1;
                }
                '"' => {
                    i += 1;
                    loop {
                        match chars.get(i) {
                            None => return Err("unterminated double quote".into()),
                            Some('"') => break,
                            Some('\\') if matches!(chars.get(i + 1), Some('"') | Some('\\')) => {
                                word.push(chars[i + 1]);
                                i += 1;
                            }
                            Some(&c) => word.push(c),
                        }
                        i += 1;
                    }
                    i += 1;
                }
                c => {
                    word.push(c);
                    i += 1;
                }
            }
        }
        out.push(word);
    }
    Ok(out)
}

// ---------------------------------------------------------------- names

/// Workspace names, proposal IDs and reference names use the client's own
/// rule (1..64 ASCII letters, digits or hyphens). The client checks again;
/// the shell checks first only because it builds paths from them.
fn workspace_name(value: &str, label: &str) -> std::result::Result<(), String> {
    if value.is_empty()
        || value.len() > 64
        || !value.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
    {
        return Err(format!("{label} must be 1..64 ASCII letters, digits or hyphens"));
    }
    Ok(())
}

/// A reference name: a workspace name, or segments under a room
/// (`lab/index`); the client's own rule (`workspace::validate_ref_name`).
/// Files the shell names after a reference use `workspace::ref_file`.
fn ref_name(value: &str, label: &str) -> std::result::Result<(), String> {
    crate::workspace::validate_ref_name(value)
        .map_err(|_| format!("{label} must be 1..64 ASCII letters, digits or hyphens, or such segments joined by '/' (lab/index)"))
}

fn ref_file(name: &str) -> String {
    crate::workspace::ref_file(name)
}

/// A file name inside one session directory: no separators, no leading dot.
fn session_file(value: &str, label: &str) -> std::result::Result<(), String> {
    if value.is_empty()
        || value.len() > 64
        || value.starts_with('.')
        || !value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
    {
        return Err(format!(
            "{label} must be a plain file name (letters, digits, '-', '_', '.'; no leading dot)"
        ));
    }
    Ok(())
}

/// Exactly `length` bytes spelled as lowercase or uppercase hex.
// A shell word a person typed (a key, a signature): either case reads.
fn hex_bytes(word: &str, length: usize) -> Option<Vec<u8>> {
    if word.len() != 2 * length {
        return None;
    }
    crate::decode_hex(word).ok()
}

fn decimal(value: &str, label: &str) -> std::result::Result<(), String> {
    if !mini_sdk::decimal::is_digits(value) {
        return Err(format!("{label} must be a decimal number"));
    }
    Ok(())
}

/// A JSON argument: inline, or `@FILE` read from HOME/requests/FILE.
fn json_argument(session: &Session, word: &str, label: &str) -> std::result::Result<Value, String> {
    let text = if let Some(file) = word.strip_prefix('@') {
        session_file(file, label)?;
        let path = session.home.join("requests").join(file);
        let bytes = session_fs::read(&session.home, &path, 1 << 20)?;
        String::from_utf8(bytes).map_err(|_| format!("{label} file is not UTF-8"))?
    } else {
        word.to_owned()
    };
    serde_json::from_str(&text).map_err(|e| format!("{label} is not JSON: {e}"))
}

/// A law: grammar text (`law::parse`), one JSON predicate as before, or
/// `@FILE` from HOME/requests holding either. Several words are one law text,
/// joined by single spaces.
fn law_argument(session: &Session, words: &[String]) -> std::result::Result<Value, String> {
    if let [word] = words {
        if word.starts_with('{') {
            return json_argument(session, word, "predicate");
        }
        if let Some(file) = word.strip_prefix('@') {
            session_file(file, "law")?;
            let path = session.home.join("requests").join(file);
            let bytes = session_fs::read(&session.home, &path, 1 << 20)?;
            let text = String::from_utf8(bytes).map_err(|_| "law file is not UTF-8".to_string())?;
            if text.trim_start().starts_with('{') {
                return serde_json::from_str(&text).map_err(|e| format!("law file is not JSON: {e}"));
            }
            return law::parse(&text).map_err(|e| format!("law: {e}"));
        }
    }
    law::parse(&words.join(" ")).map_err(|e| format!("law: {e}"))
}

/// `law check -`: the law (grammar or JSON) from standard input, to EOF.
fn law_from_stdin() -> std::result::Result<Value, String> {
    let mut text = String::new();
    io::stdin()
        .take(1 << 20)
        .read_to_string(&mut text)
        .map_err(|e| format!("cannot read the law from standard input: {e}"))?;
    if text.trim_start().starts_with('{') {
        return serde_json::from_str(&text).map_err(|e| format!("law is not JSON: {e}"));
    }
    law::parse(&text).map_err(|e| format!("law: {e}"))
}

fn request_file(path: PathBuf, value: &Value) -> (PathBuf, Vec<u8>) {
    let mut bytes = serde_json::to_vec(value).expect("JSON values serialise");
    bytes.push(b'\n');
    (path, bytes)
}

fn flag(name: &str, value: impl Into<OsString>) -> (String, OsString) {
    (name.to_owned(), value.into())
}

fn proposal(session: &Session, id: &str, request: &Value) -> Plan {
    let path = session.home.join("requests").join(format!("{id}.json"));
    Plan::Client {
        command: "workspace".into(),
        flags: vec![
            flag("action", "propose"),
            flag("dir", session.workspace.clone()),
            flag("request", path.clone()),
            flag("proposal-id", id),
        ],
        writes: vec![request_file(path, request)],
    }
}

// ---------------------------------------------------------------- plan

fn arity(words: &[String], min: usize, max: usize, usage: &str) -> std::result::Result<(), String> {
    let n = words.len() - 1;
    if n < min || n > max {
        return Err(usage.to_owned());
    }
    Ok(())
}

fn usage_of(name: &str) -> &'static str {
    // Through the catalog, so a grammar-backed verb answers its rendered usage.
    VERBS.iter().find(|v| v.name == name).map(|v| rendered_row(v).usage).unwrap_or("")
}

/// Map one line to one client operation. Pure: reads nothing but `@FILE`
/// arguments and writes nothing.
pub(crate) fn plan(session: &Session, line: &str) -> std::result::Result<Plan, String> {
    if let Some(chat) = crate::chat::plan(line) {
        return chat.map(Plan::Chat);
    }
    if let Some(story) = crate::story::plan(line) {
        return story.map(Plan::Story);
    }
    let mut w = words(line)?;
    // `create` and `doc new` may end `--in ROOM`: the new cell is born in the
    // room a reference names (the Host's birth gate decides).
    let birth = take_birth(&mut w)?;
    let room = birth.room.clone();
    let Some(verb) = w.first() else {
        return Ok(Plan::Nothing);
    };
    let u = usage_of(verb);
    let ws = || session.workspace.clone();
    let client = |command: &str, flags: Vec<(String, OsString)>| Plan::Client {
        command: command.into(),
        flags,
        writes: vec![],
    };
    Ok(match verb.as_str() {
        "app" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::APP, &w)?;
            match p.leaf.path {
                ["app", "status"] => {
                    let mut args = vec![flag("dir", ws()), flag("action", "app-status"), flag("name", p.arg(0))];
                    if p.has("--json") { args.push(flag("json", "true")); }
                    client("member", args)
                }
                ["app", "delegate-lifecycle", "prepare"] => {
                    crate::workspace::validate_name(p.arg(0))?;
                    let (package, snapshot, manager) = (p.required("--package"), p.required("--snapshot"), p.required("--manager"));
                    client("workspace", vec![flag("dir", ws()), flag("action", "app-lifecycle"), flag("request-id", p.arg(0)), flag("op", "prepare"),
                        flag("name", p.arg(1)), flag("package-name", package), flag("snapshot-name", snapshot), flag("manager", manager)])
                }
                _ => {
                    crate::workspace::validate_name(p.arg(1))?;
                    client("workspace", vec![flag("dir", ws()), flag("action", "app-lifecycle"), flag("request-id", p.arg(1)), flag("op", p.arg(0))])
                }
            }
        }
        "home" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::HOME, &w)?;
            let mut flags = vec![flag("dir", session.workspace.clone()), flag("home", session.home.clone())];
            if let Some(name) = p.opt(0) { flags.push(flag("name", name)); }
            if p.has("--json") { flags.push(flag("json", "true")); }
            Plan::Client { command: "member".into(), flags, writes: vec![] }
        }
        "private-compute" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::PRIVATE_COMPUTE, &w)?;
            // Typed by the grammar (decimal); bounded here, before anything runs.
            for (name, at) in [("LEFT", 0), ("RIGHT", 1)] {
                if p.arg(at).parse::<u8>().is_err() {
                    return Err(format!("{name} must be a decimal value 0..=255"));
                }
            }
            client("private-compute", vec![flag("left", p.arg(0)), flag("right", p.arg(1))])
        }
        "whoami" => {
            crate::shell_grammar::parse(&crate::shell_grammar::WHOAMI, &w)?;
            Plan::Whoami
        }
        "help" | "?" => {
            let mut named = w.clone();
            named[0] = "help".into();
            let p = crate::shell_grammar::parse(&crate::shell_grammar::HELP, &named)?;
            match p.opt(0) {
                Some("guide") => Plan::Guide,
                topic => Plan::Help(topic.map(str::to_owned)),
            }
        }
        "inbox" => {
            crate::shell_grammar::parse(&crate::shell_grammar::INBOX, &w)?;
            Plan::Inbox
        }
        "revoke" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::REVOKE, &w)?;
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"revoke","name":p.arg(1),"recipient":p.arg(2)});
            proposal(session, p.arg(0), &request)
        }
        "renounce" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::RENOUNCE, &w)?;
            let request = if p.index_in(&crate::shell_grammar::RENOUNCE) == 1 {
                json!({"type":"minidregg-workspace-proposal-v1","action":"renounce","capability":p.arg(1),"kind":p.arg(2)})
            } else {
                json!({"type":"minidregg-workspace-proposal-v1","action":"renounce","name":p.arg(1)})
            };
            proposal(session, p.arg(0), &request)
        }
        "room" => room_plan(session, &w, u)?,
        "forget" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::FORGET, &w)?;
            let mut flags = vec![flag("action", "room-key"), flag("op", "forget"), flag("dir", ws()), flag("name", p.arg(0))];
            if let Some(epoch) = p.opt(1) { flags.push(flag("epoch", epoch)); }
            client("workspace", flags)
        }
        "doc" => {
            // The grammar does the counting and the checking; each leaf keeps only its semantics.
            let p = crate::shell_grammar::parse(&crate::shell_grammar::DOC, &w)?;
            let requests = |file: &str| session.home.join("requests").join(file.trim_start_matches('@'));
            let session_file_of = |value: &str, label: &str| -> std::result::Result<PathBuf, String> {
                let file = value.strip_prefix('@').ok_or_else(|| format!("{label} uses @FILE in HOME/requests"))?;
                session_file(file, label)?;
                Ok(session.home.join("requests").join(file))
            };
            match p.leaf.path {
                ["doc", "app-export", "capture"] => client("workspace", vec![flag("action", "app-document"), flag("dir", ws()), flag("op", "capture"), flag("id", p.arg(0)), flag("binding", session_file_of(p.arg(1), "app export binding")?)]),
                ["doc", "app-export"] => client("workspace", vec![flag("action", "app-document"), flag("dir", ws()), flag("op", p.arg(0)), flag("id", p.arg(1))]),
                ["doc", "app-export", "rebase"] => client("workspace", vec![flag("action", "app-document"), flag("dir", ws()), flag("op", "rebase"), flag("id", p.arg(0)), flag("next", p.arg(1))]),
                ["doc", "device"] => client("workspace", vec![flag("action", "doc-device"), flag("dir", ws())]),
                ["doc", "share"] => client("workspace", vec![flag("action", "doc-share"), flag("dir", ws()), flag("change", p.arg(0)), flag("name", p.arg(1)), flag("subject", p.arg(2)),
                    flag("device", session_file_of(p.arg(3), "document sharing file")?), flag("output", session_file_of(p.arg(4), "document sharing file")?)]),
                ["doc", "revoke"] => client("workspace", vec![flag("action", "doc-revoke"), flag("dir", ws()), flag("change", p.arg(0)), flag("name", p.arg(1)), flag("subject", p.arg(2))]),
                ["doc", "membership-recover"] => {
                    let mut flags = vec![flag("action", "doc-membership-recover"), flag("dir", ws()), flag("change", p.arg(0)), flag("name", p.arg(1))];
                    if let Some(invitation) = p.opt(2) {
                        flags.push(flag("output", session_file_of(invitation, "invitation")?));
                    }
                    client("workspace", flags)
                }
                ["doc", "accept"] => client("workspace", vec![flag("action", "doc-accept"), flag("dir", ws()), flag("name", p.arg(0)), flag("catalog", p.arg(1)), flag("bundle", session_file_of(p.arg(2), "invitation")?)]),
                ["doc", action @ ("protect" | "protect-current" | "protect-recover")] => client("workspace", vec![flag("action", format!("doc-{action}")), flag("dir", ws()), flag("name", p.arg(0))]),
                ["doc", "epoch-export"] => client("workspace", vec![flag("action", "doc-epoch-export"), flag("dir", ws()), flag("name", p.arg(0)), flag("output", session_file_of(p.arg(1), "epoch bundle")?)]),
                ["doc", "epoch-import"] => client("workspace", vec![flag("action", "doc-epoch-import"), flag("dir", ws()), flag("name", p.arg(0)), flag("catalog", p.arg(1)), flag("bundle", session_file_of(p.arg(2), "epoch bundle")?)]),
                ["doc", "context"] => {
                    let mut flags = vec![flag("action", "doc-context"), flag("dir", ws()), flag("name", p.arg(0))];
                    match (p.opt(1), p.opt(2)) {
                        (None, None) => {}
                        (Some(rows), Some(bytes)) => { flags.push(flag("max-rows", rows)); flags.push(flag("max-bytes", bytes)); }
                        _ => return Err("doc context NAME [MAX-ROWS MAX-BYTES]".into()),
                    }
                    client("workspace", flags)
                }
                ["doc", "review"] => client("workspace", vec![flag("action", "context-review"), flag("dir", ws()), flag("proposal-id", p.arg(0)),
                    flag("context", session_file_of(p.arg(1), "review context")?), flag("request", session_file_of(p.arg(2), "review request")?)]),
                ["doc", "search"] => {
                    let mut flags = vec![flag("action", "doc-search"), flag("dir", ws()), flag("text", p.arg(0)), flag("scope", p.arg(1))];
                    match (p.opt(2), p.opt(3)) {
                        (None, None) => {}
                        (Some(offset), Some(cursor)) => { flags.push(flag("offset", offset)); flags.push(flag("cursor", cursor)); }
                        _ => return Err("doc search QUERY NAME[,NAME...]|@held [OFFSET CURSOR]".into()),
                    }
                    client("workspace", flags)
                }
                ["doc", "hit"] => client("workspace", vec![flag("action", "doc-search-follow"), flag("dir", ws()), flag("name", p.arg(0)), flag("target", p.arg(1)), flag("atom", p.arg(2)), flag("revision", p.arg(3))]),
                ["doc", "new"] => {
                    // `draft`, `note`, `index`, or the document's own law in the law grammar (one
                    // word: quote it), JSON, or `@FILE`.
                    let law = match p.opt(1).unwrap_or("draft") {
                        stock @ ("draft" | "note" | "index") => document_law(stock).expect("stock document law"),
                        other => law_argument(session, &[other.to_owned()])?,
                    };
                    let path = requests(&format!("create-{}.json", ref_file(p.arg(0))));
                    let mut flags = vec![flag("action", "doc-new"), flag("dir", ws()), flag("name", p.arg(0)), flag("predicate", path.clone())];
                    if let Some(room) = &room {
                        flags.push(flag("in", room.clone()));
                    }
                    Plan::Client { command: "workspace".into(), flags, writes: vec![request_file(path, &law)] }
                }
                ["doc", "show" | "outline" | "history" | "diff" | "pull" | "range" | "mark" | "unmark" | "insert" | "move" | "remove" | "transclude" | "transclusions" | "follow" | "links" | "backlinks"] => {
                    // The render verbs keep their own flag mapping (`doc_render::doc_flags`); the grammar
                    // has already checked the words.
                    let mut words = w.clone();
                    if p.leaf.path[1] == "insert" {
                        words[4] = text_argument(session, &words[4])?;
                    }
                    let mut flags: Vec<(String, OsString)> = doc_render::doc_flags(&words)
                        .map_err(|message| message.strip_prefix("usage: ").map(str::to_owned).unwrap_or(message))?
                        .into_iter()
                        .map(|(name, value)| flag(name, value))
                        .collect();
                    flags.insert(1, flag("dir", ws()));
                    client("workspace", flags)
                }
                ["doc", "push"] => {
                    // @FILE is HOME/requests/FILE; @- is standard input (`ssh … doc push ID NAME @- < f.md`).
                    let file = if p.arg(2) == "@-" { PathBuf::from("-") } else { session_file_of(p.arg(2), "pushed file")? };
                    client("workspace", vec![flag("action", "doc-push"), flag("dir", ws()), flag("name", p.arg(1)), flag("file", file), flag("proposal-id", p.arg(0)), flag("attempt", ws().join("attempts").join(p.arg(0)))])
                }
                ["doc", "append"] => {
                    let text = text_argument(session, p.arg(2))?;
                    document_proposal(session, p.arg(0), p.arg(1), json!({"type":"append","text":text}))
                }
                ["doc", "edit"] => {
                    let text = text_argument(session, p.arg(3))?;
                    document_proposal(session, p.arg(0), p.arg(1), json!({"type":"edit","line":p.arg(2),"text":text}))
                }
                ["doc", "annotate"] => {
                    let text = text_argument(session, p.arg(3))?;
                    document_proposal(session, p.arg(0), p.arg(1), json!({"type":"annotate","line":p.arg(2),"text":text}))
                }
                ["doc", "link"] => {
                    let relation = p.opt(3).unwrap_or("0");
                    document_proposal(session, p.arg(0), p.arg(1), json!({"type":"link","to":p.arg(2),"relation":relation}))
                }
                _ => return Err(u.to_owned()),
            }
        }
        "board" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::BOARD, &w)?;
            let task_field = |task: &str, offset: u64| -> std::result::Result<String, String> {
                task.parse::<u64>()
                    .ok()
                    .and_then(|n| n.checked_mul(2)?.checked_add(2 + offset))
                    .map(|n| n.to_string())
                    .ok_or_else(|| "task number is too large".to_owned())
            };
            match p.leaf.path {
                ["board", "new"] => {
                    let path = session.home.join("requests").join(format!("create-{}.json", ref_file(p.arg(0))));
                    Plan::Client {
                        command: "workspace".into(),
                        flags: vec![flag("action", "create"), flag("dir", ws()), flag("name", p.arg(0)), flag("storage", "declared"), flag("predicate", path.clone()),
                            // The board law governs tasks 0 and 1: fields 2-5, no other.
                            flag("fields", "2-5")],
                        writes: vec![request_file(path, &board_law())],
                    }
                }
                ["board", "add"] => {
                    let field = task_field(p.arg(2), 0)?;
                    scalar_proposal(session, p.arg(0), p.arg(1), json!({"type":"create","key":{"type":"object","field":field},"value":"0"}))
                }
                ["board", "move"] => {
                    let field = task_field(p.arg(2), 0)?;
                    let from = board_state(p.arg(3));
                    let to = board_state(p.arg(4));
                    scalar_proposal(session, p.arg(0), p.arg(1), json!({"type":"write","key":{"type":"object","field":field},"value":to,"expected":from}))
                }
                _ => {
                    let field = task_field(p.arg(2), 1)?;
                    let me = session_subject(session)?;
                    scalar_proposal(session, p.arg(0), p.arg(1), json!({"type":"create","key":{"type":"object","field":field},"value":me}))
                }
            }
        }
        "exit" | "quit" => {
            let mut named = w.clone();
            named[0] = "exit".into();
            crate::shell_grammar::parse(&crate::shell_grammar::EXIT, &named)?;
            Plan::Exit
        }
        "key" => crate::keys::shell_plan(&session.workspace, &session.home, &w)?,
        "job" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::JOB, &w)?;
            let action = p.leaf.path[1];
            let positional: &[&str] = match action {
                "post" => &["room", "program"],
                "claim" => &["job"],
                "answer" => &["name", "output"],
                _ => &["name"],
            };
            let mut flags = vec![flag("action", action), flag("dir", ws())];
            for (i, key) in positional.iter().enumerate() {
                if let Some(value) = p.opt(i) { flags.push(flag(*key, value)); }
            }
            for (name, value) in &p.flags {
                if let Some(value) = value { flags.push(flag(&name[2..], value.clone())); }
            }
            client("job", flags)
        }
        "bend" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::BEND, &w)?;
            let mut flags = vec![flag("dir", ws())];
            match p.leaf.path[1] {
                "publish" => {
                    let file = p.arg(1).trim_start_matches('@');
                    session_file(file, "bend source")?;
                    flags.extend([flag("action", "publish"), flag("name", p.arg(0)), flag("source", session.home.join("requests").join(file))]);
                }
                "run" => flags.extend([flag("action", "run"), flag("name", p.arg(0)), flag("object", p.arg(1))]),
                "show" => flags.extend([flag("action", "show"), flag("object", p.arg(0))]),
                "await" => flags.extend([flag("action", "await"), flag("object", p.arg(0)), flag("transaction", p.arg(1))]),
                "deliver" => flags.extend([flag("action", "deliver"), flag("object", p.arg(0)), flag("transaction", p.arg(1))]),
                "settle" => flags.push(flag("action", "settle")),
                "answer" => {
                    let file = p.arg(1).trim_start_matches('@');
                    session_file(file, "answer")?;
                    flags.extend([flag("action", "answer"), flag("slot", p.arg(0)), flag("answer", session.home.join("requests").join(file))]);
                }
                action => flags.extend([flag("action", action), flag("name", p.arg(0))]),
            }
            if p.has("--lose-reply-once") { flags.push(flag("lose-reply-once", "true")); }
            if p.has("--again") { flags.push(flag("again", "true")); }
            for (name, value) in &p.flags {
                if let Some(value) = value { flags.push(flag(&name[2..], value.clone())); }
            }
            client("bend", flags)
        }
        "jobs" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::JOBS, &w)?;
            client("job", vec![flag("action", "list"), flag("dir", ws()), flag("room", p.arg(0))])
        }
        "history" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::HISTORY, &w)?;
            Plan::History { all: p.opt(0).is_some() }
        }
        "keygen" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::KEYGEN, &w)?;
            let keys = session.home.join("keys");
            client("keygen", vec![flag("secret", keys.join(p.arg(0))), flag("public", keys.join(format!("{}.pub", p.arg(0)))), flag("hosted", "yes")])
        }
        "init" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::INIT, &w)?;
            let context = session.home.join("provision").join("birth-context.json");
            if !context.is_file() {
                return Ok(Plan::NotHere(format!(
                    "init needs your provisioning at {} (your sponsor writes it when they provision you); without it this workspace could never create",
                    context.display()
                )));
            }
            let mut flags = vec![flag("action", "init")];
            // A remote session has no Host image; the process already pins
            // the Host digest, which init records.
            if !session.host.as_os_str().is_empty() {
                flags.push(flag("host", session.host.clone()));
            }
            flags.extend([
                flag("config", session.config.clone()),
                flag("key", session.home.join("keys").join(p.arg(0))),
                flag("subject", p.arg(1)),
                flag("birth-context", context),
                flag("namespace-root", session.home.join("namespace")),
                flag("dir", ws()),
            ]);
            // init refuses a subject whose committed next key is not
            // HOME/keys/KEYFILE.next.pub (FIX-IDENTITY), unless --no-prerotation.
            if p.has("--no-prerotation") {
                flags.push(flag("no-prerotation", "true"));
            }
            client("workspace", flags)
        }
        "enroll" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::ENROLL, &w)?;
            let name = p.arg(0);
            let enroll_dir = session.home.join("enroll").join(name);
            match p.leaf.path {
                ["enroll", "plan"] => {
                    // enroll plan NAME KEYFILE|PUBLIC-HEX [NEXT-PUB-HEX COSIGN-HEX | --no-prerotation] [FACTORY-REF]
                    // The next public key and its co-signature are the NEWCOMER's
                    // (their `keygen` / `mini join --key` prints them): never a file
                    // this session home happens to hold (FIX-IDENTITY).
                    let without = p.has("--no-prerotation");
                    let mut extra: Vec<&str> = [p.opt(2), p.opt(3), p.opt(4)].into_iter().flatten().collect();
                    let next = match (extra.first().and_then(|word| hex_bytes(word, 32)), extra.get(1).and_then(|word| hex_bytes(word, 64))) {
                        (Some(next), Some(cosign)) => {
                            extra.drain(0..2);
                            Some((next, cosign))
                        }
                        _ => None,
                    };
                    if extra.len() > 1 {
                        return Err(u.to_owned());
                    }
                    let factory = extra.first().map(|f| f.to_string()).unwrap_or_else(|| "factory".into());
                    ref_name(&factory, "factory reference")?;
                    let mut flags = vec![flag("action", "plan"), flag("sponsor-workspace", ws()), flag("factory-ref", factory), flag("name", name)];
                    let mut writes = vec![];
                    if let Some(public) = hex_bytes(p.arg(1), 32) {
                        // The newcomer keeps the secret; only the public key
                        // enters this session home.
                        let path = session.home.join("keys").join(format!("{name}.pub"));
                        flags.push(flag("new-public-key", path.clone()));
                        writes.push((path, public));
                    } else {
                        session_file(p.arg(1), "key file")?;
                        flags.push(flag("new-key", session.home.join("keys").join(p.arg(1))));
                    }
                    match (next, without) {
                        (Some((next, cosign)), false) => {
                            let next_path = session.home.join("enroll").join(format!("{name}.next.pub"));
                            let cosign_path = session.home.join("enroll").join(format!("{name}.next.cosign"));
                            flags.push(flag("next-public-key", next_path.clone()));
                            flags.push(flag("next-cosign", cosign_path.clone()));
                            writes.push((next_path, next));
                            writes.push((cosign_path, cosign));
                        }
                        (None, true) => flags.push(flag("no-prerotation", "true")),
                        (Some(_), true) => return Err("a next public key and --no-prerotation exclude each other".into()),
                        (None, false) => return Err("enroll plan NAME KEYFILE|PUBLIC-KEY-HEX NEXT-PUBLIC-KEY-HEX COSIGN-HEX: the record commits to the newcomer's next key, and that key is theirs to make; --no-prerotation says you mean to enrol without one".into()),
                    }
                    flags.push(flag("dir", enroll_dir));
                    Plan::Client { command: "enroll".into(), flags, writes }
                }
                ["enroll", "seal"] if p.opt(1).is_some() => {
                    let signature = hex_bytes(p.arg(1), 64)
                        .ok_or("the possession signature is 128 hex digits (from the newcomer's mini join)")?;
                    let path = session.home.join("requests").join(format!("{name}.possession"));
                    Plan::Client { command: "enroll".into(), flags: vec![flag("action", "seal"), flag("dir", enroll_dir), flag("possession-signature", path.clone())], writes: vec![(path, signature)] }
                }
                ["enroll", "welcome"] => {
                    let mut flags = vec![flag("action", "welcome"), flag("dir", enroll_dir)];
                    let context = ws().join("provisions").join(name).join("birth-context.json");
                    if context.is_file() {
                        flags.push(flag("birth-context", context));
                    }
                    client("enroll", flags)
                }
                ["enroll", action] => client("enroll", vec![flag("action", *action), flag("dir", enroll_dir)]),
                _ => return Err(u.to_owned()),
            }
        }
        "credit" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::CREDIT, &w)?;
            let mut flags = vec![flag("action", "balance"), flag("dir", ws())];
            if let Some(account) = p.opt(0) { flags.push(flag("account", account)); }
            client("credit", flags)
        }
        "tariff" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::TARIFF, &w)?;
            let mut flags = vec![flag("action", "tariff"), flag("dir", ws())];
            if p.index_in(&crate::shell_grammar::TARIFF) == 1 {
                flags.push(flag("set", p.arg(2)));
                flags.push(flag("value", p.arg(3)));
            }
            flags.push(flag("room", p.arg(0)));
            client("credit", flags)
        }
        "topup" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::TOPUP, &w)?;
            let mut flags = vec![flag("action", "topup"), flag("dir", ws()), flag("room", p.arg(0)), flag("amount", p.arg(1))];
            if let Some(Some(account)) = p.flag("--account") { flags.push(flag("account", account)); }
            if let Some(whose) = p.opt(2) { flags.push(flag("to", whose)); }
            if p.opt(3).is_some() { flags.push(flag("again", "true")); }
            client("credit", flags)
        }
        "pay" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::PAY, &w)?;
            match p.leaf.path {
                ["pay", action @ ("address" | "status" | "audit")] => {
                    let mut flags = vec![flag("action", *action), flag("dir", ws())];
                    if let Some(account) = p.opt(0) { flags.push(flag("account", account)); }
                    client("pay", flags)
                }
                _ => {
                    // `pay ROOM week|N [--account REF] [again]` (P-CREDIT). A rerun of the same payment
                    // recovers its record; `again` is the member's decision to pay once more.
                    let mut flags = vec![flag("action", "pay"), flag("dir", ws()), flag("room", p.arg(0)), flag("outbox", session.home.join("outbox"))];
                    if p.arg(1) != "week" {
                        decimal(p.arg(1), "amount")?;
                        flags.push(flag("amount", p.arg(1)));
                    }
                    if let Some(Some(account)) = p.flag("--account") { flags.push(flag("account", account)); }
                    if p.opt(2).is_some() { flags.push(flag("again", "true")); }
                    client("credit", flags)
                }
            }
        }
        "provision" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::PROVISION, &w)?;
            let predicate = json_argument(session, p.arg(3), "account predicate")?;
            let factory = p.opt(4).unwrap_or("factory");
            let path = session.home.join("requests").join(format!("provision-{}.json", p.arg(0)));
            Plan::Client { command: "workspace".into(), flags: vec![flag("action", "provision"), flag("dir", ws()), flag("name", p.arg(0)), flag("holder", p.arg(1)),
                flag("funding", p.arg(2)), flag("account-predicate", path.clone()), flag("factory-ref", factory)], writes: vec![request_file(path, &predicate)] }
        }
        "key-status" => {
            crate::shell_grammar::parse(&crate::shell_grammar::KEY_STATUS, &w)?;
            client("key-status", vec![flag("workspace", ws())])
        }
        "adopt-next-key" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::ADOPT_NEXT_KEY, &w)?;
            if p.leaf.path.len() == 2 {
                session_file(p.arg(0), "adoption attempt")?;
                client("adopt-next-key", vec![flag("workspace", ws()), flag("action", "lookup"), flag("attempt", p.arg(0))])
            } else {
                // `adopt-next-key lookup` without its ATTEMPT is a usage error, not a key file named lookup.
                if p.arg(0) == "lookup" {
                    return Err(u.to_owned());
                }
                client("adopt-next-key", vec![flag("workspace", ws()), flag("next-key", session.home.join("keys").join(p.arg(0)))])
            }
        }
        "rotate-key" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::ROTATE_KEY, &w)?;
            client("rotate-key", vec![flag("workspace", ws()), flag("next-key", session.home.join("keys").join(p.arg(0)))])
        }
        "refs" => {
            crate::shell_grammar::parse(&crate::shell_grammar::REFS, &w)?;
            client("workspace", vec![flag("action", "list"), flag("dir", ws())])
        }
        "inspect" | "why" => {
            let p = if verb == "why" { crate::shell_grammar::parse(&crate::shell_grammar::WHY, &w)? } else { crate::shell_grammar::parse(&crate::shell_grammar::INSPECT, &w)? };
            let view = if verb == "why" { "why" } else { p.leaf.path[1] };
            let mut flags = vec![flag("action", "inspect"), flag("dir", ws()), flag("view", view)];
            if let Some(name) = p.opt(0) {
                flags.push(flag("name", name));
            }
            if view == "why" {
                flags.push(flag("refusals", session.home.join("refusals")));
            }
            if p.has("--json") {
                flags.push(flag("json", "true"));
            }
            client("workspace", flags)
        }
        "can" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::CAN, &w)?;
            if p.has("--any") && p.opt(0).is_none() {
                return Err(u.to_owned());
            }
            let mut flags = vec![flag("action", "can"), flag("dir", ws())];
            if let Some(name) = p.opt(0) { flags.push(flag("name", name)); }
            if p.has("--all") { flags.push(flag("all", "true")); }
            if p.has("--any") { flags.push(flag("any", "true")); }
            client("workspace", flags)
        }
        "read" | "describe" => {
            let p = if verb == "read" { crate::shell_grammar::parse(&crate::shell_grammar::READ, &w)? } else { crate::shell_grammar::parse(&crate::shell_grammar::DESCRIBE, &w)? };
            client("workspace", vec![flag("action", verb.clone()), flag("dir", ws()), flag("name", p.arg(0))])
        }
        "import" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::IMPORT, &w)?;
            if p.index_in(&crate::shell_grammar::IMPORT) == 0 {
                if !(p.arg(1).starts_with('{') || p.arg(1).starts_with('@')) {
                    return Err(u.to_owned());
                }
                let value = json_argument(session, p.arg(1), "reference")?;
                let path = session.home.join("inbox").join(format!("{}.json", ref_file(p.arg(0))));
                Plan::Client { command: "workspace".into(), flags: vec![flag("action", "import"), flag("dir", ws()), flag("name", p.arg(0)), flag("from-ref", path.clone())], writes: vec![request_file(path, &value)] }
            } else {
                let mut flags = vec![flag("action", "import"), flag("dir", ws()), flag("name", p.arg(0)), flag("kind", p.arg(1)), flag("target", p.arg(2)), flag("observe-capability", p.arg(3))];
                if let Some(operation) = p.opt(4).filter(|v| *v != "-") {
                    decimal(operation, "operation capability")?;
                    flags.push(flag("operation-capability", operation));
                }
                if let Some(control) = p.opt(5) { flags.push(flag("control-capability", control)); }
                client("workspace", flags)
            }
        }
        "program" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::PROGRAM, &w)?;
            let source = json_argument(session, p.arg(1), "program source")?;
            let predicate = law_argument(session, &[p.arg(2).to_owned()])?;
            let prefix = session.home.join("requests");
            let path = prefix.join(format!("program-{}.json", ref_file(p.arg(0))));
            let lawpath = prefix.join(format!("program-{}-law.json", ref_file(p.arg(0))));
            let mut flags = vec![flag("action", "program-create"), flag("dir", ws()), flag("name", p.arg(0)), flag("source", path.clone()), flag("predicate", lawpath.clone())];
            if let Some(room) = &room { flags.push(flag("in", room)); }
            Plan::Client { command: "workspace".into(), flags, writes: vec![request_file(path, &source), request_file(lawpath, &predicate)] }
        }
        "kind" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::KIND, &w)?;
            match p.leaf.path {
                ["kind", "show"] => client("workspace", vec![flag("action", "kind-show"), flag("dir", ws()), flag("name", p.arg(0))]),
                ["kind", "create"] => {
                    let definition = json_argument(session, p.arg(1), "kind definition")?;
                    let predicate = law_argument(session, &[p.arg(2).to_owned()])?;
                    let prefix = session.home.join("requests");
                    let defpath = prefix.join(format!("kind-{}.json", ref_file(p.arg(0))));
                    let lawpath = prefix.join(format!("kind-{}-law.json", ref_file(p.arg(0))));
                    let mut flags = vec![flag("action", "kind-create"), flag("dir", ws()), flag("name", p.arg(0)), flag("definition", defpath.clone()), flag("predicate", lawpath.clone())];
                    if let Some(room) = &room { flags.push(flag("in", room)); }
                    Plan::Client { command: "workspace".into(), flags, writes: vec![request_file(defpath, &definition), request_file(lawpath, &predicate)] }
                }
                ["kind", "construct"] => {
                    let parents = json_argument(session, p.arg(3), "ordered parent reference names")?;
                    let parent_path = session.home.join("requests").join(format!("construct-{}.json", ref_file(p.arg(0))));
                    Plan::Client { command: "workspace".into(), flags: vec![flag("action", "kind-construct"), flag("dir", ws()), flag("proposal-id", p.arg(0)), flag("name", p.arg(1)),
                        flag("program", p.arg(2)), flag("parents", parent_path.clone())], writes: vec![request_file(parent_path, &parents)] }
                }
                _ => {
                    let definition = json_argument(session, p.arg(2), "kind definition")?;
                    proposal(session, p.arg(0), &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                        "targets":[{"name":p.arg(1),"payload":{"type":"kindDefinition","definition":definition}}]}))
                }
            }
        }
        "instance" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::INSTANCE, &w)?;
            match p.leaf.path {
                ["instance", "show"] => client("workspace", vec![flag("action", "instance-show"), flag("dir", ws()), flag("name", p.arg(0))]),
                ["instance", "call"] => {
                    let mut flags = vec![flag("action", "instance-call"), flag("dir", ws()), flag("proposal-id", p.arg(0)), flag("name", p.arg(1)), flag("method", p.arg(2))];
                    match (p.flag("--fund").flatten(), p.flag("--max-compute-credits").flatten()) {
                        (None, None) => {}
                        (Some(fund), Some(max)) => { flags.push(flag("fund", fund)); flags.push(flag("max-compute-credits", max)); }
                        _ => return Err("--fund and --max-compute-credits must be supplied together".into()),
                    }
                    client("workspace", flags)
                }
                ["instance", operation @ ("set" | "erase")] => {
                    let mut action = json!({"type":operation,"field":p.arg(2),"key":p.arg(3)});
                    if *operation == "set" { action["value"] = json!(p.arg(4)); }
                    proposal(session, p.arg(0), &json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                        "targets":[{"name":p.arg(1),"payload":{"type":"worldNamed","actions":[action]}}]}))
                }
                _ => return Err(u.to_owned()),
            }
        }
        "create" if birth.from.is_some() => {
            arity(&w, 2, 2, u)?; ref_name(&w[1], "instance name")?;
            if birth.owner.is_some() { return Err("create --from currently creates for the signing member".into()); }
            let predicate = law_argument(session, &w[2..3])?;
            let path = session.home.join("requests").join(format!("create-{}.json",ref_file(&w[1])));
            let mut flags = vec![flag("action", "instance-create"),flag("dir",ws()),flag("name",&w[1]),
                flag("from",birth.from.as_ref().expect("matched")),flag("predicate",path.clone())];
            if let Some(room) = &room { flags.push(flag("in",room)); }
            Plan::Client { command:"workspace".into(),flags,writes:vec![request_file(path,&predicate)] }
        }
        "create" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::CREATE, &w)?;
            let predicate = law_argument(session, &[p.arg(2).to_owned()])?;
            let path = session.home.join("requests").join(format!("create-{}.json", ref_file(p.arg(0))));
            let mut flags = vec![flag("action", "create"), flag("dir", ws()), flag("name", p.arg(0)), flag("storage", p.arg(1)), flag("predicate", path.clone())];
            // `create NAME declared LAW FIELDS`: the fields the cell may hold
            // (`0-3,7` or `open`); without it a declared cell holds none.
            if let Some(fields) = p.opt(3) {
                crate::workspace::parse_fields(fields)?;
                flags.push(flag("fields", fields));
            }
            if let Some(room) = &room {
                flags.push(flag("in", room.clone()));
            }
            if let Some(owner) = &birth.owner {
                flags.push(flag("owner", owner.clone()));
            }
            Plan::Client { command: "workspace".into(), flags, writes: vec![request_file(path, &predicate)] }
        }
        "propose" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::PROPOSE, &w)?;
            let request = json_argument(session, p.arg(1), "request")?;
            proposal(session, p.arg(0), &request)
        }
        "invoke" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::INVOKE, &w)?;
            let scalar = if p.arg(2) == "create" {
                json!({"type":"create","key":{"type":"object","field":p.arg(3)},"value":p.arg(4)})
            } else {
                json!({"type":"write","key":{"type":"object","field":p.arg(3)},"value":p.arg(4),"expected":p.arg(5)})
            };
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                "targets":[{"name":p.arg(1),"payload":{"type":"scalar","actions":[scalar]}}]});
            proposal(session, p.arg(0), &request)
        }
        "delegate" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::DELEGATE, &w)?;
            let verbs: Vec<&str> = p.arg(3).split(',').collect();
            // A read is judged with a cost (its encoded intent's length), and a grant covers it only
            // while cost <= MAX-COST: an observe grant at 0 covers no read, so its holder is refused
            // `no-grant` on everything. Named here so the trap cannot be typed (the publish form's
            // ceiling is deploy/demo-seed/public-read-max-cost).
            if verbs.contains(&"observe") && p.arg(4).bytes().all(|b| b == b'0') {
                return Err("a ceiling of 0 covers no read: an observe grant needs a MAX-COST above 0 (every signed read costs its encoded length); give a MAX-COST at or above the value in deploy/demo-seed/public-read-max-cost".into());
            }
            let mut request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                "name":p.arg(1),"recipient":p.arg(2),"verbs":verbs,"maxCost":p.arg(4)});
            if let Some(Some(height)) = p.flag("--until") {
                request["notAfter"] = json!(height);
            }
            proposal(session, p.arg(0), &request)
        }
        "market" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::MARKET, &w)?;
            match p.leaf.path {
                ["market", "open"] => client("workspace", vec![flag("action", "market-open"), flag("dir", ws()), flag("name", p.arg(0)), flag("close", p.arg(1)), flag("reveal-end", p.arg(2)), flag("supply", p.arg(3))]),
                _ => {
                    let id = p.opt(1).map(str::to_owned).unwrap_or_else(|| format!("settle-{}", p.arg(0)));
                    client("workspace", vec![flag("action", "market-settle"), flag("dir", ws()), flag("name", p.arg(0)), flag("proposal-id", id)])
                }
            }
        }
        "apps" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::APPS, &w)?;
            let action = p.leaf.path[1];
            let mut flags = vec![flag("action", if action == "retry" { "install" } else { action }), flag("dir", ws())];
            if p.has("--json") { flags.push(flag("json", "yes")); }
            match action {
                "search" => {
                    if let Some(category) = p.flag("--category").flatten() { flags.push(flag("category", category)); }
                    if let Some(term) = p.opt(0) { flags.push(flag("term", term)); }
                }
                "show" => flags.push(flag("app", p.arg(0))),
                "install" => {
                    flags.push(flag("app", p.arg(0)));
                    flags.push(flag("home", session.home.clone()));
                    if let Some(class) = p.flag("--class").flatten() { flags.push(flag("class", class)); }
                }
                "retry" => flags.push(flag("retry", p.arg(0))),
                "list" => {}
                "share" | "export" | "revoke-identity" => {
                    if !crate::apps::valid_grain(p.arg(0)) { return Err(u.to_owned()); }
                    flags.push(flag("grain", p.arg(0)));
                    flags.push(flag(match action { "share" => "to", "export" => "out", _ => "token" }, p.arg(1)));
                }
                _ => {
                    if !crate::apps::valid_grain(p.arg(0)) { return Err(u.to_owned()); }
                    flags.push(flag("grain", p.arg(0)));
                }
            }
            client("apps", flags)
        }
        "bid" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::BID, &w)?;
            let id = p.opt(3).map(str::to_owned).unwrap_or_else(|| format!("bid-{}", p.arg(0)));
            client("workspace", vec![flag("action", "market-bid"), flag("dir", ws()), flag("name", p.arg(0)), flag("price", p.arg(1)), flag("qty", p.arg(2)), flag("proposal-id", id)])
        }
        "reveal" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::REVEAL, &w)?;
            let id = p.opt(1).map(str::to_owned).unwrap_or_else(|| format!("reveal-{}", p.arg(0)));
            client("workspace", vec![flag("action", "market-reveal"), flag("dir", ws()), flag("name", p.arg(0)), flag("proposal-id", id)])
        }
        "bids" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::BIDS, &w)?;
            client("workspace", vec![flag("action", "market-bids"), flag("dir", ws()), flag("name", p.arg(0))])
        }
        "law" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::LAW, &w)?;
            match p.leaf.path {
                ["law", "show"] => client("workspace", vec![flag("action", "law-show"), flag("dir", ws()), flag("name", p.arg(0))]),
                ["law", "export", "show"] => client("workspace", vec![flag("action", "law-export-show"), flag("dir", ws()), flag("name", p.arg(0))]),
                ["law", "export"] => {
                    let component = if p.arg(2) == "none" { Value::Null } else { json_argument(session, p.arg(2), "descendant law component")? };
                    proposal(session, p.arg(0), &json!({"type":"minidregg-workspace-proposal-v1","action":"install-export","name":p.arg(1),"component":component}))
                }
                ["law", "check"] => {
                    let law = if p.arg(0) == "-" { law_from_stdin()? } else { law_argument(session, &[p.arg(0).to_owned()])? };
                    let bytes = serde_json::to_vec(&law).expect("JSON values serialise");
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    std::hash::Hasher::write(&mut hasher, &bytes);
                    let name = format!("law-check-{:016x}.json", std::hash::Hasher::finish(&hasher));
                    let path = session.home.join("requests").join(name);
                    Plan::Client { command: "workspace".into(), flags: vec![flag("action", "law-check"), flag("dir", ws()), flag("predicate", path.clone())], writes: vec![request_file(path, &law)] }
                }
                _ => {
                    // Explicit consent switches cover unsatisfiability, self-lockout and frozen membership.
                    let predicate = law_argument(session, &[p.arg(2).to_owned()])?;
                    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":p.arg(1),"predicate":predicate});
                    let mut plan = proposal(session, p.arg(0), &request);
                    let chat_room = crate::chat::load_room(session, p.arg(1)).is_ok();
                    if let Plan::Client { flags, .. } = &mut plan {
                        if p.has("--allow-unsatisfiable") { flags.push(flag("allow-unsatisfiable", "true")); }
                        if p.has("--freeze-roster") { flags.push(flag("freeze-roster", "true")); }
                        if chat_room { flags.push(flag("room-cell", "true")); }
                        if p.has("--i-lock-myself-out") { flags.push(flag("i-lock-myself-out", "true")); }
                    }
                    plan
                }
            }
        }
        "submit" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::SUBMIT, &w)?;
            if p.has("--lose-reply-once") {
                std::env::set_var(mini_sdk::operator::LOSE_REPLY_ENV, mini_sdk::flow::Request::Submit.operation().to_string());
            }
            client("workspace", vec![flag("action", "submit"), flag("dir", ws()),
                flag("intent", ws().join("proposals").join(p.arg(0)).join("intent.json")), flag("attempt", ws().join("attempts").join(p.arg(0)))])
        }
        "lookup" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::LOOKUP, &w)?;
            client("workspace", vec![flag("action", "recover"), flag("dir", ws()), flag("attempt", ws().join("attempts").join(p.arg(0)))])
        }
        "attempt" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::ATTEMPT, &w)?;
            client("attempt-state", vec![flag("attempt", ws().join("attempts").join(p.arg(0)))])
        }
        "retry" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::RETRY, &w)?;
            client("retry", vec![flag("attempt", ws().join("attempts").join(p.arg(0))), flag("mode", "submit")])
        }
        "publish" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::PUBLISH, &w)?;
            client("workspace", vec![flag("action", "publish-delegation"), flag("dir", ws()), flag("proposal-id", p.arg(0)), flag("attempt", ws().join("attempts").join(p.arg(0)))])
        }
        "export" => {
            let p = crate::shell_grammar::parse(&crate::shell_grammar::EXPORT, &w)?;
            if p.leaf.path == ["export", "world"] {
                let name = p.opt(0).unwrap_or("world.tar");
                if !crate::shell_grammar::is_session_file(name) {
                    return Err("export world NAME: a plain file name (letters, digits, '-', '_', '.'; no leading dot), written under HOME/exports".into());
                }
                return Ok(client("export-world", vec![flag("workspace", ws()), flag("home", session.home.clone()), flag("out", session.home.join("exports").join(name))]));
            }
            Plan::Export(ws().join("proposals").join(p.arg(0)).join("recipient-reference.json"))
        }
        other => return Err(format!("unknown verb {other}; type help")),
    })
}

// ---------------------------------------------------------------- verdicts

/// How one verb ended, before rendering.
#[derive(Debug)]
pub(crate) enum Ending {
    Done,
    Usage(String),
    /// The client returned an error and the Host recorded no decision.
    Client(String),
    /// The Host decided. `decoded` is the Host's own `inspect outcome` of the
    /// retained frame, or why it could not be decoded.
    Host {
        client: String,
        decision: HostDecision,
        decoded: Option<std::result::Result<Value, String>>,
        evidence: Option<PathBuf>,
    },
    /// A chat verb's own ending: (exit code, stderr text).
    Rendered(i32, String),
    /// A refused `doc push` whose pinned lines changed since the pull: the
    /// line diagnosis, above the Host's own refusal (`host`).
    LineRefused { lines: String, host: Box<Ending> },
}

fn hex_text(value: Option<&Value>) -> String {
    let Some(hex) = value.and_then(Value::as_str) else {
        return "(absent)".into();
    };
    let bytes: Option<Vec<u8>> = mini_sdk::hex::decode(hex).ok();
    match bytes.and_then(|b| String::from_utf8(b).ok()) {
        Some(text) if !text.chars().any(char::is_control) => format!("{text:?}"),
        _ => format!("hex {hex}"),
    }
}

fn outcome_line(outcome: &Value) -> (i32, String) {
    if let Some(line) = super::charged_line(outcome) {
        return (EXIT_REFUSED, line);
    }
    match outcome.get("type").and_then(Value::as_str) {
        Some("refused") => (
            EXIT_REFUSED,
            super::refusal_line(outcome).unwrap_or_else(|| "refused: unnamed".into()),
        ),
        Some(kind @ ("uncertain" | "unavailable")) => (
            EXIT_UNDECIDED,
            format!(
                "undecided: Host outcome {kind}, detail {}; the attempt is retained, `lookup ID` asks again",
                hex_text(outcome.get("detail"))
            ),
        ),
        Some(kind @ ("contention" | "absent")) => (
            EXIT_UNDECIDED,
            format!("undecided: Host outcome {kind}; the attempt is retained, `lookup ID` asks again"),
        ),
        Some(kind) => (EXIT_UNDECIDED, format!("undecided: Host outcome type {kind}")),
        None => (EXIT_UNDECIDED, "undecided: Host outcome has no type".into()),
    }
}

/// Render an ending as (exit code, stderr text). Every non-success line
/// starts with one of `usage:`, `error:`, `refused:` or `undecided:`; the
/// client's own message follows verbatim.
pub(crate) fn render(ending: &Ending) -> (i32, String) {
    match ending {
        Ending::Done => (EXIT_OK, String::new()),
        Ending::LineRefused { lines, host } => {
            let (code, text) = render(host);
            (code, format!("refused: stale-line: {lines}\n{text}"))
        }
        Ending::Usage(message) => (EXIT_USAGE, format!("usage: {message}\n")),
        Ending::Client(message) => (EXIT_CLIENT, format!("error: {message}\n")),
        Ending::Rendered(code, text) => (*code, text.clone()),
        Ending::Host { client, decision, decoded, evidence } => {
            let mut text = String::new();
            let code = match decision {
                HostDecision::Outcome(outcome) => {
                    let (code, line) = outcome_line(outcome);
                    text.push_str(&line);
                    text.push('\n');
                    text.push_str(&format!("  outcome: {outcome}\n"));
                    code
                }
                // The class is the DECODED outcome's, never the reply byte's: Lean answers 255
                // for `unavailable` and thrown handlers too (`HostDecision::is_refusal`), and an
                // undecoded frame decides nothing. Only a decoded `refused` exits 3.
                HostDecision::Frame { command, byte, encoded, .. } => {
                    let code = match decoded {
                        // 254 is the socket's, judged before the Host write: certainly never sent.
                        _ if *byte == super::host_operations_never_forwarded() => {
                            text.push_str(&format!(
                                "refused: not sent: {command} was never forwarded to the Host (reply byte {byte}); nothing happened\n"
                            ));
                            EXIT_REFUSED
                        }
                        // NO_RECORD (253): decided before any append, a refusal whatever the type.
                        Some(Ok(outcome)) if *byte == crate::RESPONSE_NO_RECORD => {
                            text.push_str(&format!("{} (Host refused {command} with no record, reply byte {byte})\n",
                                super::no_record_line(Some(outcome))));
                            text.push_str(&format!("  outcome (decoded by the Host): {outcome}\n"));
                            EXIT_REFUSED
                        }
                        // HOST_OUTCOME (255): undecided whatever it decodes to.
                        Some(Ok(outcome)) if *byte == crate::RESPONSE_HOST_OUTCOME => {
                            text.push_str(&format!(
                                "undecided: Host answered {command} with reply byte {byte} and outcome {}; \
                                 the attempt is retained, `lookup ID` asks again\n", super::outcome_type(Some(outcome))));
                            text.push_str(&format!("  outcome (decoded by the Host): {outcome}\n"));
                            EXIT_UNDECIDED
                        }
                        Some(Ok(outcome)) => {
                            let (code, line) = outcome_line(outcome);
                            if code == EXIT_REFUSED {
                                text.push_str(&format!("{line} (Host refused {command}, reply byte {byte})\n"));
                            } else {
                                text.push_str(&format!("{line} (Host answered {command} with reply byte {byte})\n"));
                            }
                            text.push_str(&format!("  outcome (decoded by the Host): {outcome}\n"));
                            code
                        }
                        Some(Err(why)) => {
                            text.push_str(&format!(
                                "undecided: Host answered {command} with reply byte {byte} and could not decode the frame: {why}; \
                                 the attempt is retained, `lookup ID` asks again\n"
                            ));
                            EXIT_UNDECIDED
                        }
                        None => {
                            text.push_str(&format!(
                                "undecided: Host answered {command} with reply byte {byte}, undecoded; \
                                 the attempt is retained, `lookup ID` asks again\n"
                            ));
                            EXIT_UNDECIDED
                        }
                    };
                    text.push_str(&format!("  encoded: {}\n", super::hex(encoded)));
                    code
                }
            };
            if let Some(path) = evidence {
                text.push_str(&format!("  evidence: {}\n", path.display()));
            }
            text.push_str(&format!("  client: {client}\n"));
            (code, text)
        }
    }
}

// ---------------------------------------------------------------- execution

/// Create a request file once. An identical file already present is the same
/// request (a retried line); different content under the same name is refused.
fn write_once(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        crate::fsio::ensure_private_dir(parent)?;
    }
    crate::fsio::retain_exact(path, bytes, || {
        format!("{} already holds a different request; choose a new ID", path.display())
    })
    .map(|_| ())
}

/// Retain a refused frame under HOME/refusals and ask the Host to decode it
/// with its own outcome codec (`inspect outcome`).
fn decode_refusal(session: &Session, command: &str, encoded: &[u8]) -> (Option<PathBuf>, std::result::Result<Value, String>) {
    let dir = session.home.join("refusals");
    if let Err(e) = crate::fsio::ensure_private_dir(&dir) {
        return (None, Err(e));
    }
    let stem = format!(
        "{}-{}-{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0),
        command.replace(|c: char| !c.is_ascii_alphanumeric(), "-"),
        match crate::fsio::random::<8>() {
            Ok(bytes) => super::hex(&bytes),
            Err(e) => return (None, Err(e)),
        }
    );
    let bin = dir.join(format!("{stem}.bin"));
    let json = dir.join(format!("{stem}.json"));
    if let Err(e) = write_once(&bin, encoded) {
        return (None, Err(e));
    }
    prune_refusals(&dir, KEPT_REFUSALS);
    (Some(bin.clone()), super::inspect(&session.host, &session.config, "outcome", &bin, &json))
}

/// Retained refusals a session keeps (each a `.bin` and its decoded `.json`).
const KEPT_REFUSALS: usize = 256;

/// Keep the newest `keep` refusals in `dir`. Names start with the unix second, so name order is
/// age order; the oldest pairs are removed. A long-lived session's refusals no longer grow
/// without bound (HCLOUD-GAP #17). Best effort: a failure here never hides the refusal itself.
fn prune_refusals(dir: &Path, keep: usize) {
    let Ok(entries) = fs::read_dir(dir) else { return };
    let mut stems: Vec<String> = entries
        .filter_map(|e| e.ok()?.file_name().into_string().ok())
        .filter_map(|name| name.strip_suffix(".bin").map(str::to_owned))
        .collect();
    stems.sort();
    let over = stems.len().saturating_sub(keep);
    for stem in &stems[..over] {
        let _ = fs::remove_file(dir.join(format!("{stem}.bin")));
        let _ = fs::remove_file(dir.join(format!("{stem}.json")));
    }
}

/// The session's own folders, then the confinement of every path a line hands
/// the client inside the session home: real directories down from the home and
/// no link or special file at the leaf. Paths outside the home are the
/// deployment's (Host, config, the sponsor's workspace), never a friend's argument.
///
/// The folders come FIRST: confinement walks every directory from the home down,
/// so on a fresh home (no `keys/` yet) `keygen mini.key` was refused as
/// "cannot open session directory" before the shell created the folder it was
/// about to use. Each folder is created from the held home descriptor,
/// owner-private, and refused unless it is a directory of this user
/// (`session_fs::private_folder`): the standard `keys` and `enroll`, and the
/// first component of every request the line writes.
fn admit_session_paths(session: &Session, flags: &[(String, OsString)], writes: &[(PathBuf, Vec<u8>)]) -> Result<()> {
    let mut folders = vec!["keys".to_owned(), "enroll".to_owned()];
    // Any flag naming a file under the home (`--out`'s export, `room concierge`'s program in
    // HOME/concierge/, an outbox) gets its first folder as a request does.
    let flagged = flags.iter().map(|(_, value)| PathBuf::from(value));
    for path in writes.iter().map(|(path, _)| path.clone()).chain(flagged) {
        if let Ok(relative) = path.strip_prefix(&session.home) {
            let mut parts = relative.components();
            if let (Some(std::path::Component::Normal(first)), Some(_)) = (parts.next(), parts.next()) {
                let first = first.to_str().ok_or_else(|| format!("{}: session folder is not UTF-8", path.display()))?;
                if !folders.iter().any(|f| f == first) {
                    folders.push(first.to_owned());
                }
            }
        }
    }
    for folder in &folders {
        session_fs::private_folder(&session.home, folder)?;
    }
    for path in writes.iter().map(|(path, _)| path.as_os_str()).chain(flags.iter().map(|(_, value)| value.as_os_str())) {
        let path = Path::new(path);
        if path.starts_with(&session.home) {
            session_fs::confined(&session.home, path).map_err(|e| format!("{}: {e}", path.display()))?;
        }
    }
    Ok(())
}

fn execute(session: &Session, plan: Plan) -> Ending {
    let Plan::Client { command, flags, writes } = plan else {
        return Ending::Done;
    };
    if let Err(e) = admit_session_paths(session, &flags, &writes) {
        return Ending::Client(e);
    }
    for (path, bytes) in &writes {
        if let Err(e) = write_once(path, bytes) {
            return Ending::Client(e);
        }
    }
    // The retained attempt this command works on, when it names one: an uncertain transmission
    // (the reply never read) is then an undecided ending that names the lookup, not a client error.
    let attempt_id = flags.iter().find(|(name, _)| name == "attempt").and_then(|(_, value)| Path::new(value).file_name().map(|n| n.to_string_lossy().into_owned()));
    let args = Args {
        command: OsString::from(&command),
        values: flags
            .into_iter()
            .map(|(name, value)| (OsString::from(format!("--{name}")), value))
            .collect(),
    };
    let _ = super::take_command_ending();
    let _ = super::take_host_decision();
    let _ = super::replan::take_count();
    let _ = super::take_line_refusal();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::run(args)))
        .unwrap_or_else(|_| Err("the client panicked; see the message above".into()));
    let _ = io::stdout().flush();
    // The cost of the timer race, visible: how often this command observed again.
    let replanned = super::replan::take_count();
    if result.is_ok() && replanned > 0 {
        eprintln!("(re-planned {replanned}×)");
    }
    let decision = super::take_host_decision();
    if let Some(ending) = super::take_command_ending() {
        let (code, message) = ending.render();
        return Ending::Rendered(i32::from(code), message);
    }
    match (result, decision) {
        (Ok(()), _) => Ending::Done,
        (Err(client), None) if client.starts_with("uncertain host") && attempt_id.is_some() => Ending::Rendered(
            EXIT_UNDECIDED,
            format!("undecided: {client}; the attempt is retained, `lookup {}` asks again\n", attempt_id.unwrap_or_default()),
        ),
        (Err(client), None) => Ending::Client(client),
        (Err(client), Some(decision)) => {
            let (evidence, decoded) = match &decision {
                HostDecision::Frame { command, encoded, .. } => {
                    let (path, decoded) = decode_refusal(session, command, encoded);
                    (path, Some(decoded))
                }
                HostDecision::Outcome(_) => (None, None),
            };
            let host = Ending::Host { client, decision, decoded, evidence };
            match super::take_line_refusal() {
                Some(lines) => Ending::LineRefused { lines, host: Box::new(host) },
                None => host,
            }
        }
    }
}

fn read_json(path: &Path) -> Option<Value> {
    let bytes = fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

fn whoami(session: &Session) {
    let pin = read_json(&session.workspace.join("workspace.json"));
    let value = json!({"type":"minidregg-shell-session-v1",
        "workspace":session.workspace,"home":session.home,
        "initialized":pin.is_some(),
        "subject":pin.as_ref().and_then(|p| p.get("subject")).cloned(),
        "socket":pin.as_ref().and_then(|p| p.get("socket")).cloned(),
        "encryptionKey":pin.as_ref().and_then(|p| p.get("key")).and_then(Value::as_str)
            .and_then(|key| crate::workspace::roomkey::enc_key_id_hex(Path::new(key)).ok()),
        "authority":"discovery-only"});
    println!("{}", serde_json::to_string_pretty(&value).expect("JSON renders"));
}

fn attempt_status(dir: &Path) -> (bool, String) {
    let mut outcomes: Vec<String> = fs::read_dir(dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok()?.file_name().into_string().ok())
                .filter(|n| n == "outcome.json" || (n.starts_with("retry-") && n.ends_with(".json")))
                .collect()
        })
        .unwrap_or_default();
    outcomes.sort();
    if let Some(last) = outcomes.last() {
        if let Some(o) = read_json(&dir.join(last)) {
            let s = |k: &str| o.get(k).and_then(Value::as_str).unwrap_or("-").to_owned();
            return (
                true,
                format!(
                    "{} {} acceptedCount={} tx={} ({} of {} outcome files)",
                    s("type"),
                    s("confirmation"),
                    s("acceptedCount"),
                    s("transactionId"),
                    last,
                    outcomes.len()
                ),
            );
        }
    }
    if let Some(r) = read_json(&dir.join("pre-submit-refusal.json")) {
        let stage = r.get("stage").and_then(Value::as_str).unwrap_or("-");
        return (true, format!("refused before a call existed (stage {stage})"));
    }
    if dir.join("call.bin").is_file() {
        return (true, "signed call retained, no outcome (use lookup or retry)".into());
    }
    if dir.join("signed-observation.bin").is_file() {
        return (false, "signed read".into());
    }
    (false, "incomplete (no call, no outcome)".into())
}

fn history(session: &Session, all: bool) {
    let mut rows: Vec<(std::time::SystemTime, String)> = Vec::new();
    if let Ok(entries) = fs::read_dir(session.workspace.join("attempts")) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let modified = entry.metadata().and_then(|m| m.modified()).unwrap_or(std::time::UNIX_EPOCH);
            let (interesting, status) = attempt_status(&entry.path());
            if all || interesting {
                rows.push((modified, format!("attempt\t{name}\t{status}")));
            }
        }
    }
    if let Ok(entries) = fs::read_dir(session.home.join("enroll")) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let modified = entry.metadata().and_then(|m| m.modified()).unwrap_or(std::time::UNIX_EPOCH);
            let status = match read_json(&entry.path().join("enrollment.json")) {
                Some(e) => format!(
                    "enrolled subject={} acceptedCount={}",
                    e.get("subject").and_then(Value::as_str).unwrap_or("-"),
                    e.pointer("/receipt/acceptedCount").and_then(Value::as_str).unwrap_or("-")
                ),
                None if entry.path().join("submit-marker.json").exists() => {
                    "submitted, no result retained (use enroll lookup)".into()
                }
                None if entry.path().join("seal.json").exists() => "sealed, not submitted".into(),
                None => "planned".into(),
            };
            rows.push((modified, format!("enroll\t{name}\t{status}")));
        }
    }
    rows.sort();
    println!("# local retained evidence, oldest first; authority: discovery-only");
    for (_, row) in rows {
        println!("{row}");
    }
}

/// The delegated references delivered to this session (`import` keeps each
/// one in HOME/inbox): who it is addressed to and whether it is a reference
/// in the workspace now. Discovery only; the Host checks every grant at use.
/// Room joins delivered before this member's workspace existed: the operator's enrolment
/// (deploy's mini-reenroll: the member's feedback room) writes HOME/inbox/NAME.join, one shell line
/// `chat join ROOM INVITATION`, when there is no workspace yet to join with. The first `init` that
/// succeeds applies each, in name order, through the same `chat join` a typed line runs (nothing
/// else: a file holding any other line is refused, never run). A join that lands renames its file
/// NAME.joined; a refused one stays NAME.join, so the member can see it and type it again. One line
/// says what happened.
fn apply_pending_joins(session: &Session) {
    let inbox = session.home.join("inbox");
    let Ok(entries) = fs::read_dir(&inbox) else { return };
    let mut files: Vec<PathBuf> = entries
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().and_then(|e| e.to_str()) == Some("join"))
        .collect();
    if files.is_empty() {
        return;
    }
    files.sort();
    let (mut joined, mut refused) = (Vec::new(), Vec::new());
    for path in files {
        let name = path.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let text = match session_fs::read(&inbox, &path, 1 << 20).map(|bytes| String::from_utf8(bytes)) {
            Ok(Ok(text)) => text.trim().to_owned(),
            _ => {
                refused.push(format!("{name} (unreadable)"));
                continue;
            }
        };
        let words: Vec<&str> = text.split_whitespace().collect();
        if text.contains('\n') || words.get(..2) != Some(&["chat", "join"][..]) {
            refused.push(format!("{name} (not one `chat join` line)"));
            continue;
        }
        match plan(session, &text) {
            Ok(Plan::Chat(join @ crate::chat::Line::Join { .. })) => {
                let room = words.get(2).copied().unwrap_or_default().to_owned();
                match crate::chat::run(session, join) {
                    (EXIT_OK, _) => {
                        let _ = fs::rename(&path, path.with_extension("joined"));
                        joined.push(room);
                    }
                    (_, why) => refused.push(format!("{name} ({})", why.trim().lines().next().unwrap_or("refused"))),
                }
            }
            Ok(_) => refused.push(format!("{name} (not one `chat join` line)")),
            Err(why) => refused.push(format!("{name} ({})", why.trim().lines().next().unwrap_or("does not plan"))),
        }
    }
    println!(
        "init: pending joins from HOME/inbox: joined {}{}",
        if joined.is_empty() { "none".to_owned() } else { joined.join(", ") },
        if refused.is_empty() { String::new() } else { format!("; refused {} (each stays .join; type it again)", refused.join(", ")) }
    );
}

fn inbox(session: &Session) {
    let me = session_subject(session).ok();
    let mut names: Vec<String> = stems(&session.home.join("inbox"), ".json", |_| false)
        .iter()
        .map(|stem| crate::workspace::ref_name_of_file(stem))
        .collect();
    names.sort();
    println!("# delivered references (HOME/inbox); authority: discovery-only");
    for name in names {
        let Some(value) = read_json(&session.home.join("inbox").join(format!("{}.json", ref_file(&name)))) else {
            println!("{name}	unreadable");
            continue;
        };
        let field = |k: &str| value.get(k).and_then(Value::as_str).unwrap_or("-").to_owned();
        let recipient = field("recipient");
        let to_me = if me.as_deref() == Some(recipient.as_str()) { "to me" } else { "not to me" };
        let imported = session.workspace.join("refs").join(format!("{}.json", ref_file(&name))).is_file();
        println!(
            "{name}	{} {} capability {}	recipient {recipient} ({to_me})	{}",
            field("kind"),
            field("target"),
            field("capability"),
            if imported { "imported" } else { "not imported" }
        );
    }
}

/// The workspace references that are rooms: founded here (`room new`, the
/// template) or an imported room invite (`member`). Discovery only.
fn rooms(session: &Session) {
    let refs = session.workspace.join("refs");
    let mut names: Vec<String> = stems(&refs, ".json", |_| false)
        .iter()
        .map(|stem| crate::workspace::ref_name_of_file(stem))
        .collect();
    names.sort();
    println!("# rooms (WORKSPACE/refs); authority: discovery-only");
    for name in names {
        let Some(value) = read_json(&refs.join(format!("{}.json", ref_file(&name)))) else {
            continue;
        };
        let Some(room) = value.get("room").and_then(Value::as_str) else {
            continue;
        };
        let field = |k: &str| value.get(k).and_then(Value::as_str).unwrap_or("-").to_owned();
        let private = if value.get("private").is_some() { "\tprivate" } else { "" };
        println!("{name}\t{room}\t{} {}\tcapability {}{private}", field("kind"), field("target"),
            field("operationCapability"));
    }
}

fn help_text(topic: Option<&str>) -> String {
    match topic {
        Some("chat") => crate::chat::HELP.to_owned(),
        Some("story") => crate::story::HELP.to_owned(),
        Some(name) => match command_catalog().find(|v| v.name == name) {
            Some(v) => format!("{}\n  = {}\n", v.usage, v.operation),
            None => format!("no verb {name}\n"),
        },
        None => {
            let mut text = format!("{HOSTED_CUSTODY_BANNER}\n");
            text.push_str("Every verb is one client operation; the Host decides. Words: 'literal', \"escaped\", {json} or [json], @FILE (HOME/requests/FILE).\n");
            for v in command_catalog() {
                text.push_str(&format!("  {:<10} {}\n", v.name, v.usage));
            }
            text.push_str("Endings on stderr: usage: (2)  error: client (1)  refused: Host (3)  undecided: Host (4).\n");
            text
        }
    }
}

/// What an interactive session prints (to stderr) before its first prompt.
fn start_text(session: &Session) -> String {
    format!(
        "{HOSTED_CUSTODY_BANNER}\nmini shell: workspace {}. Type home to find your work; help lists commands.\n",
        session.workspace.display()
    )
}

/// Whether the verb's grammar accepts the line's words (as split words, or as a raw line for
/// the verbs that read one); a verb without a grammar accepts nothing here.
fn grammar_accepts(text: &str) -> bool {
    let Ok(w) = words(text) else { return false };
    let Some(verb) = w.first() else { return false };
    let Some(g) = crate::shell_grammar::grammar(verb) else { return false };
    crate::shell_grammar::parse(g, &w).is_ok() || crate::shell_grammar::parse_line(g, text).is_ok()
}

/// A plan as one line of words: the client command and its flag names (values elided), or the
/// local plan's kind. What `--plan` prints; never the secrets a flag may carry.
fn describe_plan(planned: &Plan) -> String {
    match planned {
        Plan::Client { command, flags, writes } => format!(
            "client {command} {}{}",
            flags.iter().map(|(name, _)| format!("--{name}")).collect::<Vec<_>>().join(" "),
            if writes.is_empty() { String::new() } else { format!(" (+{} request file(s))", writes.len()) }
        ),
        other => {
            let text = format!("{other:?}");
            text.split(|c: char| c == '{' || c == '(').next().unwrap_or("local").trim().to_owned()
        }
    }
}

/// Run one line; returns (exit code, keep going).
pub(crate) fn line(session: &Session, text: &str) -> (i32, bool) {
    let started = std::time::Instant::now();
    let result = line_untraced(session, text);
    crate::trace::record("line", text, 0, result.0 as usize, started);
    result
}

fn line_untraced(session: &Session, text: &str) -> (i32, bool) {
    let ending = match plan(session, text) {
        Err(message) => Ending::Usage(message),
        Ok(Plan::Exit) => return (EXIT_OK, false),
        Ok(Plan::Nothing) => return (EXIT_OK, true),
        Ok(Plan::Whoami) => {
            whoami(session);
            Ending::Done
        }
        Ok(Plan::Help(topic)) => {
            print!("{}", help_text(topic.as_deref()));
            Ending::Done
        }
        Ok(Plan::History { all }) => {
            history(session, all);
            Ending::Done
        }
        Ok(Plan::Inbox) => {
            inbox(session);
            Ending::Done
        }
        Ok(Plan::Rooms) => {
            rooms(session);
            Ending::Done
        }
        Ok(Plan::Text(text)) => {
            print!("{text}");
            Ending::Done
        }
        Ok(Plan::Template { label, lines }) => return run_template(session, &label, &lines),
        Ok(Plan::Guide) => match fs::read_to_string(FRIENDS_GUIDE) {
            Ok(text) => {
                print!("{text}");
                Ending::Done
            }
            Err(e) => Ending::Client(format!(
                "the friends' guide is not installed at {FRIENDS_GUIDE} ({e}); it is deploy/shell/FRIENDS.md in the Mini source, and ember sent you a copy"
            )),
        },
        Ok(Plan::NotHere(text)) => Ending::Client(text),
        Ok(Plan::Chat(chat)) => {
            let (code, text) = crate::chat::run(session, chat);
            Ending::Rendered(code, text)
        }
        Ok(Plan::Story(story)) => {
            let (code, text) = crate::story::run(session, story);
            Ending::Rendered(code, text)
        }
        Ok(Plan::Export(path)) => match fs::read(&path) {
            Ok(bytes) => {
                let value: std::result::Result<Value, _> = serde_json::from_slice(&bytes);
                match value {
                    Ok(v) => {
                        println!("{v}");
                        Ending::Done
                    }
                    Err(e) => Ending::Client(format!("{} is not JSON: {e}", path.display())),
                }
            }
            Err(e) => Ending::Client(format!(
                "cannot read {}: {e} (publish the delegation first)",
                path.display()
            )),
        },
        Ok(plan) => {
            let init = text.split_whitespace().next() == Some("init");
            let ending = execute(session, plan);
            if init && matches!(ending, Ending::Done) {
                apply_pending_joins(session);
            }
            ending
        }
    };
    let (code, text) = render(&ending);
    let _ = io::stdout().flush();
    if !text.is_empty() {
        eprint!("{text}");
    }
    (code, true)
}

// ---------------------------------------------------------------- completion

fn stems(dir: &Path, suffix: &str, skip: impl Fn(&str) -> bool) -> Vec<String> {
    let mut out: Vec<String> = fs::read_dir(dir)
        .map(|entries| {
            entries
                .filter_map(|e| e.ok()?.file_name().into_string().ok())
                .filter_map(|n| n.strip_suffix(suffix).map(str::to_owned))
                .filter(|n| !skip(n))
                .collect()
        })
        .unwrap_or_default();
    out.sort();
    out
}

/// Candidates for the word being typed at the end of `prefix`.
pub(crate) fn complete(session: &Session, prefix: &str) -> Vec<String> {
    let mut w: Vec<String> = prefix.split_whitespace().map(str::to_owned).collect();
    if prefix.is_empty() || prefix.ends_with(char::is_whitespace) {
        w.push(String::new());
    }
    let position = w.len() - 1;
    let partial = w[position].clone();
    let refs = || -> Vec<String> {
        stems(&session.workspace.join("refs"), ".json", |_| false)
            .iter()
            .map(|stem| crate::workspace::ref_name_of_file(stem))
            .collect()
    };
    let proposals = || stems(&session.workspace.join("proposals"), "", |_| false);
    let attempts = || stems(&session.workspace.join("attempts"), "", |n| n.starts_with("a-"));
    let keys = || stems(&session.home.join("keys"), "", |n| n.ends_with(".pub"));
    let enrolled = || stems(&session.home.join("enroll"), "", |_| false);
    let verb = w[0].as_str();
    let candidates: Vec<String> = match (verb, position) {
        (_, 0) => command_catalog().map(|v| v.name.to_owned()).collect(),
        ("room" | "key" | "chat" | "app", 1) => subcommands(verb),
        ("app", 2) if w[1] == "status" => refs(),
        ("app", 2) if w[1] == "delegate-lifecycle" => subcommands_after("app","app delegate-lifecycle "),
        ("app", 4) if w[1] == "delegate-lifecycle" && w[2] == "prepare" => refs(),
        ("ask" | "dismiss" | "summon", 1) => refs(),
        ("home" | "read" | "describe", 1) => refs(),
        ("submit" | "publish" | "export", 1) => proposals(),
        ("lookup" | "retry" | "attempt", 1) => attempts(),
        ("history", 1) => vec!["all".into()],
        ("pay", 1) => ["address", "status", "audit"].map(String::from).to_vec(),
        ("pay", 2) if w[1] != "audit" => refs(),
        ("init", 1) => keys(),
        ("enroll", 1) => ["plan", "offer", "seal", "submit", "lookup", "welcome"].map(String::from).to_vec(),
        ("enroll", 2) if w[1] != "plan" => enrolled(),
        ("enroll", 3) if w[1] == "plan" => keys(),
        ("law", 1) => vec!["show".into()],
        ("law", 2) if w[1] == "show" => refs(),
        ("invoke" | "delegate" | "law", 2) => refs(),
        ("invoke", 3) => vec!["create".into(), "write".into()],
        ("revoke" | "renounce", 2) => refs(),
        ("doc", 1) => subcommands("doc"),
        ("room", 2) if !matches!(w[1].as_str(), "new" | "welcome" | "template" | "invite" | "kick" | "seal" | "rotate" | "register" | "rewrap" | "leave" | "index" | "bind" | "rename" | "unbind") => refs(),
        ("doc", 2) if w[1]=="app-export" => subcommands_after("doc","doc app-export "),
        ("doc", 2) if !matches!(w[1].as_str(), "new" | "append" | "edit" | "annotate" | "link" | "push") => refs(),
        ("doc", 3) if matches!(w[1].as_str(), "append" | "edit" | "annotate" | "link" | "push" | "transclude") => refs(),
        ("doc", 4) if w[1] == "link" => refs(),
        ("board", 1) => ["new", "add", "move", "take"].map(String::from).to_vec(),
        ("board", 3) if w[1] != "new" => refs(),
        ("help", 1) => {
            let mut all: Vec<String> = command_catalog().map(|v| v.name.to_owned()).collect();
            all.push("guide".into());
            all
        }
        ("delegate", 4) => vec!["observe".into(), "observe,mutate".into()],
        ("bid" | "reveal" | "bids", 1) => refs(),
        ("market", 1) => ["open", "settle"].map(String::from).to_vec(),
        ("market", 2) if w[1] == "settle" => refs(),
        _ => vec![],
    };
    candidates.into_iter().filter(|c| c.starts_with(&partial)).collect()
}

// ---------------------------------------------------------------- terminal

/// Character-at-a-time input for the line editor. Only three flags change,
/// and they are set back by name: some `stty` builds cannot parse their own
/// `-g` state string.
struct Raw;

impl Raw {
    fn enter() -> Option<Self> {
        let ok = Command::new("stty")
            .args(["-icanon", "-echo", "-isig", "min", "1", "time", "0"])
            .stdin(Stdio::inherit())
            .status()
            .ok()?
            .success();
        ok.then_some(Self)
    }
}

impl Drop for Raw {
    fn drop(&mut self) {
        let _ = Command::new("stty")
            .args(["icanon", "echo", "isig"])
            .stdin(Stdio::inherit())
            .status();
    }
}

fn common_prefix(items: &[String]) -> String {
    let Some(first) = items.first() else {
        return String::new();
    };
    let mut end = first.len();
    for item in items {
        end = end.min(first.bytes().zip(item.bytes()).take_while(|(a, b)| a == b).count());
    }
    first[..end].to_owned()
}

/// Read one line with echo, backspace, Ctrl-U, Ctrl-C, Ctrl-D, Tab
/// completion and Up/Down history. None means end of input.
fn read_line(session: &Session, prompt: &str, past: &[String]) -> Option<String> {
    let _raw = Raw::enter()?;
    let mut out = io::stderr();
    let mut line = String::new();
    let mut back = past.len();
    let redraw = |out: &mut io::Stderr, line: &str| {
        let _ = write!(out, "\r\x1b[K{prompt}{line}");
        let _ = out.flush();
    };
    redraw(&mut out, &line);
    let mut stdin = io::stdin().lock();
    let mut pending: Vec<u8> = Vec::new();
    loop {
        let mut byte = [0u8; 1];
        if stdin.read(&mut byte).ok()? == 0 {
            return None;
        }
        match byte[0] {
            b'\r' | b'\n' => {
                let _ = writeln!(out);
                return Some(line);
            }
            4 if line.is_empty() => {
                let _ = writeln!(out);
                return None;
            }
            3 => {
                let _ = writeln!(out, "^C");
                line.clear();
                redraw(&mut out, &line);
            }
            21 => {
                line.clear();
                redraw(&mut out, &line);
            }
            127 | 8 => {
                line.pop();
                redraw(&mut out, &line);
            }
            b'\t' => {
                let found = complete(session, &line);
                let partial_len = if line.is_empty() || line.ends_with(' ') {
                    0
                } else {
                    line.rsplit(' ').next().map(str::len).unwrap_or(0)
                };
                let stem = &line[..line.len() - partial_len];
                if found.len() == 1 {
                    line = format!("{stem}{} ", found[0]);
                } else if !found.is_empty() {
                    let common = common_prefix(&found);
                    if common.len() > partial_len {
                        line = format!("{stem}{common}");
                    } else {
                        let _ = writeln!(out);
                        let _ = writeln!(out, "{}", found.join("  "));
                    }
                }
                redraw(&mut out, &line);
            }
            0x1b => {
                let mut seq = [0u8; 2];
                if stdin.read_exact(&mut seq).is_err() {
                    return None;
                }
                match seq {
                    [b'[', b'A'] if back > 0 => {
                        back -= 1;
                        line = past[back].clone();
                    }
                    [b'[', b'B'] if back < past.len() => {
                        back += 1;
                        line = past.get(back).cloned().unwrap_or_default();
                    }
                    _ => {}
                }
                redraw(&mut out, &line);
            }
            b if b >= 0x20 => {
                pending.push(b);
                if let Ok(text) = std::str::from_utf8(&pending) {
                    line.push_str(text);
                    pending.clear();
                    redraw(&mut out, &line);
                } else if pending.len() >= 4 {
                    pending.clear();
                }
            }
            _ => {}
        }
    }
}

// ---------------------------------------------------------------- entry

pub(crate) fn run(mut args: Args) -> Result<()> {
    let absolute = |value: OsString, label: &str| -> Result<PathBuf> {
        let path = PathBuf::from(value);
        if !path.is_absolute() {
            return Err(format!("shell --{label} must be absolute"));
        }
        Ok(path)
    };
    let workspace = absolute(args.required("workspace")?, "workspace")?;
    let home = absolute(args.required("home")?, "home")?;
    let host = args.optional("host").map(|h| absolute(h, "host")).transpose()?;
    let config = args.optional("config").map(|c| absolute(c, "config")).transpose()?;
    let one = args.optional("line");
    // `--plan`: parse and plan the one line, print the plan, run nothing (the per-leaf dry run of
    // the web front end's parity row; a usage error is the shell's usage ending, exit 2).
    let plan_only = args.optional("plan").is_some();
    args.finish()?;
    let _ = crate::keys::STDIN_FREE.set(one.is_some());
    // A session over a workspace that already pins its Host takes host,
    // config and socket from that pin (a remote workspace from `mini join`
    // pins no Host image, only its digest).
    let (host, config) = match (host, config) {
        (Some(host), Some(config)) => (host, config),
        (None, config) if super::SOCKET.get().is_none_or(|s| super::transport::is_remote(s)) => {
            let pin = super::workspace::load(&workspace)?;
            let pinned = super::workspace::workspace_host(&pin)?;
            let config = match config {
                Some(config) => config,
                None => super::workspace::member_path(&pin, "config")?,
            };
            (pinned, config)
        }
        _ => return Err("shell takes --host and --config, or a remote workspace that pins them".into()),
    };
    if super::SOCKET.get().is_none() {
        return Err("shell requires --socket (the deployment's public socket) or --remote".into());
    }
    crate::fsio::ensure_private_dir(&home)?;
    let session = Session { workspace, home, host, config };
    let code = if let Some(one) = one {
        let text = one.into_string().map_err(|_| "--line must be UTF-8")?;
        if plan_only {
            match plan(&session, &text) {
                Ok(planned) => {
                    println!("plan: {}", describe_plan(&planned));
                    EXIT_OK
                }
                // The grammar accepted the words but the plan builder refused on a fact of this
                // workspace (an open room given a private room's declaration, a template file
                // that does not parse): exit 1, named as such. The grammar's own refusal: usage.
                Err(message) if grammar_accepts(&text) => {
                    eprintln!("error: parsed, not plannable here: {message}");
                    EXIT_CLIENT
                }
                Err(message) => {
                    eprint!("{}", render(&Ending::Usage(message)).1);
                    EXIT_USAGE
                }
            }
        } else {
            line(&session, &text).0
        }
    } else if io::stdin().is_terminal() {
        let mut past: Vec<String> = Vec::new();
        let mut last = EXIT_OK;
        eprint!("{}", start_text(&session));
        while let Some(text) = read_line(&session, "mini> ", &past) {
            if !text.trim().is_empty() {
                past.push(text.clone());
            }
            let (code, more) = line(&session, &text);
            last = code;
            if !more {
                break;
            }
        }
        last
    } else {
        let mut last = EXIT_OK;
        for text in io::stdin().lock().lines() {
            let text = text.map_err(|e| format!("cannot read script: {e}"))?;
            if text.trim().is_empty() || text.trim_start().starts_with('#') {
                continue;
            }
            eprintln!("mini> {text}");
            let (code, more) = line(&session, &text);
            last = code;
            if code != EXIT_OK || !more {
                break;
            }
        }
        last
    };
    let _ = io::stdout().flush();
    std::process::exit(code);
}

#[cfg(test)]
mod tests {
    #[test]
    fn refusals_keep_only_the_newest() {
        let dir = std::env::temp_dir().join(format!("refusals-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        for n in 0..5 {
            fs::write(dir.join(format!("100{n}-x-ab.bin")), b"x").unwrap();
            fs::write(dir.join(format!("100{n}-x-ab.json")), b"{}").unwrap();
        }
        super::prune_refusals(&dir, 2);
        let mut left: Vec<String> = fs::read_dir(&dir).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
        left.sort();
        assert_eq!(left, ["1003-x-ab.bin", "1003-x-ab.json", "1004-x-ab.bin", "1004-x-ab.json"]);
        fs::remove_dir_all(&dir).unwrap();
    }

    use super::*;
    use std::os::unix::fs::PermissionsExt;

    fn session() -> Session {
        Session {
            workspace: PathBuf::from("/w"),
            home: PathBuf::from("/h"),
            host: PathBuf::from("/bin/host"),
            config: PathBuf::from("/c.json"),
        }
    }

    #[test]
    fn export_world_writes_into_a_private_exports_folder_under_home() {
        let home = std::env::temp_dir().join(format!("mini-export-home-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&home);
        std::fs::create_dir_all(&home).unwrap();
        std::fs::set_permissions(&home, std::fs::Permissions::from_mode(0o700)).unwrap();
        let s = Session { home: home.clone(), ..session() };
        let Plan::Client { command, flags, writes } = plan(&s, "export world w1").unwrap() else { panic!("not a client plan") };
        assert_eq!(command, "export-world");
        assert!(flags.iter().any(|(k, v)| k == "out" && PathBuf::from(v) == home.join("exports/w1")));
        admit_session_paths(&s, &flags, &writes).unwrap();
        assert_eq!(std::fs::metadata(home.join("exports")).unwrap().permissions().mode() & 0o777, 0o700);
        assert!(plan(&s, "export world ../x").is_err());
        assert!(matches!(plan(&s, "export p1").unwrap(), Plan::Export(_)), "export ID keeps its meaning");
        let _ = std::fs::remove_dir_all(&home);
    }

    /// Every `apps` grammar leaf, planned by the shell and read back by `apps::run`'s own argument
    /// reader, leaves no flag unconsumed: the shell passes the workspace to every apps verb, and
    /// `run` takes it for every action (it had left `--dir` on all but install and bootstrap, so
    /// `apps search` and `apps list` failed with "unknown or duplicate option --dir").
    #[test]
    fn every_apps_leaf_is_read_whole_by_the_apps_argument_reader() {
        let home = std::env::temp_dir().join(format!("mini-apps-leaves-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&home);
        std::fs::create_dir_all(&home).unwrap();
        std::fs::set_permissions(&home, std::fs::Permissions::from_mode(0o700)).unwrap();
        let s = Session { home: home.clone(), ..session() };
        for leaf in crate::shell_grammar::APPS.leaves {
            let mut words = leaf.path.iter().map(|w| w.to_string()).collect::<Vec<_>>();
            for a in leaf.args {
                words.push(match a.name {
                    "GRAIN" => "a4501", "MEMBER" => "bob", "FILE" => "out.spk", "TOKEN" => "t0",
                    "REQUEST-ID" => "00000000000000000000000000000000", "TERM" => "slides", _ => "x1",
                }.to_owned());
            }
            let line = words.join(" ");
            let Plan::Client { command, flags, .. } = plan(&s, &line).unwrap_or_else(|e| panic!("{line}: {e}")) else { panic!("{line}: not a client plan") };
            assert_eq!(command, "apps", "{line}");
            let args = crate::Args { command: "apps".into(), values: flags.into_iter().map(|(k, v)| (std::ffi::OsString::from(format!("--{k}")), v)).collect() };
            // The run may fail on a world this test does not have (no index, no worker socket); it must
            // not fail on the arguments.
            if let Err(error) = crate::apps::run(args) {
                assert!(!error.contains("unknown or duplicate option") && !error.contains("unexpected argument"), "{line}: {error}");
            }
        }
        let _ = std::fs::remove_dir_all(&home);
    }

    fn client(plan: Plan) -> (String, Vec<(String, String)>, Vec<(PathBuf, String)>) {
        let Plan::Client { command, flags, writes } = plan else {
            panic!("not a client plan: {plan:?}");
        };
        (
            command,
            flags.into_iter().map(|(k, v)| (k, v.into_string().unwrap())).collect(),
            writes.into_iter().map(|(p, b)| (p, String::from_utf8(b).unwrap())).collect(),
        )
    }

    #[test]
    fn pending_inbox_joins_run_only_chat_join_and_a_refused_one_stays_for_the_member() {
        let home = std::env::temp_dir().join(format!("mini-pending-joins-{}", std::process::id()));
        let _ = fs::remove_dir_all(&home);
        fs::create_dir_all(home.join("inbox")).unwrap();
        fs::set_permissions(&home, fs::Permissions::from_mode(0o700)).unwrap();
        fs::write(home.join("inbox/a-other.join"), "keygen stolen.key\n").unwrap();
        fs::write(home.join("inbox/b-two.join"), "chat join x {}\nkeygen y.key\n").unwrap();
        // no workspace: the join is refused by chat join itself, and the file stays for the member
        fs::write(home.join("inbox/c-feedback.join"), "chat join feedback {\"recipient\":\"7\"}\n").unwrap();
        fs::write(home.join("inbox/ref.json"), "{}").unwrap();
        let session = Session { home: home.clone(), workspace: home.join("no-workspace"), ..session() };
        apply_pending_joins(&session);
        for name in ["a-other", "b-two", "c-feedback"] {
            assert!(home.join(format!("inbox/{name}.join")).is_file(), "{name} stays pending");
            assert!(!home.join(format!("inbox/{name}.joined")).exists(), "{name} was not joined");
        }
        assert!(!home.join("keys").exists(), "a .join file never runs another verb");
        assert!(home.join("inbox/ref.json").is_file(), "delivered references are untouched");
        let _ = fs::remove_dir_all(&home);
    }

    #[test]
    fn a_fresh_home_admits_keygen_and_requests_and_still_refuses_a_linked_folder() {
        let home = std::env::temp_dir().join(format!("mini-shell-fresh-home-{}", std::process::id()));
        let _ = fs::remove_dir_all(&home);
        fs::create_dir(&home).unwrap();
        fs::set_permissions(&home, fs::Permissions::from_mode(0o700)).unwrap();
        let session = Session { home: home.clone(), ..session() };
        let Plan::Client { flags, writes, .. } = plan(&session, "keygen mini.key").unwrap() else { panic!("keygen is a client plan") };
        assert!(writes.is_empty());
        assert!(flags.iter().any(|(_, v)| Path::new(v).starts_with(home.join("keys"))), "keygen hands the client HOME/keys/...");
        admit_session_paths(&session, &flags, &writes).expect("a fresh home admits keygen");
        assert!(home.join("keys").is_dir() && home.join("enroll").is_dir());
        let request = vec![(home.join("requests").join("a.json"), b"{}".to_vec())];
        admit_session_paths(&session, &[], &request).expect("a fresh home admits a request");
        assert!(home.join("requests").is_dir());
        let outside = home.with_extension("outside");
        let _ = fs::remove_dir_all(&outside);
        fs::create_dir(&outside).unwrap();
        fs::remove_dir(home.join("keys")).unwrap();
        std::os::unix::fs::symlink(&outside, home.join("keys")).unwrap();
        assert!(admit_session_paths(&session, &flags, &writes).is_err(), "a linked keys folder is refused");
        fs::remove_dir_all(&home).unwrap();
        fs::remove_dir_all(&outside).unwrap();
    }

    fn pairs(items: &[(&str, &str)]) -> Vec<(String, String)> {
        items.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect()
    }

    #[test]
    fn adoption_shell_pins_home_key_and_named_lookup_attempt() {
        let s = session();
        let prepared = client(plan(&s, "adopt-next-key future.key").unwrap());
        assert_eq!(prepared.0, "adopt-next-key");
        assert_eq!(prepared.1, pairs(&[("workspace", "/w"), ("next-key", "/h/keys/future.key")]));
        let recovery = client(plan(&s, "adopt-next-key lookup adopt-next-4-0").unwrap());
        assert_eq!(recovery.1, pairs(&[("workspace", "/w"), ("action", "lookup"), ("attempt", "adopt-next-4-0")]));
        for line in ["adopt-next-key", "adopt-next-key ../secret", "adopt-next-key /tmp/key", "adopt-next-key lookup", "adopt-next-key lookup ../attempt"] {
            assert!(plan(&s, line).is_err(), "accepted {line}");
        }
    }

    #[test]
    fn world_kind_shell_routes_named_world_operations() {
        let s = session();
        let created = client(plan(&s, "create election --from poll open --in lab").unwrap());
        assert!(created.1.contains(&("action".into(), "instance-create".into())));
        assert!(created.1.contains(&("from".into(), "poll".into())));
        assert!(created.1.contains(&("in".into(), "lab".into())));
        assert!(plan(&s, "create election --from poll --from other open").is_err());
        assert!(plan(&s, "create election --from poll open --owner 7").is_err());
        let edit = client(plan(&s, "instance set vote election votes 7 1").unwrap());
        let request: Value = serde_json::from_str(&edit.2[0].1).unwrap();
        assert_eq!(request["targets"][0]["payload"], json!({"type":"worldNamed", "actions":[
            {"type":"set","field":"votes","key":"7","value":"1"}]}));
        let shown = client(plan(&s, "kind show poll").unwrap());
        assert!(shown.1.contains(&("action".into(), "kind-show".into())));
        assert!(plan(&s, "instance erase delete election votes -1").is_err());
        let definition = r#"{"descriptor":{"revision":"1","fields":[]},"defaults":[]}"#;
        let kind = client(plan(&s, &format!("kind create poll {definition} open --in lab")).unwrap());
        assert!(kind.1.contains(&("action".into(), "kind-create".into())));
        assert_eq!(kind.2.len(),2);
        let revision = client(plan(&s, &format!("kind revise rev poll {definition}")).unwrap());
        let request: Value = serde_json::from_str(&revision.2[0].1).unwrap();
        assert_eq!(request["targets"][0]["payload"]["type"], "kindDefinition");
    }

    #[test]
    fn world_kind_method_compute_consent_is_explicit() {
        let s=session();
        let call=client(plan(&s,"instance call close poll close --max-compute-credits 12 --fund purse").unwrap());
        assert!(call.1.contains(&("fund".into(),"purse".into())));
        assert!(call.1.contains(&("max-compute-credits".into(),"12".into())));
        for bad in ["instance call close poll close --fund purse", "instance call close poll close --max-compute-credits 12",
          "instance call close poll close --fund purse --fund other", "instance call close poll close --max-cost 12"] {
            assert!(plan(&s,bad).is_err(),"{bad}");
        }
        let program=client(plan(&s,r#"program create close {"jam":"02","abi":{}} open --in lab"#).unwrap());
        assert!(program.1.contains(&("in".into(),"lab".into())));
    }

    #[test]
    fn law_export_is_a_separate_facet_operation() {
        let s=session();
        let plan=client(super::plan(&s,r#"law export change poll {"selector":{"physicalKinds":["18"]},"predicate":{"type":"all","predicates":[]},"parents":[]}"#).unwrap());
        let request:Value=serde_json::from_str(&plan.2[0].1).unwrap();
        assert_eq!(request["action"],"install-export"); assert_eq!(request["name"],"poll");
        assert!(request.get("predicate").is_none());
        let shown=client(super::plan(&s,"law export show poll").unwrap());
        assert!(shown.1.contains(&("action".into(),"law-export-show".into())));
        let removed=client(super::plan(&s,"law export remove poll none").unwrap());
        let request:Value=serde_json::from_str(&removed.2[0].1).unwrap();
        assert!(request["component"].is_null());
    }

    #[test]
    fn law_export_show_passes_the_whole_reference() {
        let s=session();
        let shown=client(super::plan(&s,"law export show jli-room/notes").unwrap());
        assert!(shown.1.contains(&("action".into(),"law-export-show".into())));
        assert!(shown.1.contains(&("name".into(),"jli-room/notes".into())));
    }

    #[test]
    fn pay_verbs_are_one_client_operation_each() {
        let s = session();
        assert_eq!(
            client(plan(&s, "pay address").unwrap()),
            ("pay".into(), pairs(&[("action", "address"), ("dir", "/w")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "pay status account").unwrap()),
            ("pay".into(), pairs(&[("action", "status"), ("dir", "/w"), ("account", "account")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "pay audit").unwrap()),
            ("pay".into(), pairs(&[("action", "audit"), ("dir", "/w")]), vec![])
        );
        // observe, book and heartbeat belong to the operator and the watcher, not a friend.
        for line in ["pay observe", "pay book x", "pay audit x", "pay address ../x", "pay"] {
            assert!(plan(&s, line).is_err(), "{line}");
        }
    }

    /// SEALED-MARKET: each market verb is one client-contract operation; the
    /// commitment, the opening and the allocation are the client's, not the
    /// shell's.
    #[test]
    fn market_verbs_are_one_client_operation_each() {
        let s = session();
        let ws = |items: &[(&str, &str)]| ("workspace".to_string(), pairs(items), vec![]);
        assert_eq!(
            client(plan(&s, "market open fish 30 40 8").unwrap()),
            ws(&[("action", "market-open"), ("dir", "/w"), ("name", "fish"), ("close", "30"),
                ("reveal-end", "40"), ("supply", "8")])
        );
        assert_eq!(
            client(plan(&s, "bid fish 30 5").unwrap()),
            ws(&[("action", "market-bid"), ("dir", "/w"), ("name", "fish"), ("price", "30"), ("qty", "5"),
                ("proposal-id", "bid-fish")])
        );
        assert_eq!(client(plan(&s, "bid fish 30 5 again").unwrap()).1[5], ("proposal-id".into(), "again".into()));
        assert_eq!(
            client(plan(&s, "reveal fish").unwrap()),
            ws(&[("action", "market-reveal"), ("dir", "/w"), ("name", "fish"), ("proposal-id", "reveal-fish")])
        );
        assert_eq!(
            client(plan(&s, "bids fish").unwrap()),
            ws(&[("action", "market-bids"), ("dir", "/w"), ("name", "fish")])
        );
        assert_eq!(
            client(plan(&s, "market settle fish").unwrap()),
            ws(&[("action", "market-settle"), ("dir", "/w"), ("name", "fish"), ("proposal-id", "settle-fish")])
        );
        assert_eq!(
            client(plan(&s, "law show fish").unwrap()),
            ws(&[("action", "law-show"), ("dir", "/w"), ("name", "fish")])
        );
        for line in ["bid fish -3 5", "bid fish 3", "bid ../x 3 5", "market open fish 30 40", "market close fish",
            "market", "reveal", "bids fish more", "market open fish x 40 8"] {
            assert!(plan(&s, line).is_err(), "{line}");
        }
        // `law ID REF TEXT` is still a proposal: a law named show is three words or more.
        assert!(matches!(plan(&s, "law show fish open").unwrap(), Plan::Client { .. }));
    }

    #[test]
    fn credit_verbs_are_one_client_operation_each() {
        let s = session();
        assert_eq!(
            client(plan(&s, "credit").unwrap()),
            ("credit".into(), pairs(&[("action", "balance"), ("dir", "/w")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "pay lab week").unwrap()),
            ("credit".into(), pairs(&[("action", "pay"), ("dir", "/w"), ("room", "lab"), ("outbox", "/h/outbox")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "pay lab 40 --account purse").unwrap()),
            ("credit".into(), pairs(&[("action", "pay"), ("dir", "/w"), ("room", "lab"), ("outbox", "/h/outbox"),
                ("amount", "40"), ("account", "purse")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "tariff lab set week 100").unwrap()),
            ("credit".into(), pairs(&[("action", "tariff"), ("dir", "/w"), ("set", "week"), ("value", "100"), ("room", "lab")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "topup lab 50").unwrap()),
            ("credit".into(), pairs(&[("action", "topup"), ("dir", "/w"), ("room", "lab"), ("amount", "50")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "room status lab").unwrap()),
            ("credit".into(), pairs(&[("action", "status"), ("dir", "/w"), ("room", "lab"), ("inbox", "/h/inbox")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "room renew lab 77 --for 12").unwrap()),
            ("credit".into(), pairs(&[("action", "renew"), ("dir", "/w"), ("room", "lab"), ("subject", "77"),
                ("outbox", "/h/outbox"), ("for", "12")]), vec![])
        );
        for line in ["pay lab", "pay lab -1", "pay lab week --wallet x", "tariff lab set week", "tariff lab set week x",
            "topup lab", "room renew lab", "room renew lab 77 --for 1 --until 3", "credit a b", "room status"] {
            assert!(plan(&s, line).is_err(), "{line}");
        }
    }

    #[test]
    fn words_split_quote_and_keep_json_whole() {
        assert_eq!(words("  read   shared ").unwrap(), ["read", "shared"]);
        assert_eq!(words("a 'b c' \"d \\\"e\\\"\" f'g h'").unwrap(), ["a", "b c", "d \"e\"", "fg h"]);
        assert_eq!(
            words(r#"law v2 shared {"type":"not","predicate":{"type":"any","predicates":[ ]}}  # c"#).unwrap(),
            ["law", "v2", "shared", r#"{"type":"not","predicate":{"type":"any","predicates":[ ]}}"#]
        );
        assert_eq!(words(r#"x {"a":"} ]{"}"#).unwrap(), ["x", r#"{"a":"} ]{"}"#]);
        assert_eq!(words("# only a comment").unwrap(), Vec::<String>::new());
        assert!(words("a 'open").is_err());
        assert!(words("a \"open").is_err());
        assert!(words(r#"a {"b":1"#).is_err());
        assert!(words(r#"a {"b":1}x"#).is_err());
    }

    #[test]
    fn each_verb_is_exactly_one_client_operation() {
        let s = session();
        assert_eq!(
            client(plan(&s, "job post lab 42 --input 6 --price 1000 --deadline 600 --account purse").unwrap()),
            (
                "job".into(),
                pairs(&[
                    ("action", "post"),
                    ("dir", "/w"),
                    ("room", "lab"),
                    ("program", "42"),
                    ("input", "6"),
                    ("price", "1000"),
                    ("deadline", "600"),
                    ("account", "purse"),
                ]),
                vec![]
            )
        );
        assert_eq!(
            client(plan(&s, "job answer j1 9").unwrap()).1,
            pairs(&[("action", "answer"), ("dir", "/w"), ("name", "j1"), ("output", "9")])
        );
        assert_eq!(client(plan(&s, "jobs lab").unwrap()).1, pairs(&[("action", "list"), ("dir", "/w"), ("room", "lab")]));
        assert!(plan(&s, "job post lab 42 --sneaky 1").is_err());
        // `bend`: the source is `@FILE` under HOME/requests; one client operation each.
        let home = s.home.display().to_string();
        assert_eq!(
            client(plan(&s, "bend publish tally @Tally.obend --entry tally").unwrap()),
            ("bend".into(), pairs(&[("dir", "/w"), ("action", "publish"), ("name", "tally"), ("source", &format!("{home}/requests/Tally.obend")), ("entry", "tally")]), vec![])
        );
        assert_eq!(
            client(plan(&s, "bend run tally counter --deposit 9000 --seed {\"tag\":\"natural\",\"value\":\"1\"}").unwrap()).1,
            pairs(&[("dir", "/w"), ("action", "run"), ("name", "tally"), ("object", "counter"), ("deposit", "9000"), ("seed", r#"{"tag":"natural","value":"1"}"#)])
        );
        assert_eq!(client(plan(&s, "bend show counter").unwrap()).1, pairs(&[("dir", "/w"), ("action", "show"), ("object", "counter")]));
        assert!(plan(&s, "bend publish tally Tally.obend").is_err(), "the source is @FILE, not a path word");
        assert!(plan(&s, "bend run tally").is_err());
        assert_eq!(client(plan(&s, "bend run tally counter --lose-reply-once").unwrap()).1, pairs(&[("dir", "/w"), ("action", "run"), ("name", "tally"), ("object", "counter"), ("lose-reply-once", "true")]));
        assert_eq!(client(plan(&s, "bend lookup tally").unwrap()).1, pairs(&[("dir", "/w"), ("action", "lookup"), ("name", "tally")]));
        assert_eq!(client(plan(&s, "bend retry tally").unwrap()).1, pairs(&[("dir", "/w"), ("action", "retry"), ("name", "tally")]));
        assert_eq!(
            client(plan(&s, "submit first-action").unwrap()),
            (
                "workspace".into(),
                pairs(&[
                    ("action", "submit"),
                    ("dir", "/w"),
                    ("intent", "/w/proposals/first-action/intent.json"),
                    ("attempt", "/w/attempts/first-action"),
                ]),
                vec![]
            )
        );
        assert_eq!(
            client(plan(&s, "retry first-action").unwrap()).1,
            pairs(&[("attempt", "/w/attempts/first-action"), ("mode", "submit")])
        );
        assert_eq!(
            client(plan(&s, "lookup first-action").unwrap()).1,
            pairs(&[("action", "recover"), ("dir", "/w"), ("attempt", "/w/attempts/first-action")])
        );
        // FIX-IDENTITY: a hosted enrollment takes the newcomer's next public key
        // and co-signature as words, never a file the sponsor's home holds.
        assert!(plan(&s, "enroll plan newcomer-1 nc.key").is_err());
        let Plan::Client { command, flags, writes } =
            plan(&s, &format!("enroll plan newcomer-1 nc.key {} {}", "cd".repeat(32), "ef".repeat(64))).unwrap()
        else {
            panic!("not a client plan")
        };
        let flags: Vec<(String, String)> =
            flags.into_iter().map(|(k, v)| (k, v.into_string().unwrap())).collect();
        assert_eq!(
            (command, flags, writes),
            (
                "enroll".into(),
                pairs(&[
                    ("action", "plan"),
                    ("sponsor-workspace", "/w"),
                    ("factory-ref", "factory"),
                    ("name", "newcomer-1"),
                    ("new-key", "/h/keys/nc.key"),
                    ("next-public-key", "/h/enroll/newcomer-1.next.pub"),
                    ("next-cosign", "/h/enroll/newcomer-1.next.cosign"),
                    ("dir", "/h/enroll/newcomer-1"),
                ]),
                vec![
                    (PathBuf::from("/h/enroll/newcomer-1.next.pub"), vec![0xcd; 32]),
                    (PathBuf::from("/h/enroll/newcomer-1.next.cosign"), vec![0xef; 64]),
                ]
            )
        );
        assert!(matches!(plan(&s, "init mini.key 42").unwrap(), Plan::NotHere(text)
            if text.starts_with("init needs your provisioning at /h/provision/birth-context.json")));
        assert_eq!(
            client(plan(&s, "import stolen object 15 11").unwrap()).1,
            pairs(&[
                ("action", "import"),
                ("dir", "/w"),
                ("name", "stolen"),
                ("kind", "object"),
                ("target", "15"),
                ("observe-capability", "11"),
            ])
        );
    }

    #[test]
    fn a_public_key_enrollment_never_names_a_newcomer_secret() {
        let s = session();
        let public = "ab".repeat(32);
        let next = "cd".repeat(32);
        // K-PREROTATE: a public-key enrollment names the next public key too,
        // or says --no-prerotation; neither is refused by name.
        let refused = plan(&s, &format!("enroll plan alice {public}")).err().unwrap();
        assert!(refused.contains("NEXT-PUBLIC-KEY-HEX"), "{refused}");
        let Plan::Client { flags: bare, .. } =
            plan(&s, &format!("enroll plan alice {public} --no-prerotation")).unwrap()
        else {
            panic!("not a client plan")
        };
        assert!(bare.contains(&flag("no-prerotation", "true")));
        let cosign = "ef".repeat(64);
        assert!(plan(&s, &format!("enroll plan alice {public} {next}")).is_err(), "a next key without its co-signature");
        let plan_line = format!("enroll plan alice {public} {next} {cosign}");
        let Plan::Client { command, flags, writes } = plan(&s, &plan_line).unwrap() else {
            panic!("not a client plan")
        };
        assert_eq!(command, "enroll");
        let flags: Vec<(String, String)> =
            flags.into_iter().map(|(k, v)| (k, v.into_string().unwrap())).collect();
        assert_eq!(
            flags,
            pairs(&[
                ("action", "plan"),
                ("sponsor-workspace", "/w"),
                ("factory-ref", "factory"),
                ("name", "alice"),
                ("new-public-key", "/h/keys/alice.pub"),
                ("next-public-key", "/h/enroll/alice.next.pub"),
                ("next-cosign", "/h/enroll/alice.next.cosign"),
                ("dir", "/h/enroll/alice"),
            ])
        );
        assert!(!flags.iter().any(|(k, _)| k == "new-key"));
        assert_eq!(
            writes,
            vec![
                (PathBuf::from("/h/keys/alice.pub"), vec![0xab; 32]),
                (PathBuf::from("/h/enroll/alice.next.pub"), vec![0xcd; 32]),
                (PathBuf::from("/h/enroll/alice.next.cosign"), vec![0xef; 64]),
            ]
        );

        let signature = "0f".repeat(64);
        let Plan::Client { flags, writes, .. } = plan(&s, &format!("enroll seal alice {signature}")).unwrap() else {
            panic!("not a client plan")
        };
        assert!(flags.contains(&flag("possession-signature", "/h/requests/alice.possession")));
        assert_eq!(writes, vec![(PathBuf::from("/h/requests/alice.possession"), vec![0x0f; 64])]);
        assert!(plan(&s, "enroll seal alice 0f0f").is_err(), "a short signature is refused");
        assert_eq!(
            client(plan(&s, "enroll offer alice").unwrap()).1,
            pairs(&[("action", "offer"), ("dir", "/h/enroll/alice")])
        );
        assert_eq!(
            client(plan(&s, "enroll welcome alice").unwrap()).1,
            pairs(&[("action", "welcome"), ("dir", "/h/enroll/alice")])
        );
        let (command, flags, writes) =
            client(plan(&s, r#"provision alice 42 1000 {"type":"all","predicates":[]}"#).unwrap());
        assert_eq!(command, "workspace");
        assert_eq!(
            flags,
            pairs(&[
                ("action", "provision"),
                ("dir", "/w"),
                ("name", "alice"),
                ("holder", "42"),
                ("funding", "1000"),
                ("account-predicate", "/h/requests/provision-alice.json"),
                ("factory-ref", "factory"),
            ])
        );
        assert_eq!(writes[0].1, "{\"predicates\":[],\"type\":\"all\"}\n");
    }

    #[test]
    fn proposal_verbs_spell_the_documented_request_shapes() {
        let s = session();
        let (_, flags, writes) = client(plan(&s, "invoke first-action shared create 2 1").unwrap());
        assert_eq!(
            flags,
            pairs(&[
                ("action", "propose"),
                ("dir", "/w"),
                ("request", "/h/requests/first-action.json"),
                ("proposal-id", "first-action"),
            ])
        );
        let request: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(
            request,
            json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"shared",
                "payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","field":"2"},"value":"1"}]}}]})
        );
        let (_, _, writes) = client(plan(&s, "invoke w shared write 2 7 1").unwrap());
        let request: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(
            request["targets"][0]["payload"]["actions"][0],
            json!({"type":"write","key":{"type":"object","field":"2"},"value":"7","expected":"1"})
        );
        let (_, _, writes) = client(plan(&s, "delegate g shared 182 observe,mutate 50000").unwrap());
        let request: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(
            request,
            json!({"type":"minidregg-workspace-proposal-v1","action":"delegate","name":"shared",
                "recipient":"182","verbs":["observe","mutate"],"maxCost":"50000"})
        );
        let (_, _, writes) = client(
            plan(&s, r#"law board-law shared "any [ field 2 monotone, not (verb == write) ]; any [ field 2 in {0,1,2}, not (verb == write) ]""#)
                .unwrap(),
        );
        let request: Value = serde_json::from_str(&writes[0].1).unwrap();
        let guard = json!({"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"2"}});
        assert_eq!(
            request["predicate"],
            json!({"type":"all","predicates":[
                {"type":"any","predicates":[{"type":"monotone","slot":"resource/field/2/after"}, guard]},
                {"type":"any","predicates":[{"type":"memberOf","slot":"resource/field/2/after","values":["0","1","2"]}, guard]}]})
        );
        let (_, _, unquoted) = client(plan(&s, "law seal shared sealed").unwrap());
        let request: Value = serde_json::from_str(&unquoted[0].1).unwrap();
        assert_eq!(request["predicate"], json!({"type":"any","predicates":[]}));
        let (_, _, words) = client(plan(&s, "law l2 shared any [ field 2 monotone, not (verb == write) ]").unwrap());
        let request: Value = serde_json::from_str(&words[0].1).unwrap();
        assert_eq!(request["predicate"]["predicates"][1]["predicate"]["value"], json!("2"));
        assert!(plan(&s, "law bad shared field 2 before monotone").unwrap_err().contains("never refuse"));
        let (_, _, writes) = client(plan(&s, r#"law lock shared {"type":"any","predicates":[]}"#).unwrap());
        let request: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(
            request,
            json!({"type":"minidregg-workspace-proposal-v1","action":"install-policy","name":"shared",
                "predicate":{"type":"any","predicates":[]}})
        );
    }

    #[test]
    fn file_names_stay_inside_the_session() {
        let s = session();
        for bad in [
            "keygen ../x",
            "keygen /etc/passwd",
            "keygen .hidden",
            "init ../../k 7",
            "enroll plan n ../k",
            "enroll lookup ../n",
            "submit ../../x",
            "read ../b",
            "read a/..",
            "read /a",
            "read a/./b",
            "propose x @../../etc/passwd",
            "import r @/abs",
        ] {
            assert!(plan(&s, bad).is_err(), "{bad} should be refused");
        }
        // A name under a room is a reference name, never a path: its files
        // are one flat entry (`lab/index` -> `lab.index`).
        assert!(plan(&s, "read lab/index").is_ok());
        assert_eq!(ref_file("lab/index"), "lab.index");
        assert_eq!(crate::workspace::ref_name_of_file("lab.index"), "lab/index");
    }

    #[test]
    fn usage_errors_name_the_usage() {
        let s = session();
        assert_eq!(plan(&s, "submit").unwrap_err(), "submit ID [--lose-reply-once]");
        assert_eq!(render(&Ending::Usage(plan(&s, "submit").unwrap_err())).1, "usage: submit ID [--lose-reply-once]\n");
        assert!(plan(&s, "frobnicate").unwrap_err().starts_with("unknown verb"));
        assert!(plan(&s, "invoke x shared delete 2").is_err());
        assert!(plan(&s, "init k notanumber").is_err());
        assert_eq!(plan(&s, "   ").unwrap(), Plan::Nothing);
        assert_eq!(plan(&s, "exit").unwrap(), Plan::Exit);
    }

    #[test]
    fn host_refusal_renders_decoded_verbatim_and_exits_three() {
        let decoded = json!({"type":"refused","reason":"no-grant",
            "phase":super::super::hex(b"observation"),
            "detail":super::super::hex(b"this key holds no grant covering this target and operation")});
        let ending = Ending::Host {
            client: "host refused query; encoded refusal: 4452".into(),
            decision: HostDecision::Frame { command: "query".into(), byte: crate::RESPONSE_NO_RECORD, encoded: vec![0x44, 0x52], decoded: None },
            decoded: Some(Ok(decoded)),
            evidence: Some(PathBuf::from("/h/refusals/r.bin")),
        };
        let (code, text) = render(&ending);
        assert_eq!(code, EXIT_REFUSED);
        assert!(text.starts_with(
            "refused: no-grant: this key holds no grant covering this target and operation (phase observation) (Host refused query with no record, reply byte 253)\n"
        ), "{text}");
        assert!(text.contains("  encoded: 4452\n"));
        assert!(text.contains("  evidence: /h/refusals/r.bin\n"));
        assert!(text.ends_with("  client: host refused query; encoded refusal: 4452\n"));
    }

    #[test]
    fn law_refusal_prints_the_hosts_rendering_of_the_failing_clause() {
        let decoded = json!({"type":"refused","reason":"law-denied",
            "phase":super::super::hex(b"observation"),
            "detail":super::super::hex(b"the resource's current law denies this operation"),
            "leaf":{"path":["0"],"text":"any [ field 2 monotone, not (verb == write) ]","before":"2","after":"1"},
            "explain":"field 2 monotone (before 2, after 1)"});
        let ending = Ending::Host {
            client: "host refused prepare".into(),
            decision: HostDecision::Frame { command: "prepare".into(), byte: crate::RESPONSE_NO_RECORD, encoded: vec![0x44], decoded: None },
            decoded: Some(Ok(decoded)),
            evidence: None,
        };
        let (code, text) = render(&ending);
        assert_eq!(code, EXIT_REFUSED);
        assert!(
            text.starts_with("refused: law-denied: field 2 monotone (before 2, after 1) (Host refused prepare with no record, reply byte 253)\n"),
            "{text}"
        );
        // Without the Host's `explain`, the reason's fixed text is printed.
        let plain = Ending::Host {
            client: "c".into(),
            decision: HostDecision::Outcome(json!({"type":"refused","reason":"law-denied","phase":"6162","detail":"78"})),
            decoded: None,
            evidence: None,
        };
        assert!(render(&plain).1.starts_with("refused: law-denied: x (phase ab)\n"));
    }

    #[test]
    fn a_no_record_frame_is_a_refusal_whatever_it_decodes_to() {
        for (decoded, first) in [
            (json!({"type":"contention"}), "refused: no record: the Host answered contention before any append"),
            (json!({"type":"unavailable"}), "refused: no record: the Host answered unavailable before any append"),
        ] {
            let ending = Ending::Host {
                client: "c".into(),
                decision: HostDecision::Frame { command: "submit".into(), byte: crate::RESPONSE_NO_RECORD, encoded: vec![1], decoded: None },
                decoded: Some(Ok(decoded)),
                evidence: None,
            };
            let (code, text) = render(&ending);
            assert_eq!(code, EXIT_REFUSED, "{text}");
            assert!(text.starts_with(first), "{text}");
        }
    }

    #[test]
    fn a_frame_is_classified_by_its_marker_never_by_its_decoding_alone() {
        // 254: the socket refused before forwarding; certainly nothing happened.
        let ending = Ending::Host {
            client: "enrollment Host refused op87; exact frame retained".into(),
            decision: HostDecision::Frame { command: "enrollment op87".into(), byte: 254, encoded: vec![1], decoded: None },
            decoded: Some(Err("bad frame".into())),
            evidence: None,
        };
        let (code, text) = render(&ending);
        assert_eq!(code, EXIT_REFUSED);
        assert!(text.starts_with("refused: not sent: enrollment op87 was never forwarded to the Host (reply byte 254)"), "{text}");
        assert!(text.contains("  encoded: 01\n"));
        // 255 the Host could not decode, or decoded as anything (a refusal included): undecided.
        for decoded in [Some(Err("bad frame".to_owned())), None,
            Some(Ok(json!({"type":"unavailable","detail":super::super::hex(b"host session reopening")}))),
            Some(Ok(json!({"type":"uncertain"}))),
            Some(Ok(json!({"type":"refused","reason":"stale-root","phase":"78","detail":"78"})))] {
            let ending = Ending::Host {
                client: "c".into(),
                decision: HostDecision::Frame { command: "submit".into(), byte: 255, encoded: vec![1], decoded: None },
                decoded,
                evidence: None,
            };
            let (code, text) = render(&ending);
            assert_eq!(code, EXIT_UNDECIDED, "{text}");
            assert!(text.starts_with("undecided: "), "{text}");
        }
    }

    #[test]
    fn receiver_outcomes_are_classified_by_type_not_prose() {
        let refused = Ending::Host {
            client: "host returned refused; exact outcome evidence was retained".into(),
            decision: HostDecision::Outcome(json!({"type":"refused","reason":"law-denied","phase":"6162","detail":"ff00"})),
            decoded: None,
            evidence: None,
        };
        let (code, text) = render(&refused);
        assert_eq!(code, EXIT_REFUSED);
        assert!(text.starts_with("refused: law-denied: hex ff00 (phase ab)\n"), "{text}");
        let uncertain = Ending::Host {
            client: "host returned uncertain; exact outcome evidence was retained".into(),
            decision: HostDecision::Outcome(json!({"type":"uncertain","detail":"78"})),
            decoded: None,
            evidence: None,
        };
        let (code, text) = render(&uncertain);
        assert_eq!(code, EXIT_UNDECIDED);
        assert!(text.starts_with("undecided: Host outcome uncertain, detail \"x\""));
        // An error whose prose mentions a refusal is still a client error when
        // the Host recorded no decision.
        let (code, text) = render(&Ending::Client("host refused query; forged prose".into()));
        assert_eq!(code, EXIT_CLIENT);
        assert_eq!(text, "error: host refused query; forged prose\n");
        assert_eq!(render(&Ending::Usage("submit ID".into())).0, EXIT_USAGE);
    }

    #[test]
    fn completion_offers_verbs_refs_and_proposals() {
        let root = std::env::temp_dir().join(format!("mini-shell-complete-{}-{}", std::process::id(), crate::fsio::random_nonce().unwrap()));
        let ws = root.join("w");
        fs::create_dir_all(ws.join("refs")).unwrap();
        fs::create_dir_all(ws.join("proposals").join("grant-newcomer")).unwrap();
        fs::create_dir_all(ws.join("attempts").join("grant-newcomer")).unwrap();
        fs::create_dir_all(ws.join("attempts").join("a-123")).unwrap();
        fs::write(ws.join("refs").join("shared.json"), b"{}").unwrap();
        fs::write(ws.join("refs").join("factory.json"), b"{}").unwrap();
        let s = Session { workspace: ws, home: root.join("h"), host: "/x".into(), config: "/y".into() };
        assert_eq!(complete(&s, "su"), ["submit", "summon"]);
        assert_eq!(complete(&s, "re"), ["refs", "read", "reveal", "retry", "revoke", "renounce", "react", "reports"]);
        assert_eq!(complete(&s, "bid "), ["factory", "shared"]);
        assert_eq!(complete(&s, "bids s"), ["shared"]);
        assert_eq!(complete(&s, "market s"), ["settle"]);
        assert_eq!(complete(&s, "market settle f"), ["factory"]);
        assert_eq!(complete(&s, "law s"), ["show"]);
        assert_eq!(complete(&s, "law show sh"), ["shared"]);
        assert_eq!(complete(&s, "doc show "), ["factory", "shared"]);
        assert_eq!(complete(&s, "doc link x shared f"), ["factory"]);
        assert_eq!(complete(&s, "board m"), ["move"]);
        assert_eq!(complete(&s, "help g"), ["go", "guide"]);
        assert_eq!(complete(&s, "read "), ["factory", "shared"]);
        assert_eq!(complete(&s, "read s"), ["shared"]);
        assert_eq!(complete(&s, "publish "), ["grant-newcomer"]);
        assert_eq!(complete(&s, "lookup "), ["grant-newcomer"]);
        assert_eq!(complete(&s, "invoke x sh"), ["shared"]);
        assert_eq!(complete(&s, "invoke x shared w"), ["write"]);
        assert_eq!(common_prefix(&["refs".into(), "read".into(), "retry".into()]), "re");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn identical_request_lines_are_idempotent_and_different_ones_refused() {
        let root = std::env::temp_dir().join(format!("mini-shell-write-{}-{}", std::process::id(), crate::fsio::random_nonce().unwrap()));
        let path = root.join("requests").join("x.json");
        fs::create_dir_all(&root).unwrap();
        write_once(&path, b"{}\n").unwrap();
        write_once(&path, b"{}\n").unwrap();
        assert!(write_once(&path, b"{\"a\":1}\n").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    fn temp_session(label: &str) -> (PathBuf, Session) {
        let root = std::env::temp_dir().join(format!("mini-shell-{label}-{}-{}", std::process::id(), crate::fsio::random_nonce().unwrap()));
        fs::create_dir_all(root.join("h")).unwrap();
        fs::create_dir_all(root.join("w")).unwrap();
        let s = Session { workspace: root.join("w"), home: root.join("h"), host: "/bin/host".into(), config: "/c.json".into() };
        (root, s)
    }

    fn request_of(plan: Plan) -> (Vec<(String, String)>, Value) {
        let (_, flags, writes) = client(plan);
        (flags, serde_json::from_str(&writes[0].1).unwrap())
    }

    #[test]
    fn init_binds_the_delivered_provisioning_context_and_a_session_namespace() {
        let (root, s) = temp_session("init");
        assert!(matches!(plan(&s, "init mini.key 42").unwrap(), Plan::NotHere(_)));
        fs::create_dir_all(s.home.join("provision")).unwrap();
        fs::write(s.home.join("provision").join("birth-context.json"), b"{}").unwrap();
        let home = s.home.display().to_string();
        let ws = s.workspace.display().to_string();
        assert_eq!(
            client(plan(&s, "init mini.key 42").unwrap()),
            (
                "workspace".into(),
                pairs(&[
                    ("action", "init"),
                    ("host", "/bin/host"),
                    ("config", "/c.json"),
                    ("key", &format!("{home}/keys/mini.key")),
                    ("subject", "42"),
                    ("birth-context", &format!("{home}/provision/birth-context.json")),
                    ("namespace-root", &format!("{home}/namespace")),
                    ("dir", &ws),
                ]),
                vec![]
            )
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn document_reads_and_push_accept_room_references() {
        let s = session();
        for line in ["doc show room/notes", "doc outline room/notes", "doc history room/notes",
            "doc pull room/notes", "doc push edit1 room/notes @notes.md"] {
            assert!(plan(&s, line).is_ok(), "{line}");
        }
        for line in ["doc show ../notes", "doc show room//notes", "doc push ../edit room/notes @notes.md"] {
            assert!(plan(&s, line).is_err(), "{line}");
        }
    }

    #[test]
    fn revoke_spells_the_revoke_proposal() {
        let s = session();
        let (flags, request) = request_of(plan(&s, "revoke cut shared 11033321548135836207").unwrap());
        assert_eq!(flags[0], ("action".into(), "propose".into()));
        assert_eq!(flags[3], ("proposal-id".into(), "cut".into()));
        assert_eq!(
            request,
            json!({"type":"minidregg-workspace-proposal-v1","action":"revoke","name":"shared",
                "recipient":"11033321548135836207"})
        );
        assert!(plan(&s, "revoke cut shared someone").is_err());
        assert_eq!(plan(&s, "revoke cut shared").unwrap_err(), usage_of("revoke"));
    }

    #[test]
    fn doc_push_and_pull_are_one_client_operation_each() {
        let s = session();
        assert_eq!(
            client(plan(&s, "doc pull paper").unwrap()).1,
            pairs(&[("action", "doc-pull"), ("dir", "/w"), ("name", "paper")])
        );
        let home_file = s.home.join("requests").join("p.md");
        let (command, flags, writes) = client(plan(&s, "doc push p1 paper @p.md").unwrap());
        assert_eq!(command, "workspace");
        assert!(writes.is_empty());
        assert_eq!(
            flags,
            pairs(&[
                ("action", "doc-push"),
                ("dir", "/w"),
                ("name", "paper"),
                ("file", home_file.to_str().unwrap()),
                ("proposal-id", "p1"),
                ("attempt", "/w/attempts/p1"),
            ])
        );
        assert_eq!(client(plan(&s, "doc push p1 paper @-").unwrap()).1[3], pairs(&[("file", "-")])[0]);
        for bad in ["doc pull", "doc push p1 paper p.md", "doc push p1 paper @../x", "doc push p1 paper",
            "doc push ../p paper @p.md"] {
            assert!(plan(&s, bad).is_err(), "{bad}");
        }
        assert_eq!(complete(&s, "doc pu"), ["pull", "push"]);
    }

    #[test]
    fn doc_verbs_are_one_client_operation_each() {
        let s = session();
        let (command, flags, writes) = client(plan(&s, "doc new paper").unwrap());
        assert_eq!(command, "workspace");
        assert_eq!(
            flags,
            pairs(&[
                ("action", "doc-new"),
                ("dir", "/w"),
                ("name", "paper"),
                ("predicate", "/h/requests/create-paper.json"),
            ])
        );
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law, document_law("draft").unwrap());
        let (_, _, writes) = client(plan(&s, "doc new log note").unwrap());
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law["predicates"][1]["predicates"][1],
            json!({"type":"eq","slot":"content/atom-edits","value":"0"}));
        assert!(plan(&s, "doc new log chaos").is_err());
        assert_eq!(
            client(plan(&s, "doc show paper").unwrap()).1,
            pairs(&[("action", "doc-show"), ("dir", "/w"), ("name", "paper")])
        );
        assert_eq!(
            client(plan(&s, "doc backlinks paper").unwrap()).1,
            pairs(&[("action", "doc-backlinks"), ("dir", "/w"), ("name", "paper")])
        );
        let (flags, request) = request_of(plan(&s, "doc append p1 paper 'first paragraph'").unwrap());
        assert_eq!(flags[2], ("request".into(), "/h/requests/p1.json".into()));
        assert_eq!(
            request,
            json!({"type":"minidregg-workspace-proposal-v1","action":"invoke","targets":[{"name":"paper",
                "payload":{"type":"document","actions":[{"type":"append","text":"first paragraph"}]}}]})
        );
        let (_, request) = request_of(plan(&s, "doc edit e1 paper 2 'better'").unwrap());
        assert_eq!(request["targets"][0]["payload"]["actions"][0],
            json!({"type":"edit","line":"2","text":"better"}));
        let (_, request) = request_of(plan(&s, "doc link l1 index paper").unwrap());
        assert_eq!(request["targets"][0]["name"], "index");
        assert_eq!(request["targets"][0]["payload"]["actions"][0],
            json!({"type":"link","to":"paper","relation":"0"}));
        let (_, request) = request_of(plan(&s, "doc link l2 index paper 3").unwrap());
        assert_eq!(request["targets"][0]["payload"]["actions"][0]["relation"], "3");
        let (_, request) = request_of(plan(&s, "doc annotate n1 paper 2 'cite this'").unwrap());
        assert_eq!(request["targets"][0]["payload"]["actions"][0],
            json!({"type":"annotate","line":"2","text":"cite this"}));
        // quote is gone: transclude replaces it (K-TRANSCLUDE)
        assert!(plan(&s, "doc quote paper wall 1").is_err());
        // The element-tree, history and rendering verbs: one workspace action each.
        for (line, want) in [
            ("doc show paper --at 77 --html", vec![("action", "doc-show"), ("dir", "/w"), ("name", "paper"),
                ("at", "77"), ("format", "html")]),
            ("doc history paper", vec![("action", "doc-history"), ("dir", "/w"), ("name", "paper")]),
            ("doc diff paper 77 81", vec![("action", "doc-diff"), ("dir", "/w"), ("name", "paper"),
                ("from", "77"), ("to", "81")]),
            ("doc links paper", vec![("action", "doc-links"), ("dir", "/w"), ("name", "paper")]),
            ("doc insert paper 2 'a new line'", vec![("action", "doc-insert"), ("dir", "/w"), ("name", "paper"),
                ("at", "2"), ("text", "a new line")]),
            ("doc move paper 3 1", vec![("action", "doc-move"), ("dir", "/w"), ("name", "paper"),
                ("from", "3"), ("to", "1")]),
            ("doc remove paper 2", vec![("action", "doc-remove"), ("dir", "/w"), ("name", "paper"), ("line", "2")]),
            ("doc mark paper 2 bold", vec![("action", "mark"), ("dir", "/w"), ("name", "paper"), ("line", "2"),
                ("kind", "bold")]),
            ("doc range notes 2 3", vec![("action", "doc-range"), ("dir", "/w"), ("name", "notes"),
                ("from", "2"), ("to", "3")]),
            ("doc transclude paper notes 2 3 live at 2", vec![("action", "transclude"), ("dir", "/w"),
                ("name", "paper"), ("source", "notes"), ("from-line", "2"), ("to-line", "3"), ("mode", "live"),
                ("at", "2")]),
            ("doc follow paper 77", vec![("action", "follow"), ("dir", "/w"), ("name", "paper"),
                ("transclusion", "77")]),
        ] {
            assert_eq!(client(plan(&s, line).unwrap()).1, pairs(&want), "{line}");
        }
        // The grammar refuses an unknown mark kind by name before any client operation.
        let unknown = plan(&s, "doc mark paper 2 underline").unwrap_err();
        assert!(unknown.contains("must be one of") && unknown.contains("underline"), "{unknown}");
        assert!(plan(&s, "doc show ../paper").is_err());
        for bad in ["doc", "doc show", "doc append p1 paper", "doc edit e1 paper x 'y'",
            "doc append p1 ../paper x", "doc append p1 paper @../../etc/passwd", "doc link l1 a b c"] {
            assert!(plan(&s, bad).is_err(), "{bad} should be refused");
        }
    }

    #[test]
    fn room_verbs_are_one_client_operation_each() {
        let (root, s) = temp_session("room");
        fs::write(s.workspace.join("workspace.json"), br#"{"subject":"7"}"#).unwrap();
        let (command, flags, writes) = client(plan(&s, "room new lab").unwrap());
        assert_eq!(command, "workspace");
        let requests = s.home.join("requests");
        let law_path = requests.join("room-lab.json");
        let fields = crate::credit::room_declared_fields();
        assert_eq!(
            flags,
            pairs(&[
                ("action", "create"),
                ("dir", s.workspace.to_str().unwrap()),
                ("name", "lab"),
                ("storage", "declared"),
                ("predicate", law_path.to_str().unwrap()),
                ("room-template", "open"),
                ("fields", &fields),
            ])
        );
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law, json!({"type":"all","predicates":[]}));
        let (_, flags, writes) =
            client(plan(&s, "room new tide --law realm --referee 9 --in lab").unwrap());
        assert!(flags.contains(&("in".into(), "lab".into())));
        assert!(flags.contains(&("room-template".into(), "realm".into())));
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law["predicates"][0],
            json!({"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"10"}}));
        assert_eq!(law["predicates"][1],
            json!({"type":"memberOf","slot":"request/subject","values":["7","9"]}));
        // An observe grant at ceiling 0 covers no read: refused by name; a mutate-only 0 and an observe above 0 are not.
        let refused = plan(&s, "delegate d0 lab 12 observe 0").err().unwrap();
        assert!(refused.contains("ceiling of 0 covers no read"), "{refused}");
        assert!(plan(&s, "delegate d0 lab 12 observe,mutate 000").is_err());
        assert!(plan(&s, "delegate d1 lab 12 observe 50000").is_ok());
        assert!(plan(&s, "delegate d2 lab 12 mutate 0").is_ok());
        let (_, request) = request_of(plan(&s, "room invite i1 lab 12").unwrap());
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
            "name":"lab","recipient":"12","verbs":["observe","place"],"maxCost":"50000","room":true}));
        let (_, request) = request_of(plan(&s,
            "room invite i2 lab 12 --verbs observe,place,delegate --fields 1,annotations --max-delta 7=50").unwrap());
        assert_eq!(request["verbs"], json!(["observe","place","delegate"]));
        assert_eq!(request["fields"], json!(["1","annotations"]));
        assert_eq!(request["maxDelta"], json!([{"field":"7","max":"50"}]));
        // A kick enumerates every standing grant the member holds (room-kick).
        assert_eq!(client(plan(&s, "room kick k1 lab 12").unwrap()).1,
            pairs(&[("action", "room-kick"), ("dir", s.workspace.to_str().unwrap()), ("name", "lab"),
                ("member", "12"), ("proposal-id", "k1")]));
        // Sealing a room says what it costs and needs --freeze-roster.
        assert!(plan(&s, "room seal s1 lab").unwrap_err().contains("--freeze-roster"));
        let (flags, request) = request_of(plan(&s, "room seal s1 lab --freeze-roster").unwrap());
        assert_eq!(request["predicate"], json!({"type":"any","predicates":[]}));
        assert!(flags.contains(&("freeze-roster".into(), "true".into())));
        let (flags, _) = request_of(plan(&s, "law s2 lab sealed --allow-unsatisfiable --freeze-roster").unwrap());
        assert!(flags.contains(&("freeze-roster".into(), "true".into())));
        assert!(flags.contains(&("allow-unsatisfiable".into(), "true".into())));
        assert_eq!(client(plan(&s, "room members lab").unwrap()).1,
            pairs(&[("action", "who"), ("dir", s.workspace.to_str().unwrap()), ("name", "lab")]));
        assert_eq!(client(plan(&s, "room law lab").unwrap()).1,
            pairs(&[("action", "describe"), ("dir", s.workspace.to_str().unwrap()), ("name", "lab")]));
        assert_eq!(plan(&s, "room list").unwrap(), Plan::Rooms);
        let (_, flags, _) = client(plan(&s, "doc new notes --in lab").unwrap());
        assert_eq!(flags.last().unwrap(), &("in".to_owned(), "lab".to_owned()));
        let (_, flags, _) = client(plan(&s, "doc new log note --in lab").unwrap());
        assert_eq!(flags.last().unwrap(), &("in".to_owned(), "lab".to_owned()));
        let (_, flags, _) = client(plan(&s, "create c1 declared {} --in lab").unwrap());
        assert_eq!(flags.last().unwrap(), &("in".to_owned(), "lab".to_owned()));
        assert!(plan(&s, "doc new notes --in ../lab").is_err());
        // Names under a room; a document's own law; a stream born for another owner.
        let (_, flags, writes) =
            client(plan(&s, "doc new lab/index 'any [ not (verb == write), subject == 7 ]' --in lab").unwrap());
        assert!(flags.contains(&("name".into(), "lab/index".into())));
        assert_eq!(writes[0].0, requests.join("create-lab.index.json"));
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law["predicates"][1], json!({"type":"eq","slot":"request/subject","value":"7"}));
        let (_, flags, _) =
            client(plan(&s, "create lab/stream-12 stream 'subject == 12' --owner 12 --in lab").unwrap());
        assert!(flags.contains(&("owner".into(), "12".into())));
        assert!(flags.contains(&("in".into(), "lab".into())));
        assert!(flags.contains(&("name".into(), "lab/stream-12".into())));
        for bad in ["doc new lab/ draft", "doc new /lab draft", "doc new lab//x draft", "doc new lab.x draft",
            "create s stream open --owner x", "create s stream open --in lab --in lab", "doc new d draft --owner 12"] {
            assert!(plan(&s, bad).is_err(), "{bad} should be refused");
        }
        // A placement law names 64-bit subjects.
        let (_, request) = request_of(plan(&s,
            "law l2 lab any [ not (verb == place), subject in {15893985203478182741} ]").unwrap());
        assert_eq!(request["predicate"]["predicates"][0]["predicate"]["value"], "10");
        assert_eq!(request["predicate"]["predicates"][1]["values"], json!(["15893985203478182741"]));
        let (_, request) = request_of(plan(&s, "room leave l1 lab").unwrap());
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"renounce",
            "name":"lab","leave":true}));
        assert_eq!(plan(&s, "room leave lab").unwrap_err(), usage_of("room"));
        let (_, request) = request_of(plan(&s, "renounce r1 77 account").unwrap());
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"renounce",
            "capability":"77","kind":"account"}));
        let (_, request) = request_of(plan(&s, "renounce r2 lab").unwrap());
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"renounce",
            "name":"lab"}));
        assert_eq!(plan(&s, "renounce r3 77 cell").unwrap_err(), usage_of("renounce"));
        assert_eq!(plan(&s, "renounce r3 lab object").unwrap_err(), usage_of("renounce"));
        for bad in ["room", "room new", "room new lab --template castle", "room new lab --referee 9",
            "room new lab --law workroom", "room new lab --template workroom --law open",
            "room new lab --bogus 1", "room invite i1 lab", "room invite i1 lab x",
            "room invite i1 lab 12 --max-delta 7", "room kick k1 lab", "room members", "room list x"] {
            assert!(plan(&s, bad).is_err(), "{bad} should be refused");
        }
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn private_room_verbs_spell_the_room_key_operations() {
        let (root, s) = temp_session("private");
        fs::write(s.workspace.join("workspace.json"), br#"{"subject":"7"}"#).unwrap();
        fs::create_dir_all(s.workspace.join("refs")).unwrap();
        fs::write(s.workspace.join("refs").join("lab.json"),
            br#"{"name":"lab","room":"private","private":{"keys":"99"}}"#).unwrap();
        fs::write(s.workspace.join("refs").join("pub.json"), br#"{"name":"pub","room":"workroom"}"#).unwrap();
        let (_, flags, writes) = client(plan(&s, "room new lab2 --private").unwrap());
        assert!(flags.contains(&("room-template".into(), "private".into())));
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law, crate::workspace::roomkey::room_law());
        let enc = "ab".repeat(32);
        let (command, flags, writes) =
            client(plan(&s, &format!("room invite i1 lab 12 {enc} --past --verbs observe,place,append")).unwrap());
        assert_eq!(command, "workspace");
        let request_path = s.home.join("requests").join("i1.json");
        assert_eq!(flags, pairs(&[("action", "room-key"), ("op", "invite"),
            ("dir", s.workspace.to_str().unwrap()), ("name", "lab"), ("member", "12"),
            ("enc-pub", enc.as_str()), ("proposal-id", "i1"), ("request", request_path.to_str().unwrap()),
            ("past", "true")]));
        let request: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
            "name":"lab","recipient":"12","verbs":["observe","place","append"],"maxCost":"50000","room":true}));
        fs::create_dir_all(s.home.join("requests")).unwrap();
        fs::write(s.home.join("requests").join("bob.enc"), format!("{enc}\n")).unwrap();
        let (_, flags, _) = client(plan(&s, "room invite i2 lab 12 @bob.enc --i-know").unwrap());
        assert!(flags.contains(&("i-know".into(), "true".into())));
        assert!(flags.contains(&("enc-pub".into(), enc.clone().into())));
        let (_, flags, _) = client(plan(&s, "room kick k1 lab 12").unwrap());
        assert_eq!(flags, pairs(&[("action", "room-key"), ("op", "kick"),
            ("dir", s.workspace.to_str().unwrap()), ("name", "lab"), ("member", "12"), ("proposal-id", "k1")]));
        // A public room's kick is the room-kick enumeration, not submitted.
        let (_, flags, _) = client(plan(&s, "room kick k2 pub 12").unwrap());
        assert!(flags.contains(&("action".into(), "room-kick".into())));
        assert_eq!(client(plan(&s, "room keys lab").unwrap()).1, pairs(&[("action", "room-key"),
            ("op", "list"), ("dir", s.workspace.to_str().unwrap()), ("name", "lab")]));
        assert_eq!(client(plan(&s, "room rotate r1 lab").unwrap()).1, pairs(&[("action", "room-key"),
            ("op", "rotate"), ("dir", s.workspace.to_str().unwrap()), ("name", "lab"), ("proposal-id", "r1")]));
        assert_eq!(client(plan(&s, "forget lab 0").unwrap()).1, pairs(&[("action", "room-key"),
            ("op", "forget"), ("dir", s.workspace.to_str().unwrap()), ("name", "lab"), ("epoch", "0")]));
        for bad in ["room invite i3 lab 12", "room invite i3 lab 12 abcd",
            &format!("room invite i3 pub 12 {enc}"), "room invite i3 pub 12 --i-know",
            "room new lab3 --private --template realm", "forget", "forget lab x", "room keys"] {
            assert!(plan(&s, bad).is_err(), "{bad} should be refused");
        }
        let _ = fs::remove_dir_all(root);
    }

    #[test]
    fn board_verbs_spell_numbered_task_fields_under_the_board_law() {
        let (root, s) = temp_session("board");
        let (_, flags, writes) = client(plan(&s, "board new tasks").unwrap());
        assert_eq!(flags[3], ("storage".into(), "declared".into()));
        let law: Value = serde_json::from_str(&writes[0].1).unwrap();
        assert_eq!(law, board_law());
        let mutate = &law["predicates"][1]["predicates"];
        assert_eq!(mutate[1], json!({"type":"not","predicate":{"type":"le","slot":"resource/field/2/delta","value":"-1"}}));
        assert_eq!(mutate[2], json!({"type":"writeOnce","slot":"resource/field/3/after"}));
        assert_eq!(mutate[4], json!({"type":"writeOnce","slot":"resource/field/5/after"}));
        let (_, request) = request_of(plan(&s, "board add t1 tasks 1").unwrap());
        assert_eq!(request["targets"][0]["payload"]["actions"][0],
            json!({"type":"create","key":{"type":"object","field":"4"},"value":"0"}));
        let (_, request) = request_of(plan(&s, "board move m1 tasks 0 todo doing").unwrap());
        assert_eq!(request["targets"][0]["payload"]["actions"][0],
            json!({"type":"write","key":{"type":"object","field":"2"},"value":"1","expected":"0"}));
        assert!(plan(&s, "board move m1 tasks 1 todo sideways").is_err());
        assert!(plan(&s, "board take k1 tasks 0").unwrap_err().contains("init first"));
        fs::write(s.workspace.join("workspace.json"), br#"{"subject":"11033321548135836207"}"#).unwrap();
        let (_, request) = request_of(plan(&s, "board take k1 tasks 0").unwrap());
        assert_eq!(request["targets"][0]["payload"]["actions"][0],
            json!({"type":"create","key":{"type":"object","field":"3"},"value":"11033321548135836207"}));
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn private_compute_takes_two_bounded_values_and_is_a_local_client_call() {
        let s = session();
        let (command, flags, writes) = client(plan(&s, "private-compute 173 59").unwrap());
        assert_eq!((command.as_str(), flags, writes), ("private-compute", pairs(&[("left", "173"), ("right", "59")]), vec![]));
        for bad in ["private-compute", "private-compute 1", "private-compute 1 2 3", "private-compute 256 1", "private-compute 1 x", "private-compute -1 2"] {
            assert!(plan(&s, bad).is_err(), "{bad}");
        }
        let g = crate::shell_grammar::grammar("private-compute").unwrap();
        assert_eq!(g.leaves[0].effect, crate::shell_grammar::Effect::Local);
        assert!(crate::shell_grammar::operation(g).contains("RESEARCH"));
    }

    #[test]
    fn inbox_and_guide_are_local() {
        let s = session();
        assert_eq!(plan(&s, "inbox").unwrap(), Plan::Inbox);
        assert_eq!(plan(&s, "help guide").unwrap(), Plan::Guide);
        assert_eq!(plan(&s, "help doc").unwrap(), Plan::Help(Some("doc".into())));
        assert!(plan(&s, "inbox all").is_err());
    }

    #[test]
    fn app_export_uses_the_existing_exact_connector_operation() {
        let s=session();
        assert_eq!(client(plan(&s,"doc app-export capture sheet-one @binding.json").unwrap()),
            ("workspace".into(),pairs(&[("action","app-document"),("dir","/w"),("op","capture"),("id","sheet-one"),("binding","/h/requests/binding.json")]),vec![]));
        assert_eq!(client(plan(&s,"doc app-export recover sheet-one").unwrap()),
            ("workspace".into(),pairs(&[("action","app-document"),("dir","/w"),("op","recover"),("id","sheet-one")]),vec![]));
        assert!(plan(&s,"doc app-export capture sheet-one @../foreign.json").is_err());
        assert!(plan(&s,"doc app-export publish sheet-one extra").is_err());
    }

    #[test]
    fn app_status_routes_current_readonly_member_admission() {
        let s=session();
        let p=client(plan(&s,"app status sheet --json").unwrap());
        assert_eq!(p.0,"member");
        assert!(p.1.contains(&("action".into(),"app-status".into())));
        assert!(p.1.contains(&("name".into(),"sheet".into())));
        assert!(plan(&s,"app status sheet extra").is_err());
        assert!(plan(&s,"app submit sheet").is_err());
    }
    #[test]
    fn home_checks_only_the_selected_member_reference() {
        let s = session();
        assert_eq!(client(plan(&s,"home lab --json").unwrap()),
            ("member".into(),pairs(&[("dir","/w"),("home","/h"),("name","lab"),("json","true")]),vec![]));
        assert_eq!(client(plan(&s,"home").unwrap()),
            ("member".into(),pairs(&[("dir","/w"),("home","/h")]),vec![]));
        assert!(plan(&s,"home lab other").is_err());
    }

    #[test]
    fn every_owned_command_is_discoverable_in_help_completion() {
        let s = session();
        let help = complete(&s, "help ");
        for command in command_catalog() {
            assert!(help.contains(&command.name.to_owned()), "{} missing from help completion", command.name);
            assert!(!help_text(Some(command.name)).starts_with("no verb"));
        }
    }

    #[test]
    fn app_lifecycle_uses_owner_workspace_custody_and_rejects_seed_options() {
        let s=session();
        let p=client(plan(&s,"app delegate-lifecycle prepare manager-delegation sheet --package package --snapshot snapshot --manager 8").unwrap());
        assert_eq!(p.0,"workspace");
        assert!(p.1.contains(&("action".into(),"app-lifecycle".into())));
        assert!(p.1.contains(&("request-id".into(),"manager-delegation".into())));
        assert!(p.1.contains(&("package-name".into(),"package".into())));
        let recovered=client(plan(&s,"app delegate-lifecycle recover manager-delegation").unwrap());
        assert!(recovered.1.contains(&("op".into(),"recover".into())));
        assert!(!recovered.1.iter().any(|(name,_)|name=="manager" || name=="name"));
        assert!(plan(&s,"app delegate-lifecycle prepare manager-delegation sheet --package package --snapshot snapshot --seed owner.key").is_err());
        assert!(plan(&s,"app delegate-lifecycle prepare ../foreign sheet --package package --snapshot snapshot --manager 8").is_err());
    }

    #[test]
    fn module_subcommands_are_derived_from_their_actual_usage() {
        let s = session();
        assert!(complete(&s, "key p").contains(&"providers".to_owned()));
        assert!(complete(&s, "key c").contains(&"choose".to_owned()));
        assert!(complete(&s, "room st").contains(&"status".to_owned()));
        assert!(complete(&s, "chat e").contains(&"enter".to_owned()));
        assert!(help_text(Some("doc")).contains("doc app-export"));
        assert!(complete(&s, "doc app-").contains(&"app-export".to_owned()));
        assert!(complete(&s, "doc app-export re").contains(&"recover".to_owned()));
        assert!(complete(&s, "doc q").is_empty());
        assert!(plan(&s,"doc quote paper notes 1 2").is_err());
        assert!(complete(&s, "app de").contains(&"delegate-lifecycle".to_owned()));
        assert!(complete(&s, "app delegate-lifecycle re").contains(&"recover".to_owned()));
        assert!(complete(&s, "app st").contains(&"status".to_owned()));
    }

    #[test]
    fn the_custody_banner_is_the_same_data_in_help_and_at_start() {
        let s = session();
        let help = help_text(None);
        let start = start_text(&s);
        assert_eq!(help.lines().next(), Some(HOSTED_CUSTODY_BANNER));
        assert_eq!(start.lines().next(), Some(HOSTED_CUSTODY_BANNER));
        assert!(HOSTED_CUSTODY_BANNER.contains("root can read and sign"));
        assert!(HOSTED_CUSTODY_BANNER.contains("mini --remote"));
        // The banner is text the shell prints, never an ending it classifies.
        assert_eq!(render(&Ending::Done), (EXIT_OK, String::new()));
    }

    #[test]
    fn every_private_room_entry_point_carries_the_disclaimer() {
        use crate::workspace::private::PRIVACY_DISCLAIMER;
        assert_eq!(PRIVACY_DISCLAIMER, "devnet quality; privacy not audited");
        let said = |text: &str| text.to_lowercase().contains(PRIVACY_DISCLAIMER);
        // Every verb that makes, joins or runs a private room.
        let mut seen = Vec::new();
        for verb in command_catalog().filter(|v| v.usage.contains("--private") || v.usage.contains("room-key")
            || v.operation.contains("room-key") || v.operation.contains("private")) {
            assert!(said(&format!("{} {}", verb.usage, verb.operation)), "verb {} lacks the private-room disclaimer", verb.name);
            seen.push(verb.name);
        }
        assert!(seen.contains(&"room") && seen.contains(&"chat"), "{seen:?}");
        for topic in ["chat", "room"] {
            assert!(said(&help_text(Some(topic))), "help {topic}");
        }
    }

    #[test]
    fn a_hosted_subject_joins_a_private_room_only_with_i_know() {
        use crate::workspace::roomkey::hosted_private_invite;
        assert!(hosted_private_invite(true, true, false).unwrap_err().contains("--i-know"));
        assert!(hosted_private_invite(true, true, true).is_ok());
        assert!(hosted_private_invite(true, false, false).is_ok());
        assert!(hosted_private_invite(false, true, false).is_ok());
        let mut w = words("room invite r1 42 --i-know").unwrap();
        assert!(take_switch(&mut w, "--i-know"));
        assert_eq!(w, ["room", "invite", "r1", "42"]);
        let mut w = words("room invite r1 42").unwrap();
        assert!(!take_switch(&mut w, "--i-know"));
        assert_eq!(w.len(), 4);
    }
    #[test]
    fn protected_document_membership_stays_inside_member_requests() {
        let s=session();
        assert!(plan(&s,"doc share add-bob paper 42 @device.json @invite.json").is_ok());
        assert!(plan(&s,"doc accept paper catalog @invite.json").is_ok());
        assert!(plan(&s,"doc revoke remove-bob paper 42").is_ok());
        assert!(plan(&s,"doc membership-recover add-bob paper @invite.json").is_ok());
        assert!(plan(&s,"doc share add-bob paper 42 @../../device.json @invite.json").is_err());
        assert!(plan(&s,"doc accept paper catalog @/tmp/invite.json").is_err());
    }

}
