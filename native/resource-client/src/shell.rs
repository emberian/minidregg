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
use std::fs::{self, OpenOptions};
use std::io::{self, BufRead, IsTerminal, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

pub(crate) mod law;
mod template;

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
    Verb { name: "whoami", usage: "whoami", operation: "local: this session's workspace, home, subject and encryption public key (what an inviter to a private room wraps to)" },
    Verb { name: "keygen", usage: "keygen FILE", operation: "mini keygen --secret HOME/keys/FILE --public HOME/keys/FILE.pub (also the NEXT key HOME/keys/FILE.next: move it off this box)" },
    Verb { name: "key-status", usage: "key-status", operation: "mini key-status --workspace WORKSPACE: key epoch, whether a next key is committed, whether HOME/keys/<key>.next.pub matches it" },
    Verb { name: "rotate-key", usage: "rotate-key NEXTFILE", operation: "mini rotate-key --workspace WORKSPACE --next-key HOME/keys/NEXTFILE: rotate to the committed next key; NEXTFILE then holds the key after it" },
    Verb { name: "init", usage: "init KEYFILE SUBJECT [--no-prerotation]", operation: "mini workspace --action init --key HOME/keys/KEYFILE --subject SUBJECT --birth-context HOME/provision/birth-context.json --namespace-root HOME/namespace (refuses a subject whose committed next key is not HOME/keys/KEYFILE.next.pub)" },
    Verb { name: "enroll", usage: "enroll plan NAME KEYFILE|PUBLIC-KEY-HEX NEXT-PUBLIC-KEY-HEX COSIGN-HEX|--no-prerotation [FACTORY-REF] | enroll offer NAME | enroll seal NAME [SIGNATURE-HEX] | enroll submit|lookup NAME | enroll welcome NAME", operation: "mini enroll --action plan|offer|seal|submit|lookup|welcome --dir HOME/enroll/NAME (a hex public key plans with --new-public-key: the newcomer's secret stays on their machine)" },
    Verb { name: "provision", usage: "provision NAME HOLDER FUNDING PREDICATE-JSON|@FILE [FACTORY-REF]", operation: "mini workspace --action provision --name NAME --holder HOLDER --funding FUNDING --account-predicate HOME/requests/provision-NAME.json" },
    Verb { name: "refs", usage: "refs", operation: "mini workspace --action list" },
    Verb { name: "read", usage: "read REF", operation: "mini workspace --action read --name REF" },
    Verb { name: "can", usage: "can [REF] [--all] | can --any REF", operation: "mini workspace --action can [--name REF] [--all true]: each verb my grants cover, prepared and dry-run (Host op 130), never submitted | --any: one write REF's law admits from its current values, as a line to paste, or the clauses that rule every write out (Host op 150)" },
    Verb { name: "inspect", usage: "inspect caps [REF] | inspect law REF | inspect receipt ID | inspect turn ID  [--json]", operation: "mini workspace --action inspect --view caps|law|receipt|turn [--name REF|ID] [--json true]: a Lean view (Host inspect cap-tree|law|receipt|turn) over bytes this workspace holds or reads with its own signed views; turn dry-runs (op 130), nothing is submitted" },
    Verb { name: "why", usage: "why [ATTEMPT] [--json]", operation: "mini workspace --action inspect --view why [--name ATTEMPT] --refusals HOME/refusals: the last refusal held, explained from the Host's own frame (clause, slot values, the request value that passes it)" },
    Verb { name: "describe", usage: "describe REF", operation: "mini workspace --action describe --name REF" },
    Verb { name: "import", usage: "import NAME REFERENCE-JSON|@FILE | import NAME KIND TARGET OBSERVE [OPERATION|- [CONTROL]]", operation: "mini workspace --action import (--from-ref | --kind --target --observe-capability)" },
    Verb { name: "create", usage: "create NAME STORAGE LAW|PREDICATE-JSON|@FILE [--in ROOM] [--owner SUBJECT]", operation: "mini workspace --action create [--in ROOM] [--owner SUBJECT]" },
    Verb { name: "propose", usage: "propose ID REQUEST-JSON|@FILE", operation: "mini workspace --action propose --proposal-id ID" },
    Verb { name: "invoke", usage: "invoke ID REF create FIELD VALUE | invoke ID REF write FIELD VALUE EXPECTED", operation: "mini workspace --action propose (action invoke, one scalar action)" },
    Verb { name: "delegate", usage: "delegate ID REF RECIPIENT VERB[,VERB...] MAX-COST", operation: "mini workspace --action propose (action delegate)" },
    Verb { name: "law", usage: "law ID REF \"CLAUSE; CLAUSE; …\"|PREDICATE-JSON|@FILE [--allow-unsatisfiable] | law check \"CLAUSE; …\"|PREDICATE-JSON|@FILE|-", operation: "mini workspace --action propose (action install-policy), after asking the Host whether the law can ever pass (op 150): a law no step can satisfy is not proposed, and the reply names the clauses that contradict (--allow-unsatisfiable installs it anyway: `sealed` is such a law on purpose); a law no write can pass is proposed with a warning | check: the same question without installing (- reads the law from standard input)" },
    Verb { name: "submit", usage: "submit ID", operation: "mini workspace --action submit --intent proposals/ID/intent.json --attempt attempts/ID" },
    Verb { name: "lookup", usage: "lookup ID", operation: "mini workspace --action recover --attempt attempts/ID" },
    Verb { name: "retry", usage: "retry ID", operation: "mini retry --attempt attempts/ID --mode submit" },
    Verb { name: "publish", usage: "publish ID", operation: "mini workspace --action publish-delegation --proposal-id ID --attempt attempts/ID" },
    Verb { name: "revoke", usage: "revoke ID REF RECIPIENT", operation: "mini workspace --action propose (action revoke: the capability this workspace delegated on REF to RECIPIENT)" },
    Verb { name: "renounce", usage: "renounce ID REF | renounce ID CAPABILITY [object|account|program]", operation: "mini workspace --action propose (action renounce: give up a capability you hold, and with it everything delegated from it)" },
    Verb { name: "doc", usage: "doc new NAME [draft|note|LAW] [--in ROOM] | doc show NAME | doc append ID NAME TEXT|@FILE | doc edit ID NAME LINE TEXT|@FILE | doc link ID FROM TO [RELATION] | doc backlinks NAME | doc annotate|quote …", operation: "mini workspace --action create (storage content) | doc-show | propose (payload document: append, edit, link) | doc-backlinks" },
    Verb { name: "room", usage: "room new NAME [--law open|realm] [--referee SUBJECT] [--in PARENT] | room new NAME --private [--in PARENT] | room new NAME --template workroom|social|story|@FILE | room welcome NAME SUBJECT --template T|@FILE | room template list | room template show T|@FILE [member] | room invite ID NAME SUBJECT [ENC-PUB|@FILE] [--past] [--i-know] [--verbs V,...] [--fields F,...] [--max-delta F=N,...] [--max-cost N] | room kick ID NAME SUBJECT | room rotate ID NAME | room register ID NAME | room rewrap ID NAME SUBJECT | room keys NAME | room leave ID NAME | room members NAME | room list | room ls [ROOM] [--since H] [--import] [--json] | room law NAME | room status NAME | room renew NAME SUBJECT [--for N|--until H] | room concierge NAME SUBJECT [--period N] [--fund N] | room new NAME [--template T] --concierge SUBJECT [--period N]", operation: "mini workspace --action create (storage declared, the room's law, --room-template LAW; private: + the room key, the keys cell, your own wrap) | the template's lines, each one typed line, in order | the template's member lines | local | local: print the template file | propose (action delegate, room: true; private: room-key --op invite, which also wraps the room key to ENC-PUB in one keys write) | propose (action revoke; private: room-key --op kick = revoke + rotate + rewrap, submitted) | room-key --op rotate | room-key --op list (local) | propose (action renounce, leave: your room grant) | who | local: references that are rooms | chat: the Host's signed since view under the room grant, with the roster's streams and my names (--import names the rest ROOM-cell-ID) | describe | mini credit --action status (my window, the tariff, the till; adopts a newer window from HOME/inbox) | mini credit --action renew (one delegation under the room with notAfter; copy in HOME/outbox/SUBJECT) | mini credit --action install (the till, the runner account, the tariff's account fields, the concierge's grants; program in HOME/concierge/NAME.json) | the room's lines, then `room concierge`" },
    Verb { name: "forget", usage: "forget ROOM [EPOCH]", operation: "mini workspace --action room-key --op forget: delete this client's copies of a private room's keys (all epochs, or one)" },
    Verb { name: "board", usage: "board new NAME | board add ID BOARD TASK | board move ID BOARD TASK FROM TO | board take ID BOARD TASK", operation: "mini workspace --action create (storage declared, the board law) | propose (action invoke: task TASK state is field 2*TASK+2, owner field 2*TASK+3)" },
    Verb { name: "inbox", usage: "inbox", operation: "local: the delegated references in HOME/inbox, whether addressed to this subject and whether imported" },
    Verb { name: "export", usage: "export ID", operation: "local: print proposals/ID/recipient-reference.json" },
    Verb { name: "pay", usage: "pay ROOM week|N [--account REF] | pay address [ACCOUNT-REF] | pay status [ACCOUNT-REF] | pay audit", operation: "mini credit --action pay --room ROOM [--amount N] (one fleet turn: N, or the room's week, to its till, publishing renew; a free room files a request in HOME/outbox) | mini pay --action address|status|audit --dir WS [--account REF]" },
    Verb { name: "credit", usage: "credit [ACCOUNT-REF]", operation: "mini credit --action balance (a signed read of my account)" },
    Verb { name: "tariff", usage: "tariff ROOM | tariff ROOM set week|birth|hermes/turn|period N", operation: "mini credit --action tariff --room ROOM [--set FIELD --value N] (a signed read of the room cell's tariff fields | one scalar turn on the room cell: only its founder holds write)" },
    Verb { name: "topup", usage: "topup ROOM N [hermes|concierge] [--account REF]", operation: "mini credit --action topup --room ROOM --amount N [--to hermes|concierge] (one fleet transfer to Hermes's budget account when the room has a Hermes, else to the concierge's runner account)" },
    Verb { name: "key", usage: crate::keys::SHELL_USAGE, operation: "mini key --action set|grant|revoke|ls --dir WORKSPACE (provider keys in hosted custody)" },
    Verb { name: "history", usage: "history [all]", operation: "local: retained attempts and their last Host outcome" },
    Verb { name: "help", usage: "help [VERB|guide]", operation: "local; `help guide` prints the friends' guide" },
    Verb { name: "exit", usage: "exit", operation: "local" },
];

/// What this shell is, stated as data: printed verbatim at the top of `help`
/// and when an interactive session starts. Nothing classifies it.
pub(crate) const HOSTED_CUSTODY_BANNER: &str = "hosted shell: your signing key is a file on this box; root can read and sign; for a key that never leaves your machine use `mini --remote` (see FRIENDS.md)";

/// Where the deployment installs the friends' guide (`deploy/shell/FRIENDS.md`).
pub(crate) const FRIENDS_GUIDE: &str = "/usr/local/lib/mini/FRIENDS.md";

/// Document laws a `doc new` chooses from. A cell has one law and it judges
/// every verb (reads and delegations carry no `content/*` slot), so each
/// content clause sits under `request/verb == 2` (mutate) and the other verbs
/// (observe 1, delegate 3, installPolicy 4, revoke 5) pass.
fn document_law(template: &str) -> Option<Value> {
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

/// `--name VALUE` pairs after the positional words of a `room` line.
fn room_flags(
    words: &[String],
    allowed: &[&str],
) -> std::result::Result<Vec<(String, String)>, String> {
    let mut out: Vec<(String, String)> = Vec::new();
    let mut i = 0;
    while i < words.len() {
        let name = words[i]
            .strip_prefix("--")
            .filter(|name| allowed.contains(name))
            .ok_or_else(|| format!("unknown room option {}", words[i]))?;
        let value = words
            .get(i + 1)
            .ok_or_else(|| format!("--{name} needs a value"))?;
        if out.iter().any(|(seen, _)| seen == name) && name != "referee" {
            return Err(format!("--{name} given twice"));
        }
        out.push((name.to_owned(), value.clone()));
        i += 2;
    }
    Ok(out)
}

fn room_flag<'a>(flags: &'a [(String, String)], name: &str) -> Option<&'a str> {
    flags.iter().find(|(seen, _)| seen == name).map(|(_, value)| value.as_str())
}

/// `room …`: each form is one client operation.
fn room_plan(session: &Session, w: &[String], u: &str) -> std::result::Result<Plan, String> {
    let ws = session.workspace.clone();
    let Some(action) = w.get(1) else {
        return Err(u.to_owned());
    };
    Ok(match action.as_str() {
        "new" => {
            let name = w.get(2).ok_or_else(|| u.to_owned())?;
            ref_name(name, "room name")?;
            let mut rest: Vec<String> = w[3..].to_vec();
            let private = take_switch(&mut rest, "--private");
            let flags = room_flags(&rest, &["law", "referee", "in", "template", "concierge", "period"])?;
            if private
                && ["law", "template", "concierge", "period"].iter().any(|f| room_flag(&flags, f).is_some())
            {
                return Err("--private is the private room's law (its keys cell, your wrap); it takes no --law, --template or --concierge".into());
            }
            // `--concierge SUBJECT [--period N]`: the room's lines, then one
            // `room concierge` line (P-CREDIT): the room is born first, then
            // its till, runner account and the concierge's grants.
            if let Some(concierge) = room_flag(&flags, "concierge") {
                decimal(concierge, "concierge subject")?;
                workspace_name(name, "a room with a concierge (its lines name proposals after it)")?;
                let mut first = format!("room new {name}");
                for (flag_name, value) in &flags {
                    if flag_name != "concierge" && flag_name != "period" {
                        first.push_str(&format!(" --{flag_name} {value}"));
                    }
                }
                let mut last = format!("room concierge {name} {concierge}");
                if let Some(period) = room_flag(&flags, "period") {
                    decimal(period, "period")?;
                    last.push_str(&format!(" --period {period}"));
                }
                let founder = session_subject(session)?;
                let text = match room_flag(&flags, "template") {
                    Some(spec) => {
                        let (_, text) = template::source(&session.home, spec, template::Part::Room)?;
                        format!("{text}\n{last}\n")
                    }
                    None => format!("{first}\n{last}\n"),
                };
                let label = format!("room {name} with a concierge");
                return template_plan(session, label, &text, &[("ROOM", name), ("ME", &founder)]);
            }
            if room_flag(&flags, "period").is_some() {
                return Err("--period is the concierge's week (--concierge SUBJECT --period N)".into());
            }
            if let Some(spec) = room_flag(&flags, "template") {
                if flags.len() != 1 {
                    return Err("--template is the whole room: its first line births the room with its law (room template show T); give no other option".into());
                }
                workspace_name(name, "a templated room's name (its lines name proposals after it)")?;
                let founder = session_subject(session)?;
                let (label, text) = template::source(&session.home, spec, template::Part::Room)?;
                return template_plan(session, label, &text, &[("ROOM", name), ("ME", &founder)]);
            }
            let law_name = if private { "private" } else { room_flag(&flags, "law").unwrap_or("open") };
            let referees: Vec<String> = flags
                .iter()
                .filter(|(flag, _)| flag == "referee")
                .map(|(_, value)| value.clone())
                .collect();
            for referee in &referees {
                decimal(referee, "referee")?;
            }
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
                flag("name", name.clone()),
                flag("storage", "declared"),
                flag("predicate", path.clone()),
                flag("room-template", law_name),
            ];
            if let Some(parent) = room_flag(&flags, "in") {
                ref_name(parent, "parent room")?;
                flags_out.push(flag("in", parent));
            }
            Plan::Client {
                command: "workspace".into(),
                flags: flags_out,
                writes: vec![request_file(path, &law)],
            }
        }
        "welcome" => {
            if w.len() < 4 {
                return Err(u.to_owned());
            }
            workspace_name(&w[2], "a templated room's name (its lines name proposals after it)")?;
            decimal(&w[3], "member")?;
            let flags = room_flags(&w[4..], &["template"])?;
            let spec = room_flag(&flags, "template")
                .ok_or_else(|| "room welcome runs a template's member lines: --template T".to_owned())?;
            let founder = session_subject(session)?;
            let (label, text) = template::source(&session.home, spec, template::Part::Member)?;
            return template_plan(
                session,
                label,
                &text,
                &[("ROOM", &w[2]), ("ME", &founder), ("MEMBER", &w[3])],
            );
        }
        "template" => match (w.get(2).map(String::as_str), w.get(4).map(String::as_str), w.len()) {
            (Some("list"), _, 3) => Plan::Text(template::list()),
            (Some("show"), _, 4) => Plan::Text(template::show(&session.home, &w[3], template::Part::Room)?),
            (Some("show"), Some("member"), 5) => {
                Plan::Text(template::show(&session.home, &w[3], template::Part::Member)?)
            }
            _ => return Err(u.to_owned()),
        },
        "invite" => {
            if w.len() < 5 {
                return Err(u.to_owned());
            }
            workspace_name(&w[2], "proposal ID")?;
            ref_name(&w[3], "room name")?;
            decimal(&w[4], "invitee")?;
            let private = room_is_private(session, &w[3]);
            let mut rest: Vec<String> = w[5..].to_vec();
            let enc = match rest.first() {
                Some(word) if !word.starts_with("--") => Some(rest.remove(0)),
                _ => None,
            };
            let past = take_switch(&mut rest, "--past");
            let i_know = take_switch(&mut rest, "--i-know");
            if !private && (enc.is_some() || past || i_know) {
                return Err(format!("{} is not a private room: ENC-PUB, --past and --i-know are a private room's", w[3]));
            }
            if private && enc.is_none() {
                return Err(format!("{} is private: name the invitee's encryption key (ENC-PUB, or @FILE in HOME/requests; the invitee's `whoami` prints it)", w[3]));
            }
            let flags = room_flags(&rest, &["verbs", "fields", "max-delta", "max-cost"])?;
            let verbs: Vec<&str> = room_flag(&flags, "verbs")
                .unwrap_or("observe,place")
                .split(',')
                .collect();
            let max_cost = room_flag(&flags, "max-cost").unwrap_or("50000");
            decimal(max_cost, "max cost")?;
            let mut request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                "name":w[3],"recipient":w[4],"verbs":verbs,"maxCost":max_cost,"room":true});
            if let Some(fields) = room_flag(&flags, "fields") {
                let fields: Vec<&str> = fields.split(',').collect();
                request["fields"] = json!(fields);
            }
            if let Some(bounds) = room_flag(&flags, "max-delta") {
                let mut out = Vec::new();
                for bound in bounds.split(',') {
                    let (field, max) = bound
                        .split_once('=')
                        .ok_or_else(|| "--max-delta is FIELD=N[,FIELD=N...]".to_owned())?;
                    decimal(max, "max delta")?;
                    out.push(json!({"field":field,"max":max}));
                }
                request["maxDelta"] = json!(out);
            }
            match enc {
                None => proposal(session, &w[2], &request),
                Some(enc) => {
                    let enc = enc_argument(session, &enc)?;
                    let path = session.home.join("requests").join(format!("{}.json", w[2]));
                    let mut flags = vec![
                        flag("action", "room-key"),
                        flag("op", "invite"),
                        flag("dir", ws),
                        flag("name", w[3].clone()),
                        flag("member", w[4].clone()),
                        flag("enc-pub", enc),
                        flag("proposal-id", w[2].clone()),
                        flag("request", path.clone()),
                    ];
                    if past {
                        flags.push(flag("past", "true"));
                    }
                    if i_know {
                        flags.push(flag("i-know", "true"));
                    }
                    Plan::Client {
                        command: "workspace".into(),
                        flags,
                        writes: vec![request_file(path, &request)],
                    }
                }
            }
        }
        "kick" => {
            arity(w, 4, 4, u)?;
            workspace_name(&w[2], "proposal ID")?;
            ref_name(&w[3], "room name")?;
            decimal(&w[4], "member")?;
            if room_is_private(session, &w[3]) {
                // Revoke, then rotate and rewrap, both submitted: the kicked
                // member keeps the past and gets nothing new.
                return Ok(Plan::Client {
                    command: "workspace".into(),
                    flags: vec![
                        flag("action", "room-key"),
                        flag("op", "kick"),
                        flag("dir", ws),
                        flag("name", w[3].clone()),
                        flag("member", w[4].clone()),
                        flag("proposal-id", w[2].clone()),
                    ],
                    writes: vec![],
                });
            }
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"revoke",
                "name":w[3],"recipient":w[4]});
            proposal(session, &w[2], &request)
        }
        "rotate" => {
            arity(w, 3, 3, u)?;
            workspace_name(&w[2], "proposal ID")?;
            workspace_name(&w[3], "room name")?;
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", "room-key"),
                    flag("op", "rotate"),
                    flag("dir", ws),
                    flag("name", w[3].clone()),
                    flag("proposal-id", w[2].clone()),
                ],
                writes: vec![],
            }
        }
        "register" => {
            // room register ID NAME: publish my current encryption key as my record
            arity(w, 3, 3, u)?;
            workspace_name(&w[2], "proposal ID")?;
            workspace_name(&w[3], "room name")?;
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", "room-key"),
                    flag("op", "register"),
                    flag("dir", ws),
                    flag("name", w[3].clone()),
                    flag("proposal-id", w[2].clone()),
                ],
                writes: vec![],
            }
        }
        "rewrap" => {
            // room rewrap ID NAME SUBJECT: wrap SUBJECT's epochs again to its record
            arity(w, 4, 4, u)?;
            workspace_name(&w[2], "proposal ID")?;
            workspace_name(&w[3], "room name")?;
            decimal(&w[4], "member")?;
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", "room-key"),
                    flag("op", "rewrap"),
                    flag("dir", ws),
                    flag("name", w[3].clone()),
                    flag("member", w[4].clone()),
                    flag("proposal-id", w[2].clone()),
                ],
                writes: vec![],
            }
        }
        "keys" => {
            arity(w, 2, 2, u)?;
            workspace_name(&w[2], "room name")?;
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", "room-key"),
                    flag("op", "list"),
                    flag("dir", ws),
                    flag("name", w[2].clone()),
                ],
                writes: vec![],
            }
        }
        "leave" => {
            arity(w, 3, 3, u)?;
            workspace_name(&w[2], "proposal ID")?;
            workspace_name(&w[3], "room name")?;
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"renounce",
                "name":w[3],"leave":true});
            proposal(session, &w[2], &request)
        }
        "members" | "law" => {
            arity(w, 2, 2, u)?;
            ref_name(&w[2], "room name")?;
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", if action == "members" { "who" } else { "describe" }),
                    flag("dir", ws),
                    flag("name", w[2].clone()),
                ],
                writes: vec![],
            }
        }
        "list" => {
            arity(w, 1, 1, u)?;
            Plan::Rooms
        }
        "status" => {
            arity(w, 2, 2, u)?;
            ref_name(&w[2], "room name")?;
            Plan::Client {
                command: "credit".into(),
                flags: vec![
                    flag("action", "status"),
                    flag("dir", ws),
                    flag("room", w[2].clone()),
                    flag("inbox", session.home.join("inbox")),
                ],
                writes: vec![],
            }
        }
        "renew" => {
            if w.len() < 4 {
                return Err(u.to_owned());
            }
            ref_name(&w[2], "room name")?;
            decimal(&w[3], "member")?;
            let flags = room_flags(&w[4..], &["for", "until"])?;
            let mut out = vec![
                flag("action", "renew"),
                flag("dir", ws),
                flag("room", w[2].clone()),
                flag("subject", w[3].clone()),
                flag("outbox", session.home.join("outbox")),
            ];
            match (room_flag(&flags, "for"), room_flag(&flags, "until")) {
                (Some(n), None) => {
                    decimal(n, "--for")?;
                    out.push(flag("for", n));
                }
                (None, Some(h)) => {
                    decimal(h, "--until")?;
                    out.push(flag("not-after", h));
                }
                (None, None) => {}
                _ => return Err("room renew takes --for N or --until H".into()),
            }
            Plan::Client { command: "credit".into(), flags: out, writes: vec![] }
        }
        "concierge" => {
            if w.len() < 4 {
                return Err(u.to_owned());
            }
            workspace_name(&w[2], "room name")?;
            decimal(&w[3], "concierge subject")?;
            let flags = room_flags(&w[4..], &["period", "fund"])?;
            let mut out = vec![
                flag("action", "install"),
                flag("dir", ws),
                flag("room", w[2].clone()),
                flag("concierge", w[3].clone()),
                flag("outbox", session.home.join("outbox")),
                flag("program", session.home.join("concierge").join(format!("{}.json", w[2]))),
            ];
            for key in ["period", "fund"] {
                if let Some(value) = room_flag(&flags, key) {
                    decimal(value, key)?;
                    out.push(flag(key, value));
                }
            }
            Plan::Client { command: "credit".into(), flags: out, writes: vec![] }
        }
        _ => return Err(u.to_owned()),
    })
}

/// The board law (PLACE §2.2): task `n` has its state in field `2n+2`
/// (0 todo, 1 doing, 2 done) and its owner in field `2n+3`. Field 1 is not a
/// task's: every declared object is born holding field 1 = 0
/// (`NativeHostGenesis.declaredCell`). A state never goes backwards (a present
/// delta is never negative; a field created in this turn has no delta) and an
/// owner, once taken, is never replaced. A declared page holds four entries
/// today, so only task 0 fits; the law also names task 1 for when it does.
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

fn board_state(value: &str) -> std::result::Result<&'static str, String> {
    Ok(match value {
        "0" | "todo" => "0",
        "1" | "doing" => "1",
        "2" | "done" => "2",
        _ => return Err("a board state is todo, doing or done (0, 1, 2)".into()),
    })
}

/// Text for a document line: a literal word, or `@FILE` from HOME/requests.
fn text_argument(session: &Session, word: &str) -> std::result::Result<String, String> {
    let text = if let Some(file) = word.strip_prefix('@') {
        session_file(file, "text file")?;
        let path = session.home.join("requests").join(file);
        let mut bytes = Vec::new();
        fs::File::open(&path)
            .and_then(|f| f.take(4097).read_to_end(&mut bytes))
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

/// An encryption public key: 64 hex digits, or `@FILE` in HOME/requests holding them.
fn enc_argument(session: &Session, word: &str) -> std::result::Result<String, String> {
    let text = match word.strip_prefix('@') {
        Some(file) => {
            session_file(file, "encryption key file")?;
            let path = session.home.join("requests").join(file);
            fs::read_to_string(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?
        }
        None => word.to_owned(),
    };
    let text = text.trim().to_owned();
    if text.len() != 64 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("an encryption public key is 64 hex digits (the invitee's `whoami` prints it)".into());
    }
    Ok(text.to_ascii_lowercase())
}

/// The birth options of a `create` or `doc new` line, removed from it:
/// `--in ROOM` (born in the room a reference names; the Host's birth gate
/// decides) and, on `create`, `--owner SUBJECT` (born owned by another
/// subject: a room founder birthing a member's stream, PLACE §2.3 (a)). Each
/// is a pair of words after the name, in any order.
#[derive(Debug, Default, PartialEq)]
struct Birth {
    room: Option<String>,
    owner: Option<String>,
}

fn take_birth(words: &mut Vec<String>) -> std::result::Result<Birth, String> {
    let verb = (words.first().map(String::as_str), words.get(1).map(String::as_str));
    let create = matches!(verb.0, Some("create"));
    let first = match verb {
        (Some("create"), _) => 2,
        (Some("doc"), Some("new")) => 3,
        _ => return Ok(Birth::default()),
    };
    let mut birth = Birth::default();
    let mut i = first;
    while i < words.len() {
        let slot = match words[i].as_str() {
            "--in" => &mut birth.room,
            "--owner" if create => &mut birth.owner,
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
fn hex_bytes(word: &str, length: usize) -> Option<Vec<u8>> {
    if word.len() != 2 * length || !word.bytes().all(|b| b.is_ascii_hexdigit()) {
        return None;
    }
    (0..length)
        .map(|i| u8::from_str_radix(&word[2 * i..2 * i + 2], 16).ok())
        .collect()
}

fn decimal(value: &str, label: &str) -> std::result::Result<(), String> {
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{label} must be a decimal number"));
    }
    Ok(())
}

/// A JSON argument: inline, or `@FILE` read from HOME/requests/FILE.
fn json_argument(session: &Session, word: &str, label: &str) -> std::result::Result<Value, String> {
    let text = if let Some(file) = word.strip_prefix('@') {
        session_file(file, label)?;
        let path = session.home.join("requests").join(file);
        let mut bytes = Vec::new();
        fs::File::open(&path)
            .and_then(|f| f.take(1 << 20).read_to_end(&mut bytes))
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
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
            let mut bytes = Vec::new();
            fs::File::open(&path)
                .and_then(|f| f.take(1 << 20).read_to_end(&mut bytes))
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
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
    VERBS.iter().find(|v| v.name == name).map(|v| v.usage).unwrap_or("")
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
        "whoami" => {
            arity(&w, 0, 0, u)?;
            Plan::Whoami
        }
        "help" | "?" => {
            arity(&w, 0, 1, usage_of("help"))?;
            match w.get(1).map(String::as_str) {
                Some("guide") => Plan::Guide,
                _ => Plan::Help(w.get(1).cloned()),
            }
        }
        "inbox" => {
            arity(&w, 0, 0, u)?;
            Plan::Inbox
        }
        "revoke" => {
            arity(&w, 3, 3, u)?;
            workspace_name(&w[1], "proposal ID")?;
            ref_name(&w[2], "reference name")?;
            decimal(&w[3], "recipient")?;
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"revoke",
                "name":w[2],"recipient":w[3]});
            proposal(session, &w[1], &request)
        }
        "renounce" => {
            arity(&w, 2, 3, u)?;
            workspace_name(&w[1], "proposal ID")?;
            let request = if w[2].bytes().all(|b| b.is_ascii_digit()) {
                decimal(&w[2], "capability")?;
                let kind = w.get(3).map(String::as_str).unwrap_or("object");
                if !matches!(kind, "object" | "account" | "program") {
                    return Err(u.to_owned());
                }
                json!({"type":"minidregg-workspace-proposal-v1","action":"renounce",
                    "capability":w[2],"kind":kind})
            } else {
                if w.len() != 3 {
                    return Err(u.to_owned());
                }
                workspace_name(&w[2], "reference name")?;
                json!({"type":"minidregg-workspace-proposal-v1","action":"renounce","name":w[2]})
            };
            proposal(session, &w[1], &request)
        }
        "room" => room_plan(session, &w, u)?,
        "forget" => {
            arity(&w, 1, 2, u)?;
            workspace_name(&w[1], "room name")?;
            let mut flags = vec![
                flag("action", "room-key"),
                flag("op", "forget"),
                flag("dir", ws()),
                flag("name", w[1].clone()),
            ];
            if let Some(epoch) = w.get(2) {
                decimal(epoch, "epoch")?;
                flags.push(flag("epoch", epoch.clone()));
            }
            client("workspace", flags)
        }
        "doc" => {
            let Some(action) = w.get(1) else {
                return Err(u.to_owned());
            };
            match action.as_str() {
                "new" => {
                    arity(&w, 2, 3, u)?;
                    ref_name(&w[2], "document name")?;
                    // `draft`, `note`, or the document's own law in the law
                    // grammar (one word: quote it), JSON, or `@FILE`.
                    let law = match w.get(3).map(String::as_str).unwrap_or("draft") {
                        stock @ ("draft" | "note") => document_law(stock).expect("stock document law"),
                        _ => law_argument(session, &w[3..4])?,
                    };
                    let path = session.home.join("requests").join(format!("create-{}.json", ref_file(&w[2])));
                    let mut flags = vec![
                        flag("action", "create"),
                        flag("dir", ws()),
                        flag("name", w[2].clone()),
                        flag("storage", "content"),
                        flag("predicate", path.clone()),
                    ];
                    if let Some(room) = &room {
                        flags.push(flag("in", room.clone()));
                    }
                    Plan::Client {
                        command: "workspace".into(),
                        flags,
                        writes: vec![request_file(path, &law)],
                    }
                }
                "show" | "backlinks" => {
                    arity(&w, 2, 2, u)?;
                    ref_name(&w[2], "document name")?;
                    client(
                        "workspace",
                        vec![
                            flag("action", format!("doc-{action}")),
                            flag("dir", ws()),
                            flag("name", w[2].clone()),
                        ],
                    )
                }
                "append" => {
                    arity(&w, 4, 4, u)?;
                    workspace_name(&w[2], "proposal ID")?;
                    ref_name(&w[3], "document name")?;
                    let text = text_argument(session, &w[4])?;
                    document_proposal(session, &w[2], &w[3], json!({"type":"append","text":text}))
                }
                "edit" => {
                    arity(&w, 5, 5, u)?;
                    workspace_name(&w[2], "proposal ID")?;
                    ref_name(&w[3], "document name")?;
                    decimal(&w[4], "line")?;
                    let text = text_argument(session, &w[5])?;
                    document_proposal(
                        session,
                        &w[2],
                        &w[3],
                        json!({"type":"edit","line":w[4],"text":text}),
                    )
                }
                "link" => {
                    arity(&w, 4, 5, u)?;
                    workspace_name(&w[2], "proposal ID")?;
                    ref_name(&w[3], "document name")?;
                    ref_name(&w[4], "document name")?;
                    let relation = w.get(5).cloned().unwrap_or_else(|| "0".into());
                    decimal(&relation, "relation")?;
                    document_proposal(
                        session,
                        &w[2],
                        &w[3],
                        json!({"type":"link","to":w[4],"relation":relation}),
                    )
                }
                "annotate" => Plan::NotHere(
                    "doc annotate: this store's content cell has no annotation action (Kernel/ContentResource.lean Action is createDocument, createAtom, editAtom, link, createRun; Theory/HyperdocumentOperations.lean AnnotatePayload and the annotations namespace are not in the page entry grammar); needs K-CONTENT-ACTIONS, and annotate-but-not-edit needs K-FIELDS".into(),
                ),
                "quote" => Plan::NotHere(
                    "doc quote: this store's content cell has no transclusion action (Kernel/ContentResource.lean Action has no transclude; TransclusionRecord with its disclosurePolicy is not in the page entry grammar); needs K-CONTENT-ACTIONS".into(),
                ),
                _ => return Err(u.to_owned()),
            }
        }
        "board" => {
            let Some(action) = w.get(1) else {
                return Err(u.to_owned());
            };
            let task_field = |task: &str, offset: u64| -> std::result::Result<String, String> {
                decimal(task, "task")?;
                task.parse::<u64>()
                    .ok()
                    .and_then(|n| n.checked_mul(2)?.checked_add(2 + offset))
                    .map(|n| n.to_string())
                    .ok_or_else(|| "task number is too large".to_owned())
            };
            match action.as_str() {
                "new" => {
                    arity(&w, 2, 2, u)?;
                    ref_name(&w[2], "board name")?;
                    let path = session.home.join("requests").join(format!("create-{}.json", ref_file(&w[2])));
                    Plan::Client {
                        command: "workspace".into(),
                        flags: vec![
                            flag("action", "create"),
                            flag("dir", ws()),
                            flag("name", w[2].clone()),
                            flag("storage", "declared"),
                            flag("predicate", path.clone()),
                        ],
                        writes: vec![request_file(path, &board_law())],
                    }
                }
                "add" => {
                    arity(&w, 4, 4, u)?;
                    workspace_name(&w[2], "proposal ID")?;
                    ref_name(&w[3], "board name")?;
                    let field = task_field(&w[4], 0)?;
                    scalar_proposal(
                        session,
                        &w[2],
                        &w[3],
                        json!({"type":"create","key":{"type":"object","field":field},"value":"0"}),
                    )
                }
                "move" => {
                    arity(&w, 6, 6, u)?;
                    workspace_name(&w[2], "proposal ID")?;
                    ref_name(&w[3], "board name")?;
                    let field = task_field(&w[4], 0)?;
                    let from = board_state(&w[5])?;
                    let to = board_state(&w[6])?;
                    scalar_proposal(
                        session,
                        &w[2],
                        &w[3],
                        json!({"type":"write","key":{"type":"object","field":field},
                            "value":to,"expected":from}),
                    )
                }
                "take" => {
                    arity(&w, 4, 4, u)?;
                    workspace_name(&w[2], "proposal ID")?;
                    ref_name(&w[3], "board name")?;
                    let field = task_field(&w[4], 1)?;
                    let me = session_subject(session)?;
                    scalar_proposal(
                        session,
                        &w[2],
                        &w[3],
                        json!({"type":"create","key":{"type":"object","field":field},"value":me}),
                    )
                }
                _ => return Err(u.to_owned()),
            }
        }
        "exit" | "quit" => {
            arity(&w, 0, 0, u)?;
            Plan::Exit
        }
        "key" => crate::keys::shell_plan(&session.workspace, &session.home, &w)?,
        "history" => {
            arity(&w, 0, 1, u)?;
            match w.get(1).map(String::as_str) {
                None => Plan::History { all: false },
                Some("all") => Plan::History { all: true },
                Some(_) => return Err(u.to_owned()),
            }
        }
        "keygen" => {
            arity(&w, 1, 1, u)?;
            session_file(&w[1], "key file")?;
            let keys = session.home.join("keys");
            client(
                "keygen",
                vec![
                    flag("secret", keys.join(&w[1])),
                    flag("public", keys.join(format!("{}.pub", w[1]))),
                    flag("hosted", "yes"),
                ],
            )
        }
        "init" => {
            let mut w: Vec<String> = w.to_vec();
            let without = take_switch(&mut w, "--no-prerotation");
            arity(&w, 2, 2, u)?;
            session_file(&w[1], "key file")?;
            decimal(&w[2], "subject")?;
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
                flag("key", session.home.join("keys").join(&w[1])),
                flag("subject", w[2].clone()),
                flag("birth-context", context),
                flag("namespace-root", session.home.join("namespace")),
                flag("dir", ws()),
            ]);
            // init refuses a subject whose committed next key is not
            // HOME/keys/KEYFILE.next.pub (FIX-IDENTITY), unless --no-prerotation.
            if without {
                flags.push(flag("no-prerotation", "true"));
            }
            client("workspace", flags)
        }
        "enroll" => {
            let Some(action) = w.get(1) else {
                return Err(u.to_owned());
            };
            match action.as_str() {
                "plan" => {
                    // enroll plan NAME KEYFILE|PUBLIC-HEX [NEXT-PUB-HEX COSIGN-HEX | --no-prerotation] [FACTORY-REF]
                    // The next public key and its co-signature are the NEWCOMER's
                    // (their `keygen` / `mini join --key` prints them): never a file
                    // this session home happens to hold (FIX-IDENTITY).
                    let mut w: Vec<String> = w.to_vec();
                    let without = take_switch(&mut w, "--no-prerotation");
                    let next = match (w.get(4).and_then(|word| hex_bytes(word, 32)), w.get(5).and_then(|word| hex_bytes(word, 64))) {
                        (Some(next), Some(cosign)) => {
                            w.drain(4..6);
                            Some((next, cosign))
                        }
                        _ => None,
                    };
                    arity(&w, 3, 4, u)?;
                    workspace_name(&w[2], "enrollment name")?;
                    let factory = w.get(4).cloned().unwrap_or_else(|| "factory".into());
                    ref_name(&factory, "factory reference")?;
                    let mut flags = vec![
                        flag("action", "plan"),
                        flag("sponsor-workspace", ws()),
                        flag("factory-ref", factory),
                        flag("name", w[2].clone()),
                    ];
                    let mut writes = vec![];
                    if let Some(public) = hex_bytes(&w[3], 32) {
                        // The newcomer keeps the secret; only the public key
                        // enters this session home.
                        let path = session.home.join("keys").join(format!("{}.pub", w[2]));
                        flags.push(flag("new-public-key", path.clone()));
                        writes.push((path, public));
                    } else {
                        session_file(&w[3], "key file")?;
                        flags.push(flag("new-key", session.home.join("keys").join(&w[3])));
                    }
                    match (next, without) {
                        (Some((next, cosign)), false) => {
                            let next_path = session.home.join("enroll").join(format!("{}.next.pub", w[2]));
                            let cosign_path = session.home.join("enroll").join(format!("{}.next.cosign", w[2]));
                            flags.push(flag("next-public-key", next_path.clone()));
                            flags.push(flag("next-cosign", cosign_path.clone()));
                            writes.push((next_path, next));
                            writes.push((cosign_path, cosign));
                        }
                        (None, true) => flags.push(flag("no-prerotation", "true")),
                        (Some(_), true) => return Err("a next public key and --no-prerotation exclude each other".into()),
                        (None, false) => return Err("enroll plan NAME KEYFILE|PUBLIC-KEY-HEX NEXT-PUBLIC-KEY-HEX COSIGN-HEX: the record commits to the newcomer's next key, and that key co-signs (their `keygen` prints both; `mini enroll --action cosign --key KEY` prints them again), or add --no-prerotation".into()),
                    }
                    flags.push(flag("dir", session.home.join("enroll").join(&w[2])));
                    Plan::Client { command: "enroll".into(), flags, writes }
                }
                "seal" if w.len() == 4 => {
                    workspace_name(&w[2], "enrollment name")?;
                    let signature = hex_bytes(&w[3], 64)
                        .ok_or("the possession signature is 128 hex digits (from the newcomer's mini join)")?;
                    let path = session.home.join("requests").join(format!("{}.possession", w[2]));
                    Plan::Client {
                        command: "enroll".into(),
                        flags: vec![
                            flag("action", "seal"),
                            flag("dir", session.home.join("enroll").join(&w[2])),
                            flag("possession-signature", path.clone()),
                        ],
                        writes: vec![(path, signature)],
                    }
                }
                "welcome" => {
                    arity(&w, 2, 2, u)?;
                    workspace_name(&w[2], "enrollment name")?;
                    let mut flags = vec![
                        flag("action", "welcome"),
                        flag("dir", session.home.join("enroll").join(&w[2])),
                    ];
                    let context = ws().join("provisions").join(&w[2]).join("birth-context.json");
                    if context.is_file() {
                        flags.push(flag("birth-context", context));
                    }
                    client("enroll", flags)
                }
                "seal" | "submit" | "lookup" | "offer" => {
                    arity(&w, 2, 2, u)?;
                    workspace_name(&w[2], "enrollment name")?;
                    client(
                        "enroll",
                        vec![
                            flag("action", action.clone()),
                            flag("dir", session.home.join("enroll").join(&w[2])),
                        ],
                    )
                }
                _ => return Err(u.to_owned()),
            }
        }
        "pay" if w.get(1).is_some_and(|word| !matches!(word.as_str(), "address" | "status" | "audit")) => {
            // `pay ROOM week|N [--account REF]` (P-CREDIT).
            if !(w.len() == 3 || w.len() == 5) {
                return Err(u.to_owned());
            }
            ref_name(&w[1], "room name")?;
            let mut flags = vec![
                flag("action", "pay"),
                flag("dir", ws()),
                flag("room", w[1].clone()),
                flag("outbox", session.home.join("outbox")),
            ];
            match w[2].as_str() {
                "week" => {}
                amount => {
                    decimal(amount, "amount")?;
                    flags.push(flag("amount", amount));
                }
            }
            if w.len() == 5 {
                if w[3] != "--account" {
                    return Err(u.to_owned());
                }
                workspace_name(&w[4], "account reference")?;
                flags.push(flag("account", w[4].clone()));
            }
            client("credit", flags)
        }
        "credit" => {
            arity(&w, 0, 1, u)?;
            let mut flags = vec![flag("action", "balance"), flag("dir", ws())];
            if let Some(account) = w.get(1) {
                workspace_name(account, "account reference")?;
                flags.push(flag("account", account.clone()));
            }
            client("credit", flags)
        }
        "tariff" => {
            let mut flags = vec![flag("action", "tariff"), flag("dir", ws())];
            match w.len() {
                2 => {}
                5 if w[2] == "set" => {
                    decimal(&w[4], "tariff value")?;
                    flags.push(flag("set", w[3].clone()));
                    flags.push(flag("value", w[4].clone()));
                }
                _ => return Err(u.to_owned()),
            }
            ref_name(&w[1], "room name")?;
            flags.push(flag("room", w[1].clone()));
            client("credit", flags)
        }
        "topup" => {
            if w.len() < 3 {
                return Err(u.to_owned());
            }
            ref_name(&w[1], "room name")?;
            decimal(&w[2], "amount")?;
            let mut flags = vec![
                flag("action", "topup"),
                flag("dir", ws()),
                flag("room", w[1].clone()),
                flag("amount", w[2].clone()),
            ];
            let mut i = 3;
            while i < w.len() {
                match w[i].as_str() {
                    "--account" if i + 1 < w.len() => {
                        workspace_name(&w[i + 1], "account reference")?;
                        flags.push(flag("account", w[i + 1].clone()));
                        i += 1;
                    }
                    whose @ ("hermes" | "concierge") => flags.push(flag("to", whose)),
                    _ => return Err(u.to_owned()),
                }
                i += 1;
            }
            client("credit", flags)
        }
        "pay" => {
            arity(&w, 1, 2, u)?;
            let mut flags = vec![flag("action", w[1].clone()), flag("dir", ws())];
            match (w[1].as_str(), w.get(2)) {
                ("address" | "status", Some(account)) => {
                    workspace_name(account, "reference name")?;
                    flags.push(flag("account", account.clone()));
                }
                ("address" | "status" | "audit", None) => {}
                _ => return Err(u.to_owned()),
            }
            client("pay", flags)
        }
        "provision" => {
            arity(&w, 4, 5, u)?;
            workspace_name(&w[1], "provision name")?;
            decimal(&w[2], "holder subject")?;
            decimal(&w[3], "funding")?;
            let predicate = json_argument(session, &w[4], "account predicate")?;
            let factory = w.get(5).cloned().unwrap_or_else(|| "factory".into());
            workspace_name(&factory, "factory reference")?;
            let path = session.home.join("requests").join(format!("provision-{}.json", w[1]));
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", "provision"),
                    flag("dir", ws()),
                    flag("name", w[1].clone()),
                    flag("holder", w[2].clone()),
                    flag("funding", w[3].clone()),
                    flag("account-predicate", path.clone()),
                    flag("factory-ref", factory),
                ],
                writes: vec![request_file(path, &predicate)],
            }
        }
        "key-status" => {
            arity(&w, 0, 0, u)?;
            client("key-status", vec![flag("workspace", ws())])
        }
        "rotate-key" => {
            arity(&w, 1, 1, u)?;
            session_file(&w[1], "next key file")?;
            client(
                "rotate-key",
                vec![
                    flag("workspace", ws()),
                    flag("next-key", session.home.join("keys").join(&w[1])),
                ],
            )
        }
        "refs" => {
            arity(&w, 0, 0, u)?;
            client("workspace", vec![flag("action", "list"), flag("dir", ws())])
        }
        "inspect" | "why" => {
            let json_out = w.iter().any(|word| word == "--json");
            let rest: Vec<&String> = w[1..].iter().filter(|word| *word != "--json").collect();
            let (view, name) = if w[0] == "why" {
                match rest.as_slice() {
                    [] => ("why", None),
                    [attempt] => ("why", Some((*attempt).clone())),
                    _ => return Err(u.to_owned()),
                }
            } else {
                match rest.as_slice() {
                    [view] if view.as_str() == "caps" => ("caps", None),
                    [view, name] if matches!(view.as_str(), "caps" | "law" | "receipt" | "turn") => {
                        (view.as_str(), Some((*name).clone()))
                    }
                    _ => return Err(u.to_owned()),
                }
            };
            let mut flags = vec![flag("action", "inspect"), flag("dir", ws()), flag("view", view)];
            if let Some(name) = name {
                // caps/law name a reference (incl. lab/index under a room);
                // receipt/turn/why name a proposal or attempt.
                if matches!(view, "caps" | "law") {
                    ref_name(&name, "reference name")?;
                } else {
                    workspace_name(&name, "name")?;
                }
                flags.push(flag("name", name));
            }
            if view == "why" {
                flags.push(flag("refusals", session.home.join("refusals")));
            }
            if json_out {
                flags.push(flag("json", "true"));
            }
            client("workspace", flags)
        }
        "can" => {
            arity(&w, 0, 2, u)?;
            let mut flags = vec![flag("action", "can"), flag("dir", ws())];
            for word in &w[1..] {
                if word == "--all" {
                    flags.push(flag("all", "true"));
                } else if word == "--any" {
                    flags.push(flag("any", "true"));
                } else if flags.iter().any(|(name, _)| name == "name") {
                    return Err(u.to_owned());
                } else {
                    // A reference name, incl. one under a room (lab/notes).
                    ref_name(word, "reference name")?;
                    flags.push(flag("name", word.clone()));
                }
            }
            if flags.iter().any(|(name, _)| name == "any")
                && !flags.iter().any(|(name, _)| name == "name")
            {
                return Err(u.to_owned());
            }
            client("workspace", flags)
        }
        "read" | "describe" => {
            arity(&w, 1, 1, u)?;
            ref_name(&w[1], "reference name")?;
            client(
                "workspace",
                vec![flag("action", verb.clone()), flag("dir", ws()), flag("name", w[1].clone())],
            )
        }
        "import" => {
            arity(&w, 2, 6, u)?;
            ref_name(&w[1], "reference name")?;
            let second = &w[2];
            if second.starts_with('{') || second.starts_with('@') {
                arity(&w, 2, 2, u)?;
                let value = json_argument(session, second, "reference")?;
                let path = session.home.join("inbox").join(format!("{}.json", ref_file(&w[1])));
                Plan::Client {
                    command: "workspace".into(),
                    flags: vec![
                        flag("action", "import"),
                        flag("dir", ws()),
                        flag("name", w[1].clone()),
                        flag("from-ref", path.clone()),
                    ],
                    writes: vec![request_file(path, &value)],
                }
            } else {
                arity(&w, 4, 6, u)?;
                decimal(&w[3], "target")?;
                decimal(&w[4], "observe capability")?;
                let mut flags = vec![
                    flag("action", "import"),
                    flag("dir", ws()),
                    flag("name", w[1].clone()),
                    flag("kind", w[2].clone()),
                    flag("target", w[3].clone()),
                    flag("observe-capability", w[4].clone()),
                ];
                if let Some(operation) = w.get(5).filter(|v| v.as_str() != "-") {
                    decimal(operation, "operation capability")?;
                    flags.push(flag("operation-capability", operation.clone()));
                }
                if let Some(control) = w.get(6) {
                    decimal(control, "control capability")?;
                    flags.push(flag("control-capability", control.clone()));
                }
                client("workspace", flags)
            }
        }
        "create" => {
            arity(&w, 3, 3, u)?;
            ref_name(&w[1], "resource name")?;
            let predicate = law_argument(session, &w[3..4])?;
            let path = session.home.join("requests").join(format!("create-{}.json", ref_file(&w[1])));
            let mut flags = vec![
                flag("action", "create"),
                flag("dir", ws()),
                flag("name", w[1].clone()),
                flag("storage", w[2].clone()),
                flag("predicate", path.clone()),
            ];
            if let Some(room) = &room {
                flags.push(flag("in", room.clone()));
            }
            if let Some(owner) = &birth.owner {
                flags.push(flag("owner", owner.clone()));
            }
            Plan::Client {
                command: "workspace".into(),
                flags,
                writes: vec![request_file(path, &predicate)],
            }
        }
        "propose" => {
            arity(&w, 2, 2, u)?;
            workspace_name(&w[1], "proposal ID")?;
            let request = json_argument(session, &w[2], "request")?;
            proposal(session, &w[1], &request)
        }
        "invoke" => {
            workspace_name(w.get(1).map(String::as_str).unwrap_or(""), "proposal ID")?;
            let action = w.get(3).map(String::as_str);
            let scalar = match action {
                Some("create") => {
                    arity(&w, 5, 5, u)?;
                    json!({"type":"create","key":{"type":"object","field":w[4]},"value":w[5]})
                }
                Some("write") => {
                    arity(&w, 6, 6, u)?;
                    json!({"type":"write","key":{"type":"object","field":w[4]},
                        "value":w[5],"expected":w[6]})
                }
                _ => return Err(u.to_owned()),
            };
            ref_name(&w[2], "reference name")?;
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                "targets":[{"name":w[2],"payload":{"type":"scalar","actions":[scalar]}}]});
            proposal(session, &w[1], &request)
        }
        "delegate" => {
            arity(&w, 5, 5, u)?;
            workspace_name(&w[1], "proposal ID")?;
            ref_name(&w[2], "reference name")?;
            let verbs: Vec<&str> = w[4].split(',').collect();
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                "name":w[2],"recipient":w[3],"verbs":verbs,"maxCost":w[5]});
            proposal(session, &w[1], &request)
        }
        "law" if w.get(1).map(String::as_str) == Some("check") => {
            let law = match &w[2..] {
                [dash] if dash == "-" => law_from_stdin()?,
                [] => return Err(u.to_owned()),
                words => law_argument(session, words)?,
            };
            let bytes = serde_json::to_vec(&law).expect("JSON values serialise");
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hasher::write(&mut hasher, &bytes);
            let name = format!("law-check-{:016x}.json", std::hash::Hasher::finish(&hasher));
            let path = session.home.join("requests").join(name);
            Plan::Client {
                command: "workspace".into(),
                flags: vec![flag("action", "law-check"), flag("dir", ws()), flag("predicate", path.clone())],
                writes: vec![request_file(path, &law)],
            }
        }
        "law" => {
            let allow = w.last().is_some_and(|word| word == "--allow-unsatisfiable");
            let w = if allow { w[..w.len() - 1].to_vec() } else { w };
            if w.len() < 4 {
                arity(&w, 3, 3, u)?;
            }
            workspace_name(&w[1], "proposal ID")?;
            ref_name(&w[2], "reference name")?;
            let predicate = law_argument(session, &w[3..])?;
            let request = json!({"type":"minidregg-workspace-proposal-v1",
                "action":"install-policy","name":w[2],"predicate":predicate});
            let mut plan = proposal(session, &w[1], &request);
            if let (true, Plan::Client { flags, .. }) = (allow, &mut plan) {
                flags.push(flag("allow-unsatisfiable", "true"));
            }
            plan
        }
        "submit" => {
            arity(&w, 1, 1, u)?;
            workspace_name(&w[1], "proposal ID")?;
            client(
                "workspace",
                vec![
                    flag("action", "submit"),
                    flag("dir", ws()),
                    flag("intent", ws().join("proposals").join(&w[1]).join("intent.json")),
                    flag("attempt", ws().join("attempts").join(&w[1])),
                ],
            )
        }
        "lookup" => {
            arity(&w, 1, 1, u)?;
            workspace_name(&w[1], "proposal ID")?;
            client(
                "workspace",
                vec![
                    flag("action", "recover"),
                    flag("dir", ws()),
                    flag("attempt", ws().join("attempts").join(&w[1])),
                ],
            )
        }
        "retry" => {
            arity(&w, 1, 1, u)?;
            workspace_name(&w[1], "proposal ID")?;
            client(
                "retry",
                vec![
                    flag("attempt", ws().join("attempts").join(&w[1])),
                    flag("mode", "submit"),
                ],
            )
        }
        "publish" => {
            arity(&w, 1, 1, u)?;
            workspace_name(&w[1], "proposal ID")?;
            client(
                "workspace",
                vec![
                    flag("action", "publish-delegation"),
                    flag("dir", ws()),
                    flag("proposal-id", w[1].clone()),
                    flag("attempt", ws().join("attempts").join(&w[1])),
                ],
            )
        }
        "export" => {
            arity(&w, 1, 1, u)?;
            workspace_name(&w[1], "proposal ID")?;
            Plan::Export(ws().join("proposals").join(&w[1]).join("recipient-reference.json"))
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
}

fn hex_text(value: Option<&Value>) -> String {
    let Some(hex) = value.and_then(Value::as_str) else {
        return "(absent)".into();
    };
    let bytes: Option<Vec<u8>> = (0..hex.len())
        .step_by(2)
        .map(|i| hex.get(i..i + 2).and_then(|b| u8::from_str_radix(b, 16).ok()))
        .collect();
    match bytes.and_then(|b| String::from_utf8(b).ok()) {
        Some(text) if !text.chars().any(char::is_control) => format!("{text:?}"),
        _ => format!("hex {hex}"),
    }
}

fn outcome_line(outcome: &Value) -> (i32, String) {
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
                HostDecision::RefusedFrame { command, byte, encoded, .. } => {
                    match decoded {
                        Some(Ok(outcome)) => {
                            let (_, line) = outcome_line(outcome);
                            text.push_str(&format!("{line} (Host refused {command}, reply byte {byte})\n"));
                            text.push_str(&format!("  outcome (decoded by the Host): {outcome}\n"));
                        }
                        Some(Err(why)) => text.push_str(&format!(
                            "refused: Host refused {command}, reply byte {byte}; the Host could not decode the frame: {why}\n"
                        )),
                        None => text.push_str(&format!(
                            "refused: Host refused {command}, reply byte {byte}\n"
                        )),
                    }
                    text.push_str(&format!("  encoded: {}\n", super::hex(encoded)));
                    EXIT_REFUSED
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

fn private_dir(path: &Path) -> Result<()> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => Ok(()),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => Ok(()),
        Err(e) => Err(format!("cannot create {}: {e}", path.display())),
    }
}

/// Create a request file once. An identical file already present is the same
/// request (a retried line); different content under the same name is refused.
fn write_once(path: &Path, bytes: &[u8]) -> Result<()> {
    if let Some(parent) = path.parent() {
        private_dir(parent)?;
    }
    match OpenOptions::new().write(true).create_new(true).mode(0o600).open(path) {
        Ok(mut file) => file
            .write_all(bytes)
            .and_then(|()| file.sync_all())
            .map_err(|e| format!("cannot write {}: {e}", path.display())),
        Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
            let existing = fs::read(path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            if existing == bytes {
                Ok(())
            } else {
                Err(format!(
                    "{} already holds a different request; choose a new ID",
                    path.display()
                ))
            }
        }
        Err(e) => Err(format!("cannot create {}: {e}", path.display())),
    }
}

fn nonce() -> String {
    let mut bytes = [0u8; 8];
    let _ = fs::File::open("/dev/urandom").and_then(|mut f| f.read_exact(&mut bytes));
    super::hex(&bytes)
}

/// Retain a refused frame under HOME/refusals and ask the Host to decode it
/// with its own outcome codec (`inspect outcome`).
fn decode_refusal(session: &Session, command: &str, encoded: &[u8]) -> (Option<PathBuf>, std::result::Result<Value, String>) {
    let dir = session.home.join("refusals");
    if let Err(e) = private_dir(&dir) {
        return (None, Err(e));
    }
    let stem = format!(
        "{}-{}-{}",
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0),
        command.replace(|c: char| !c.is_ascii_alphanumeric(), "-"),
        nonce()
    );
    let bin = dir.join(format!("{stem}.bin"));
    let json = dir.join(format!("{stem}.json"));
    if let Err(e) = write_once(&bin, encoded) {
        return (None, Err(e));
    }
    (Some(bin.clone()), super::inspect(&session.host, &session.config, "outcome", &bin, &json))
}

fn execute(session: &Session, plan: Plan) -> Ending {
    let Plan::Client { command, flags, writes } = plan else {
        return Ending::Done;
    };
    for (path, bytes) in &writes {
        if let Err(e) = write_once(path, bytes) {
            return Ending::Client(e);
        }
    }
    for folder in ["keys", "enroll"] {
        if let Err(e) = private_dir(&session.home.join(folder)) {
            return Ending::Client(e);
        }
    }
    let args = Args {
        command: OsString::from(&command),
        values: flags
            .into_iter()
            .map(|(name, value)| (OsString::from(format!("--{name}")), value))
            .collect(),
    };
    let _ = super::take_host_decision();
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| super::run(args)))
        .unwrap_or_else(|_| Err("the client panicked; see the message above".into()));
    let _ = io::stdout().flush();
    let decision = super::take_host_decision();
    match (result, decision) {
        (Ok(()), _) => Ending::Done,
        (Err(client), None) => Ending::Client(client),
        (Err(client), Some(decision)) => {
            let (evidence, decoded) = match &decision {
                HostDecision::RefusedFrame { command, encoded, .. } => {
                    let (path, decoded) = decode_refusal(session, command, encoded);
                    (path, Some(decoded))
                }
                HostDecision::Outcome(_) => (None, None),
            };
            Ending::Host { client, decision, decoded, evidence }
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
            .and_then(|key| crate::workspace::roomkey::enc_public_hex(Path::new(key)).ok()),
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
        Some(name) => match VERBS.iter().chain(crate::chat::VERBS).chain(crate::hermes::VERBS).chain(crate::story::VERBS).find(|v| v.name == name) {
            Some(v) => format!("{}\n  = {}\n", v.usage, v.operation),
            None => format!("no verb {name}\n"),
        },
        None => {
            let mut text = format!("{HOSTED_CUSTODY_BANNER}\n");
            text.push_str("Every verb is one client operation; the Host decides. Words: 'literal', \"escaped\", {json} or [json], @FILE (HOME/requests/FILE).\n");
            for v in VERBS.iter().chain(crate::chat::VERBS).chain(crate::hermes::VERBS).chain(crate::story::VERBS) {
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
        "{HOSTED_CUSTODY_BANNER}\nmini shell: workspace {}. help lists verbs; every decision is the Host's.\n",
        session.workspace.display()
    )
}

/// Run one line; returns (exit code, keep going).
pub(crate) fn line(session: &Session, text: &str) -> (i32, bool) {
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
        Ok(plan) => execute(session, plan),
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
        (_, 0) => VERBS.iter().chain(crate::chat::VERBS).chain(crate::hermes::VERBS).chain(crate::story::VERBS).map(|v| v.name.to_owned()).chain(["unpin".to_owned()]).collect(),
        ("read" | "describe", 1) => refs(),
        ("submit" | "publish" | "export", 1) => proposals(),
        ("lookup" | "retry", 1) => attempts(),
        ("history", 1) => vec!["all".into()],
        ("pay", 1) => ["address", "status", "audit"].map(String::from).to_vec(),
        ("pay", 2) if w[1] != "audit" => refs(),
        ("init", 1) => keys(),
        ("enroll", 1) => ["plan", "offer", "seal", "submit", "lookup", "welcome"].map(String::from).to_vec(),
        ("enroll", 2) if w[1] != "plan" => enrolled(),
        ("enroll", 3) if w[1] == "plan" => keys(),
        ("invoke" | "delegate" | "law", 2) => refs(),
        ("invoke", 3) => vec!["create".into(), "write".into()],
        ("revoke" | "renounce", 2) => refs(),
        ("doc", 1) => ["new", "show", "append", "edit", "link", "backlinks", "annotate", "quote"]
            .map(String::from)
            .to_vec(),
        ("doc", 2) if matches!(w[1].as_str(), "show" | "backlinks") => refs(),
        ("doc", 3) if matches!(w[1].as_str(), "append" | "edit" | "link") => refs(),
        ("doc", 4) if w[1] == "link" => refs(),
        ("board", 1) => ["new", "add", "move", "take"].map(String::from).to_vec(),
        ("board", 3) if w[1] != "new" => refs(),
        ("help", 1) => {
            let mut all: Vec<String> = VERBS.iter().map(|v| v.name.to_owned()).collect();
            all.push("guide".into());
            all
        }
        ("delegate", 4) => vec!["observe".into(), "observe,mutate".into()],
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
    private_dir(&home)?;
    let session = Session { workspace, home, host, config };
    let code = if let Some(one) = one {
        let text = one.into_string().map_err(|_| "--line must be UTF-8")?;
        line(&session, &text).0
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
    use super::*;

    fn session() -> Session {
        Session {
            workspace: PathBuf::from("/w"),
            home: PathBuf::from("/h"),
            host: PathBuf::from("/bin/host"),
            config: PathBuf::from("/c.json"),
        }
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

    fn pairs(items: &[(&str, &str)]) -> Vec<(String, String)> {
        items.iter().map(|(k, v)| (k.to_string(), v.to_string())).collect()
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
        assert_eq!(plan(&s, "submit").unwrap_err(), "submit ID");
        assert_eq!(render(&Ending::Usage(plan(&s, "submit").unwrap_err())).1, "usage: submit ID\n");
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
            decision: HostDecision::RefusedFrame { command: "query".into(), byte: 255, encoded: vec![0x44, 0x52], decoded: None },
            decoded: Some(Ok(decoded)),
            evidence: Some(PathBuf::from("/h/refusals/r.bin")),
        };
        let (code, text) = render(&ending);
        assert_eq!(code, EXIT_REFUSED);
        assert!(text.starts_with(
            "refused: no-grant: this key holds no grant covering this target and operation (phase observation) (Host refused query, reply byte 255)\n"
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
            decision: HostDecision::RefusedFrame { command: "prepare".into(), byte: 255, encoded: vec![0x44], decoded: None },
            decoded: Some(Ok(decoded)),
            evidence: None,
        };
        let (code, text) = render(&ending);
        assert_eq!(code, EXIT_REFUSED);
        assert!(
            text.starts_with("refused: law-denied: field 2 monotone (before 2, after 1) (Host refused prepare, reply byte 255)\n"),
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
    fn undecodable_refusal_is_still_a_refusal_with_its_bytes() {
        let ending = Ending::Host {
            client: "enrollment Host refused op87; exact frame retained".into(),
            decision: HostDecision::RefusedFrame { command: "enrollment op87".into(), byte: 254, encoded: vec![1], decoded: None },
            decoded: Some(Err("bad frame".into())),
            evidence: None,
        };
        let (code, text) = render(&ending);
        assert_eq!(code, EXIT_REFUSED);
        assert!(text.starts_with("refused: Host refused enrollment op87, reply byte 254; the Host could not decode the frame: bad frame\n"));
        assert!(text.contains("  encoded: 01\n"));
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
        let root = std::env::temp_dir().join(format!("mini-shell-complete-{}-{}", std::process::id(), nonce()));
        let ws = root.join("w");
        fs::create_dir_all(ws.join("refs")).unwrap();
        fs::create_dir_all(ws.join("proposals").join("grant-newcomer")).unwrap();
        fs::create_dir_all(ws.join("attempts").join("grant-newcomer")).unwrap();
        fs::create_dir_all(ws.join("attempts").join("a-123")).unwrap();
        fs::write(ws.join("refs").join("shared.json"), b"{}").unwrap();
        fs::write(ws.join("refs").join("factory.json"), b"{}").unwrap();
        let s = Session { workspace: ws, home: root.join("h"), host: "/x".into(), config: "/y".into() };
        assert_eq!(complete(&s, "su"), ["submit", "summon"]);
        assert_eq!(complete(&s, "re"), ["refs", "read", "retry", "revoke", "renounce", "react"]);
        assert_eq!(complete(&s, "doc show "), ["factory", "shared"]);
        assert_eq!(complete(&s, "doc link x shared f"), ["factory"]);
        assert_eq!(complete(&s, "board m"), ["move"]);
        assert_eq!(complete(&s, "help g"), ["guide"]);
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
        let root = std::env::temp_dir().join(format!("mini-shell-write-{}-{}", std::process::id(), nonce()));
        let path = root.join("requests").join("x.json");
        fs::create_dir_all(&root).unwrap();
        write_once(&path, b"{}\n").unwrap();
        write_once(&path, b"{}\n").unwrap();
        assert!(write_once(&path, b"{\"a\":1}\n").is_err());
        fs::remove_dir_all(root).unwrap();
    }
    fn temp_session(label: &str) -> (PathBuf, Session) {
        let root = std::env::temp_dir().join(format!("mini-shell-{label}-{}-{}", std::process::id(), nonce()));
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
    fn doc_verbs_are_one_client_operation_each() {
        let s = session();
        let (command, flags, writes) = client(plan(&s, "doc new paper").unwrap());
        assert_eq!(command, "workspace");
        assert_eq!(
            flags,
            pairs(&[
                ("action", "create"),
                ("dir", "/w"),
                ("name", "paper"),
                ("storage", "content"),
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
        for missing in ["doc annotate paper 1 'x'", "doc quote paper wall 1"] {
            assert!(matches!(plan(&s, missing).unwrap(), Plan::NotHere(t) if t.contains("K-CONTENT-ACTIONS")));
        }
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
        assert_eq!(
            flags,
            pairs(&[
                ("action", "create"),
                ("dir", s.workspace.to_str().unwrap()),
                ("name", "lab"),
                ("storage", "declared"),
                ("predicate", law_path.to_str().unwrap()),
                ("room-template", "open"),
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
        let (_, request) = request_of(plan(&s, "room invite i1 lab 12").unwrap());
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
            "name":"lab","recipient":"12","verbs":["observe","place"],"maxCost":"50000","room":true}));
        let (_, request) = request_of(plan(&s,
            "room invite i2 lab 12 --verbs observe,place,delegate --fields 1,annotations --max-delta 7=50").unwrap());
        assert_eq!(request["verbs"], json!(["observe","place","delegate"]));
        assert_eq!(request["fields"], json!(["1","annotations"]));
        assert_eq!(request["maxDelta"], json!([{"field":"7","max":"50"}]));
        let (_, request) = request_of(plan(&s, "room kick k1 lab 12").unwrap());
        assert_eq!(request, json!({"type":"minidregg-workspace-proposal-v1","action":"revoke",
            "name":"lab","recipient":"12"}));
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
        // A public room's kick is K-ROOM's revoke proposal, unchanged.
        let (_, request) = request_of(plan(&s, "room kick k2 pub 12").unwrap());
        assert_eq!(request["action"], "revoke");
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
    fn inbox_and_guide_are_local() {
        let s = session();
        assert_eq!(plan(&s, "inbox").unwrap(), Plan::Inbox);
        assert_eq!(plan(&s, "help guide").unwrap(), Plan::Guide);
        assert_eq!(plan(&s, "help doc").unwrap(), Plan::Help(Some("doc".into())));
        assert!(plan(&s, "inbox all").is_err());
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
}
