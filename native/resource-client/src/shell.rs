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
    Verb { name: "whoami", usage: "whoami", operation: "local: this session's workspace, home and subject" },
    Verb { name: "keygen", usage: "keygen FILE", operation: "mini keygen --secret HOME/keys/FILE --public HOME/keys/FILE.pub" },
    Verb { name: "init", usage: "init KEYFILE SUBJECT", operation: "mini workspace --action init --key HOME/keys/KEYFILE --subject SUBJECT" },
    Verb { name: "enroll", usage: "enroll plan NAME KEYFILE|PUBLIC-KEY-HEX [FACTORY-REF] | enroll offer NAME | enroll seal NAME [SIGNATURE-HEX] | enroll submit|lookup NAME | enroll welcome NAME", operation: "mini enroll --action plan|offer|seal|submit|lookup|welcome --dir HOME/enroll/NAME (a hex public key plans with --new-public-key: the newcomer's secret stays on their machine)" },
    Verb { name: "provision", usage: "provision NAME HOLDER FUNDING PREDICATE-JSON|@FILE [FACTORY-REF]", operation: "mini workspace --action provision --name NAME --holder HOLDER --funding FUNDING --account-predicate HOME/requests/provision-NAME.json" },
    Verb { name: "refs", usage: "refs", operation: "mini workspace --action list" },
    Verb { name: "read", usage: "read REF", operation: "mini workspace --action read --name REF" },
    Verb { name: "describe", usage: "describe REF", operation: "mini workspace --action describe --name REF" },
    Verb { name: "import", usage: "import NAME REFERENCE-JSON|@FILE | import NAME KIND TARGET OBSERVE [OPERATION|- [CONTROL]]", operation: "mini workspace --action import (--from-ref | --kind --target --observe-capability)" },
    Verb { name: "create", usage: "create NAME STORAGE PREDICATE-JSON|@FILE", operation: "mini workspace --action create" },
    Verb { name: "propose", usage: "propose ID REQUEST-JSON|@FILE", operation: "mini workspace --action propose --proposal-id ID" },
    Verb { name: "invoke", usage: "invoke ID REF create FIELD VALUE | invoke ID REF write FIELD VALUE EXPECTED", operation: "mini workspace --action propose (action invoke, one scalar action)" },
    Verb { name: "delegate", usage: "delegate ID REF RECIPIENT VERB[,VERB...] MAX-COST", operation: "mini workspace --action propose (action delegate)" },
    Verb { name: "law", usage: "law ID REF PREDICATE-JSON|@FILE", operation: "mini workspace --action propose (action install-policy)" },
    Verb { name: "submit", usage: "submit ID", operation: "mini workspace --action submit --intent proposals/ID/intent.json --attempt attempts/ID" },
    Verb { name: "lookup", usage: "lookup ID", operation: "mini workspace --action recover --attempt attempts/ID" },
    Verb { name: "retry", usage: "retry ID", operation: "mini retry --attempt attempts/ID --mode submit" },
    Verb { name: "publish", usage: "publish ID", operation: "mini workspace --action publish-delegation --proposal-id ID --attempt attempts/ID" },
    Verb { name: "export", usage: "export ID", operation: "local: print proposals/ID/recipient-reference.json" },
    Verb { name: "history", usage: "history [all]", operation: "local: retained attempts and their last Host outcome" },
    Verb { name: "help", usage: "help [VERB]", operation: "local" },
    Verb { name: "exit", usage: "exit", operation: "local" },
];

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
    Export(PathBuf),
    History { all: bool },
    Help(Option<String>),
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
    let w = words(line)?;
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
            arity(&w, 0, 1, "help [VERB]")?;
            Plan::Help(w.get(1).cloned())
        }
        "exit" | "quit" => {
            arity(&w, 0, 0, u)?;
            Plan::Exit
        }
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
                ],
            )
        }
        "init" => {
            arity(&w, 2, 2, u)?;
            session_file(&w[1], "key file")?;
            decimal(&w[2], "subject")?;
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
                flag("dir", ws()),
            ]);
            client("workspace", flags)
        }
        "enroll" => {
            let Some(action) = w.get(1) else {
                return Err(u.to_owned());
            };
            match action.as_str() {
                "plan" => {
                    arity(&w, 3, 4, u)?;
                    workspace_name(&w[2], "enrollment name")?;
                    let factory = w.get(4).cloned().unwrap_or_else(|| "factory".into());
                    workspace_name(&factory, "factory reference")?;
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
        "refs" => {
            arity(&w, 0, 0, u)?;
            client("workspace", vec![flag("action", "list"), flag("dir", ws())])
        }
        "read" | "describe" => {
            arity(&w, 1, 1, u)?;
            workspace_name(&w[1], "reference name")?;
            client(
                "workspace",
                vec![flag("action", verb.clone()), flag("dir", ws()), flag("name", w[1].clone())],
            )
        }
        "import" => {
            arity(&w, 2, 6, u)?;
            workspace_name(&w[1], "reference name")?;
            let second = &w[2];
            if second.starts_with('{') || second.starts_with('@') {
                arity(&w, 2, 2, u)?;
                let value = json_argument(session, second, "reference")?;
                let path = session.home.join("inbox").join(format!("{}.json", w[1]));
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
            workspace_name(&w[1], "resource name")?;
            let predicate = json_argument(session, &w[3], "predicate")?;
            let path = session.home.join("requests").join(format!("create-{}.json", w[1]));
            Plan::Client {
                command: "workspace".into(),
                flags: vec![
                    flag("action", "create"),
                    flag("dir", ws()),
                    flag("name", w[1].clone()),
                    flag("storage", w[2].clone()),
                    flag("predicate", path.clone()),
                ],
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
            workspace_name(&w[2], "reference name")?;
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                "targets":[{"name":w[2],"payload":{"type":"scalar","actions":[scalar]}}]});
            proposal(session, &w[1], &request)
        }
        "delegate" => {
            arity(&w, 5, 5, u)?;
            workspace_name(&w[1], "proposal ID")?;
            workspace_name(&w[2], "reference name")?;
            let verbs: Vec<&str> = w[4].split(',').collect();
            let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
                "name":w[2],"recipient":w[3],"verbs":verbs,"maxCost":w[5]});
            proposal(session, &w[1], &request)
        }
        "law" => {
            arity(&w, 3, 3, u)?;
            workspace_name(&w[1], "proposal ID")?;
            workspace_name(&w[2], "reference name")?;
            let predicate = json_argument(session, &w[3], "predicate")?;
            let request = json!({"type":"minidregg-workspace-proposal-v1",
                "action":"install-policy","name":w[2],"predicate":predicate});
            proposal(session, &w[1], &request)
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

fn help(topic: Option<&str>) {
    match topic {
        Some(name) => match VERBS.iter().find(|v| v.name == name) {
            Some(v) => println!("{}\n  = {}", v.usage, v.operation),
            None => println!("no verb {name}"),
        },
        None => {
            println!("Every verb is one client operation; the Host decides. Words: 'literal', \"escaped\", {{json}} or [json], @FILE (HOME/requests/FILE).");
            for v in VERBS {
                println!("  {:<10} {}", v.name, v.usage);
            }
            println!("Endings on stderr: usage: (2)  error: client (1)  refused: Host (3)  undecided: Host (4).");
        }
    }
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
            help(topic.as_deref());
            Ending::Done
        }
        Ok(Plan::History { all }) => {
            history(session, all);
            Ending::Done
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
    let refs = || stems(&session.workspace.join("refs"), ".json", |_| false);
    let proposals = || stems(&session.workspace.join("proposals"), "", |_| false);
    let attempts = || stems(&session.workspace.join("attempts"), "", |n| n.starts_with("a-"));
    let keys = || stems(&session.home.join("keys"), "", |n| n.ends_with(".pub"));
    let enrolled = || stems(&session.home.join("enroll"), "", |_| false);
    let verb = w[0].as_str();
    let candidates: Vec<String> = match (verb, position) {
        (_, 0) => VERBS.iter().map(|v| v.name.to_owned()).collect(),
        ("read" | "describe", 1) => refs(),
        ("submit" | "publish" | "export", 1) => proposals(),
        ("lookup" | "retry", 1) => attempts(),
        ("help", 1) => VERBS.iter().map(|v| v.name.to_owned()).collect(),
        ("history", 1) => vec!["all".into()],
        ("init", 1) => keys(),
        ("enroll", 1) => ["plan", "offer", "seal", "submit", "lookup", "welcome"].map(String::from).to_vec(),
        ("enroll", 2) if w[1] != "plan" => enrolled(),
        ("enroll", 3) if w[1] == "plan" => keys(),
        ("invoke" | "delegate" | "law", 2) => refs(),
        ("invoke", 3) => vec!["create".into(), "write".into()],
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
        eprintln!("mini shell: workspace {}. help lists verbs; every decision is the Host's.", session.workspace.display());
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
        assert_eq!(
            client(plan(&s, "enroll plan newcomer-1 nc.key").unwrap()),
            (
                "enroll".into(),
                pairs(&[
                    ("action", "plan"),
                    ("sponsor-workspace", "/w"),
                    ("factory-ref", "factory"),
                    ("name", "newcomer-1"),
                    ("new-key", "/h/keys/nc.key"),
                    ("dir", "/h/enroll/newcomer-1"),
                ]),
                vec![]
            )
        );
        assert_eq!(
            client(plan(&s, "init mini.key 42").unwrap()).1,
            pairs(&[
                ("action", "init"),
                ("host", "/bin/host"),
                ("config", "/c.json"),
                ("key", "/h/keys/mini.key"),
                ("subject", "42"),
                ("dir", "/w"),
            ])
        );
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
        let plan_line = format!("enroll plan alice {public}");
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
                ("dir", "/h/enroll/alice"),
            ])
        );
        assert!(!flags.iter().any(|(k, _)| k == "new-key"));
        assert_eq!(writes, vec![(PathBuf::from("/h/keys/alice.pub"), vec![0xab; 32])]);

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
            "read a/b",
            "propose x @../../etc/passwd",
            "import r @/abs",
        ] {
            assert!(plan(&s, bad).is_err(), "{bad} should be refused");
        }
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
        assert_eq!(complete(&s, "su"), ["submit"]);
        assert_eq!(complete(&s, "re"), ["refs", "read", "retry"]);
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
}
