//! The Hermes ROOM RUNNER (PLACE §2.7, §5 row 7): Hermes's controller for one
//! room it was summoned into.
//!
//! An attach: adopt what the founder handed over (`summon`'s hand-off in the
//! inbox: the budget account, the invitation, the delegated documents), join
//! the room's roster as any friend does, read the program DOCUMENT from the
//! room (members can read it; the founder edits it), and then run the model:
//! a chat-completions exchange with the provider whose function list is the
//! room tools (`resource_tools::room_tool_specs`). Every tool call is one of
//! those tools, run by the pinned `mini` client under HERMES'S OWN workspace;
//! the Host judges each one. Every write is a turn, paid first
//! (`RoomTools::pay`, refused at plan `bookRefused` when the budget cannot
//! cover it: the write is not attempted and Hermes says "out of budget" in
//! its stream, once per attach).
//!
//! The controller's discipline is M5's, journaled line by line (`journal.jsonl`,
//! fsynced before the act it records):
//! - `send K` before a provider request leaves, `recv K` after the reply; a
//!   `send` without its `recv` at restart is ABANDONED, never resent (the
//!   provider's own log is the count);
//! - `deciding` before a write's payment, `paid` after it, `submitter PID`
//!   when the client that submits is spawned, `resolved` with its outcome;
//!   at restart a paid, unresolved write waits for its submitter to be gone
//!   (the pid is no longer that client) and is resolved by EXACT LOOKUP of
//!   its fixed proposal id (`hr-OP`), or for a `say` by a signed tail of
//!   Hermes's own stream; never by a second send.
//!
//! This is the controller binary with M5's client-contract discipline, not
//! an AgentGrain task unit: a room Hermes is an ordinary enrolled participant
//! whose budget is a Book account, so it needs no grain purse and no
//! historical grain birth. The same room tools are offered to an AgentGrain
//! Hermes through the MCP broker (`toolTask.room`).
use crate::resource_tools::{RoomTools, RoomToolsConfig, ROOM_WRITE_TOOLS};
use crate::Result;
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::net::TcpStream;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Config {
    #[serde(rename = "type")]
    kind: String,
    /// The room tools: the pinned client, Hermes's workspace and home, the
    /// room, Hermes's budget account reference.
    tools: RoomToolsConfig,
    /// Where `summon`'s hand-off arrives (`summon-ROOM.json`, the account
    /// handoff, the invitation, the delegated references, `dismiss-ROOM.json`).
    inbox: PathBuf,
    /// The journal and the transcript.
    state: PathBuf,
    provider: Option<Provider>,
    #[serde(default = "default_rounds")]
    max_rounds: u32,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Provider {
    /// `http://127.0.0.1:PORT/v1` (loopback; the deterministic provider on a
    /// test box, the node's provider gateway on a real one).
    url: String,
    model: String,
}

fn default_rounds() -> u32 {
    8
}

fn now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

// ---------------------------------------------------------------- journal

#[derive(Default, Debug)]
pub(crate) struct Op {
    pub tool: String,
    pub arguments: Value,
    pub paid: bool,
    pub unpaid: bool,
    pub submitter: Option<u32>,
    pub resolved: Option<String>,
}

#[derive(Default, Debug)]
pub(crate) struct Journal {
    path: PathBuf,
    pub next_op: u64,
    pub next_request: u64,
    pub attaches: u64,
    pub ops: BTreeMap<u64, Op>,
    pub sent: BTreeMap<u64, bool>,
    pub returned: bool,
}

impl Journal {
    pub(crate) fn open(path: &Path) -> Result<Self> {
        let mut journal = Journal { path: path.to_owned(), next_op: 1, next_request: 1, ..Journal::default() };
        let Ok(text) = fs::read_to_string(path) else { return Ok(journal) };
        for (index, line) in text.lines().enumerate() {
            if line.trim().is_empty() {
                continue;
            }
            let value: Value = serde_json::from_str(line).map_err(|e| format!("journal line {}: {e}", index + 1))?;
            journal.apply(&value);
        }
        Ok(journal)
    }

    fn apply(&mut self, value: &Value) {
        let number = |key: &str| value.get(key).and_then(Value::as_u64);
        match value.get("event").and_then(Value::as_str).unwrap_or("") {
            "send" => {
                if let Some(k) = number("request") {
                    self.sent.insert(k, false);
                    self.next_request = self.next_request.max(k + 1);
                }
            }
            "recv" | "abandoned" => {
                if let Some(k) = number("request") {
                    self.sent.insert(k, true);
                }
            }
            "deciding" => {
                if let Some(op) = number("op") {
                    self.next_op = self.next_op.max(op + 1);
                    let entry = self.ops.entry(op).or_default();
                    entry.tool = value["tool"].as_str().unwrap_or("").to_owned();
                    entry.arguments = value["arguments"].clone();
                }
            }
            "paid" => {
                if let Some(op) = number("op") {
                    self.ops.entry(op).or_default().paid = true;
                }
            }
            "unpaid" => {
                if let Some(op) = number("op") {
                    let entry = self.ops.entry(op).or_default();
                    entry.unpaid = true;
                    entry.resolved = Some("not-attempted".into());
                }
            }
            "submitter" => {
                if let (Some(op), Some(pid)) = (number("op"), number("pid")) {
                    self.ops.entry(op).or_default().submitter = u32::try_from(pid).ok();
                }
            }
            "resolved" => {
                if let Some(op) = number("op") {
                    self.ops.entry(op).or_default().resolved =
                        Some(value["resolution"].as_str().unwrap_or("uncertain").to_owned());
                }
            }
            "attach" => {
                if value["phase"] == "begin" {
                    self.attaches = self.attaches.max(number("attach").unwrap_or(0));
                }
            }
            "returned" => self.returned = true,
            _ => {}
        }
    }

    pub(crate) fn append(&mut self, mut value: Value) -> Result<()> {
        value["at"] = json!(now());
        let mut line = serde_json::to_vec(&value).map_err(|e| e.to_string())?;
        line.push(b'\n');
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .map_err(|e| format!("{}: {e}", self.path.display()))?;
        file.write_all(&line).and_then(|_| file.sync_all()).map_err(|e| e.to_string())?;
        self.apply(&value);
        println!("{}", String::from_utf8_lossy(&line).trim_end());
        Ok(())
    }
}

// ---------------------------------------------------------------- provider

/// One non-streaming chat-completions exchange over loopback HTTP/1.1.
fn complete(provider: &Provider, body: &Value) -> Result<Value> {
    let rest = provider.url.strip_prefix("http://").ok_or("provider url must be http://HOST:PORT/PATH")?;
    let (authority, prefix) = rest.split_once('/').map(|(a, p)| (a, format!("/{p}"))).unwrap_or((rest, String::new()));
    let host = authority.rsplit_once(':').map(|(h, _)| h).unwrap_or(authority);
    if !(host == "127.0.0.1" || host == "localhost" || host == "[::1]") {
        return Err("the room runner speaks only to a loopback provider (the node's gateway)".into());
    }
    let bytes = serde_json::to_vec(body).map_err(|e| e.to_string())?;
    let mut stream = TcpStream::connect(authority).map_err(|e| format!("provider {authority}: {e}"))?;
    stream.set_read_timeout(Some(Duration::from_secs(600))).map_err(|e| e.to_string())?;
    write!(
        stream,
        "POST {}/chat/completions HTTP/1.1\r\nHost: {authority}\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n",
        prefix.trim_end_matches('/'),
        bytes.len()
    )
    .and_then(|_| stream.write_all(&bytes))
    .and_then(|_| stream.flush())
    .map_err(|e| format!("provider send: {e}"))?;
    let mut reply = Vec::new();
    stream.read_to_end(&mut reply).map_err(|e| format!("provider reply: {e}"))?;
    let text = String::from_utf8_lossy(&reply);
    let (head, body) = text.split_once("\r\n\r\n").ok_or("provider reply has no header end")?;
    let status = head.lines().next().unwrap_or("");
    if !status.contains(" 200 ") {
        return Err(format!("provider answered {status}: {}", body.chars().take(400).collect::<String>()));
    }
    let value: Value = serde_json::from_str(body).map_err(|e| format!("provider body: {e}"))?;
    value
        .pointer("/choices/0/message")
        .cloned()
        .ok_or_else(|| "provider reply has no choices[0].message".to_owned())
}

/// The room tools as the provider's function list.
fn functions() -> Value {
    json!(crate::resource_tools::room_tool_specs()
        .into_iter()
        .map(|spec| json!({"type":"function","function":{"name":spec["name"],
            "description":spec["description"],"parameters":spec["inputSchema"]}}))
        .collect::<Vec<_>>())
}

// ---------------------------------------------------------------- runner

struct Runner<'a> {
    config: &'a Config,
    tools: RoomTools<'a>,
    journal: Journal,
}

fn read_json(path: &Path) -> Option<Value> {
    serde_json::from_slice(&fs::read(path).ok()?).ok()
}

/// Is `pid` still the client this journal spawned for proposal `id` (or for a
/// `say`)? A pid that is gone, or now names another program, is no longer a
/// submitter: what it sent is final and an exact lookup decides it.
fn submitter_alive(pid: u32, marker: &str) -> bool {
    match fs::read(format!("/proc/{pid}/cmdline")) {
        Ok(bytes) => {
            let cmdline = String::from_utf8_lossy(&bytes);
            cmdline.contains("shell") && cmdline.contains(&format!("{marker}\u{0}"))
        }
        Err(_) => false,
    }
}

impl Runner<'_> {
    fn room(&self) -> &str {
        &self.config.tools.room
    }

    fn mini(&self, args: &[&str]) -> Result<String> {
        let output = Command::new(&self.config.tools.mini)
            .args(args)
            .arg("--socket")
            .arg(&self.config.tools.socket)
            .output()
            .map_err(|e| format!("{}: {e}", self.config.tools.mini.display()))?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let tail: Vec<&str> = stderr.lines().rev().take(4).collect();
            return Err(format!(
                "mini {} exited {}: {}",
                args.first().copied().unwrap_or(""),
                output.status.code().unwrap_or(-1),
                tail.into_iter().rev().collect::<Vec<_>>().join(" | ")
            ));
        }
        Ok(String::from_utf8_lossy(&output.stdout).into_owned())
    }

    fn ws(&self) -> String {
        self.config.tools.workspace.display().to_string()
    }

    /// Settle what a previous run left open, before anything new.
    fn recover(&mut self) -> Result<()> {
        let abandoned: Vec<u64> = self.journal.sent.iter().filter(|(_, done)| !**done).map(|(k, _)| *k).collect();
        for k in abandoned {
            self.journal.append(json!({"event":"abandoned","request":k,
                "basis":"sent before the controller stopped; its reply was never recorded; not resent"}))?;
        }
        let open: Vec<u64> = self.journal.ops.iter().filter(|(_, op)| op.resolved.is_none()).map(|(k, _)| *k).collect();
        for op in open {
            let (tool, arguments, paid, submitter) = {
                let entry = &self.journal.ops[&op];
                (entry.tool.clone(), entry.arguments.clone(), entry.paid, entry.submitter)
            };
            let id = RoomTools::proposal(&op.to_string());
            if !paid {
                self.journal.append(json!({"event":"resolved","op":op,"resolution":"uncertain",
                    "basis":"the turn's payment was in flight when the controller stopped; not resent"}))?;
                continue;
            }
            if let Some(pid) = submitter {
                let marker = if tool == "mini_say" { format!("{id}.txt") } else { format!("submit {id}") };
                let start = Instant::now();
                while submitter_alive(pid, &marker) {
                    if start.elapsed() > Duration::from_secs(600) {
                        return Err(format!("operation {op}'s submitter {pid} is still running after 600 s; not deciding"));
                    }
                    std::thread::sleep(Duration::from_millis(500));
                }
                self.journal.append(json!({"event":"submitter-stopped","op":op,"pid":pid,
                    "proof":"/proc/PID/cmdline no longer names this operation's client"}))?;
            }
            let resolution = if tool == "mini_say" {
                self.said_already(&arguments)?
            } else {
                self.tools.lookup(&op.to_string())?
            };
            let mut event = resolution;
            event["event"] = json!("resolved");
            event["op"] = json!(op);
            event["recovered"] = json!(true);
            self.journal.append(event)?;
        }
        Ok(())
    }

    /// A `say` has no fixed proposal id: after its submitter stopped, a
    /// signed tail of the room decides whether Hermes's entry with exactly
    /// this text landed.
    fn said_already(&self, arguments: &Value) -> Result<Value> {
        let text = arguments["text"].as_str().unwrap_or("");
        let tail = self.tools.read("mini_stream_tail", &json!({"n":"100"}))?;
        let me = self.me()?;
        let found = tail["entries"].as_array().into_iter().flatten().find(|e| {
            e["author"].as_str() == Some(me.as_str()) && e["text"].as_str() == Some(text)
        });
        Ok(match found {
            Some(entry) => json!({"resolution":"performed","basis":"signed-tail","entry":entry["n"]}),
            None => json!({"resolution":"refused","basis":"absent-after-submitter-stop (signed tail)"}),
        })
    }

    fn me(&self) -> Result<String> {
        let ws = read_json(&self.config.tools.workspace.join("workspace.json")).ok_or("Hermes's workspace has no workspace.json")?;
        ws["subject"].as_str().map(str::to_owned).ok_or_else(|| "workspace.json names no subject".into())
    }

    /// Adopt the founder's hand-off and join the room (idempotent).
    fn adopt(&mut self) -> Result<Value> {
        let inbox = self.config.inbox.display().to_string();
        let ws = self.ws();
        let adopted = self.mini(&["credit", "--action", "adopt", "--dir", &ws, "--inbox", &inbox])?;
        let room = self.room().to_owned();
        let manifest = read_json(&self.config.inbox.join(format!("summon-{room}.json")))
            .ok_or_else(|| format!("no summon-{room}.json in the inbox: nobody summoned this Hermes into {room}"))?;
        if !self.config.tools.home.join("chat").join("rooms").join(format!("{room}.json")).exists() {
            let invite = self.config.inbox.join(format!("{room}-invite.json"));
            let requests = self.config.tools.home.join("requests");
            fs::create_dir_all(&requests).map_err(|e| e.to_string())?;
            fs::copy(&invite, requests.join(format!("{room}-invite.json")))
                .map_err(|e| format!("{}: {e}", invite.display()))?;
            let run = self.tools.line(&format!("chat join {room} @{room}-invite.json"))?;
            if run.code != 0 {
                return Err(format!("chat join {room}: {}", run.ending()));
            }
            self.journal.append(json!({"event":"joined","room":room,"line":run.stdout.trim()}))?;
        }
        // The program document: read under the room grant.
        let program = manifest["program"]["name"].as_str().ok_or("the manifest names no program")?.to_owned();
        let target = manifest["program"]["target"].as_str().ok_or("the manifest names no program target")?.to_owned();
        if !self.config.tools.workspace.join("refs").join(format!("{}.json", program.replace('/', "."))).exists() {
            let grant = read_json(&self.config.tools.workspace.join("refs").join(format!("{room}.json")))
                .ok_or_else(|| format!("no room grant reference {room}"))?;
            let capability = grant["observeCapability"].as_str().ok_or("the room grant has no capability")?.to_owned();
            self.mini(&[
                "workspace", "--action", "import", "--dir", &ws, "--name", &program, "--kind", "object",
                "--target", &target, "--observe-capability", &capability, "--operation-capability", &capability,
            ])?;
        }
        if adopted.contains("\"adopted\"") && !adopted.contains("\"adopted\": []") {
            self.journal.append(json!({"event":"adopted","output":adopted.trim()}))?;
        }
        Ok(manifest)
    }

    /// One write tool call: pay, then write, journaled between.
    fn write(&mut self, name: &str, arguments: &Value, out_of_budget: &mut Option<String>) -> Result<Value> {
        if let Some(reason) = out_of_budget {
            return Ok(json!({"error":format!("not attempted: {reason}")}));
        }
        let op = self.journal.next_op;
        self.journal.append(json!({"event":"deciding","op":op,"tool":name,"arguments":arguments}))?;
        let op_s = op.to_string();
        match self.tools.pay(&op_s, name) {
            Ok(payment) => self.journal.append(json!({"event":"paid","op":op,"payment":payment}))?,
            Err(reason) => {
                self.journal.append(json!({"event":"unpaid","op":op,"reason":reason}))?;
                if reason.starts_with("out of budget") {
                    let account = self.config.tools.account.clone().unwrap_or_default();
                    let text = format!(
                        "out of budget: my account {account} cannot pay this room's turn, so I stopped. `topup {} N` refills it.",
                        self.room()
                    );
                    match self.tools.notice(&text) {
                        Ok(run) => self.journal.append(json!({"event":"notice","text":text,"said":run.stdout.trim()}))?,
                        Err(e) => self.journal.append(json!({"event":"notice-failed","text":text,"error":e}))?,
                    }
                    *out_of_budget = Some(reason.clone());
                }
                return Ok(json!({"error":reason}));
            }
        }
        let result = {
            let journal = &mut self.journal;
            self.tools.write(&op_s, name, arguments, &mut |pid| {
                let _ = journal.append(json!({"event":"submitter","op":op,"pid":pid}));
            })
        };
        match result {
            Ok(value) => {
                self.journal.append(json!({"event":"resolved","op":op,"resolution":"performed","result":value}))?;
                Ok(json!({"ok":value}))
            }
            Err(ending) => {
                self.journal.append(json!({"event":"resolved","op":op,"resolution":"refused","basis":"host-refusal","detail":ending}))?;
                Ok(json!({"error":ending}))
            }
        }
    }

    fn dismissed(&mut self) -> Result<bool> {
        let room = self.room().to_owned();
        let Some(notice) = read_json(&self.config.inbox.join(format!("dismiss-{room}.json"))) else { return Ok(false) };
        if self.journal.returned {
            return Ok(true);
        }
        let to = notice["returnTo"].as_str().ok_or("the dismissal names no account to return to")?.to_owned();
        let account = self.config.tools.account.clone().ok_or("this runner has no budget account")?;
        let ws = self.ws();
        let out = self.mini(&["credit", "--action", "return", "--dir", &ws, "--account", &account, "--to", &to])?;
        let value = crate::resource_tools::last_json(&out).unwrap_or(Value::Null);
        self.journal.append(json!({"event":"returned","room":room,"to":to,"result":value}))?;
        Ok(true)
    }

    fn attach(&mut self, manifest: &Value) -> Result<()> {
        let attach = self.journal.attaches + 1;
        self.journal.append(json!({"event":"attach","phase":"begin","attach":attach}))?;
        let program_name = manifest["program"]["name"].as_str().unwrap_or("").to_owned();
        let program = self.tools.read("mini_doc_show", &json!({"doc":program_name}))?;
        let me = self.me()?;
        let docs: Vec<String> = manifest["docs"].as_array().into_iter().flatten().filter_map(|d| d["name"].as_str().map(str::to_owned)).collect();
        let brief = json!({"type":"mini-hermes-attach-v1","room":self.room(),"me":me,"role":manifest["role"],
            "program":program_name,"docs":docs,"every":manifest["every"],"account":self.config.tools.account,
            "attach":attach});
        let mut messages = vec![
            json!({"role":"system","content":program["text"]}),
            json!({"role":"user","content":brief.to_string()}),
        ];
        let mut out_of_budget: Option<String> = None;
        let mut summary = String::new();
        for round in 1..=self.config.max_rounds {
            let k = self.journal.next_request;
            let provider = self.config.provider.as_ref().ok_or("legacy room runner requires a provider")?;
            let body = json!({"model":provider.model,"messages":messages,"tools":functions(),
                "stream":false,"user":format!("hermes-room-{k}")});
            self.journal.append(json!({"event":"send","request":k,"attach":attach,"round":round,"messages":messages.len()}))?;
            let message = complete(provider, &body)?;
            self.journal.append(json!({"event":"recv","request":k,"message":message}))?;
            let calls: Vec<Value> = message.get("tool_calls").and_then(Value::as_array).cloned().unwrap_or_default();
            if calls.is_empty() {
                summary = message.get("content").and_then(Value::as_str).unwrap_or("").to_owned();
                break;
            }
            messages.push(message.clone());
            for call in calls {
                let id = call["id"].as_str().unwrap_or("").to_owned();
                let name = call.pointer("/function/name").and_then(Value::as_str).unwrap_or("").to_owned();
                let arguments: Value = call
                    .pointer("/function/arguments")
                    .and_then(Value::as_str)
                    .and_then(|a| serde_json::from_str(a).ok())
                    .unwrap_or(Value::Null);
                let result = if ROOM_WRITE_TOOLS.contains(&name.as_str()) {
                    self.write(&name, &arguments, &mut out_of_budget)?
                } else {
                    match self.tools.read(&name, &arguments) {
                        Ok(value) => json!({"ok":value}),
                        Err(error) => json!({"error":error}),
                    }
                };
                messages.push(json!({"role":"tool","tool_call_id":id,"content":result.to_string()}));
            }
        }
        self.journal.append(json!({"event":"attach","phase":"end","attach":attach,"summary":summary,
            "outOfBudget":out_of_budget.is_some()}))?;
        Ok(())
    }
}

/// Read a room assignment for the durable ACP controller. No provider call
/// or room write occurs here. The existing ordinary participant adoption is
/// shared with the legacy runner; the worker receives only the signed text.
pub(crate) fn prepare_resident(tools: &RoomToolsConfig, inbox: &Path, state: &Path) -> Result<Value> {
    let dismissal = inbox.join(format!("dismiss-{}.json", tools.room));
    if dismissal.exists() {
        let notice = read_json(&dismissal).ok_or("dismissal notice is not readable JSON")?;
        let manifest = read_json(&inbox.join(format!("summon-{}.json", tools.room)))
            .ok_or("dismissal has no retained summon manifest")?;
        let to = notice["returnTo"].as_str().ok_or("dismissal lacks return destination")?;
        if notice["type"] != "mini-hermes-dismiss-v1" || notice["room"] != tools.room
            || notice["hermes"] != manifest["hermes"] || notice["founder"] != manifest["founder"]
            || notice["account"] != manifest["account"] || manifest["founderAccount"] != to
            || notice["account"]["name"].as_str() != tools.account.as_deref()
        { return Err("dismissal differs from this room's retained summon assignment".into()); }
        return Ok(json!({"dismissed":true,"returnTo":to}));
    }
    let config = Config { kind:"mini-hermes-room-runner-v1".into(),tools:tools.clone(),
        inbox:inbox.to_owned(),state:state.to_owned(),
        provider:None,max_rounds:1 };
    let journal = Journal::open(&state.join("adoption.jsonl"))?;
    let mut runner = Runner { config:&config,tools:RoomTools { config:tools },journal };
    let manifest = runner.adopt()?;
    let name = manifest["program"]["name"].as_str().ok_or("resident program name absent")?;
    let program = runner.tools.read("mini_doc_show", &json!({"doc":name}))?;
    let me = runner.me()?;
    let tail = runner.tools.read("mini_stream_tail", &json!({"n":"100"}))?;
    let entries: Vec<Value> = tail["entries"].as_array().into_iter().flatten()
        .filter(|entry| entry["author"].as_str() != Some(me.as_str())).rev().take(20).cloned().collect();
    let room = runner.tools.read("mini_room_ls", &json!({}))?;
    let member_changes: Vec<Value> = room["entries"].as_array().into_iter().flatten()
        .filter(|entry| entry["subject"].as_str() != Some(me.as_str())).rev().take(20).cloned().collect();
    let room_status = runner.tools.read("mini_room_status", &json!({}))?;
    Ok(json!({"type":"mini-hermes-resident-assignment-v1","room":tools.room,"me":me,
        "role":manifest["role"],"programName":name,"program":program["text"],
        "docs":manifest["docs"],"every":manifest["every"],"account":tools.account,
        "recentMemberEntries":entries,"recentMemberChanges":member_changes,"roomStatus":room_status}))
}

/// One attach: recover, adopt, return the budget when dismissed, else run the
/// program once.
pub(crate) fn step(config: &Config) -> Result<()> {
    if config.kind != "mini-hermes-room-runner-v1" || config.provider.is_none() {
        return Err("legacy config requires mini-hermes-room-runner-v1 and a provider".into());
    }
    fs::create_dir_all(&config.state).map_err(|e| format!("{}: {e}", config.state.display()))?;
    let journal = Journal::open(&config.state.join("journal.jsonl"))?;
    let mut runner = Runner { config, tools: RoomTools { config: &config.tools }, journal };
    runner.recover()?;
    if runner.dismissed()? {
        println!("hermes-room: dismissed from {}; the budget was returned", config.tools.room);
        return Ok(());
    }
    let manifest = runner.adopt()?;
    runner.attach(&manifest)
}

pub(crate) fn main(args: &[std::ffi::OsString]) -> Result<()> {
    let words: Vec<String> = args.iter().map(|a| a.to_string_lossy().into_owned()).collect();
    let (mode, path, every) = match words.as_slice() {
        [mode, path] => (mode.as_str(), path, None),
        [mode, path, seconds] => (mode.as_str(), path, Some(seconds.parse::<u64>().map_err(|_| "SECONDS must be a number")?)),
        _ => return Err("usage: grain-runtime hermes-room step|serve CONFIG [SECONDS]".into()),
    };
    let config: Config = serde_json::from_slice(&fs::read(path).map_err(|e| format!("{path}: {e}"))?)
        .map_err(|e| format!("{path}: {e}"))?;
    match mode {
        "step" => step(&config),
        "serve" => loop {
            if let Err(error) = step(&config) {
                eprintln!("hermes-room: {error}");
            }
            if config.inbox.join(format!("dismiss-{}.json", config.tools.room)).exists()
                && Journal::open(&config.state.join("journal.jsonl"))?.returned
            {
                return Ok(());
            }
            std::thread::sleep(Duration::from_secs(every.unwrap_or(30)));
        },
        _ => Err("mode must be step or serve".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn journal_with(lines: &[Value]) -> Journal {
        let dir = std::env::temp_dir().join(format!("hermes-room-journal-{}-{}", std::process::id(), now()));
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join(format!("j-{}.jsonl", lines.len()));
        let _ = fs::remove_file(&path);
        let text: String = lines.iter().map(|l| format!("{l}\n")).collect();
        fs::write(&path, text).unwrap();
        Journal::open(&path).unwrap()
    }

    #[test]
    fn a_send_without_its_reply_is_open_and_is_never_reused() {
        let journal = journal_with(&[
            json!({"event":"send","request":1}),
            json!({"event":"recv","request":1}),
            json!({"event":"send","request":2}),
        ]);
        assert_eq!(journal.sent.get(&1), Some(&true));
        assert_eq!(journal.sent.get(&2), Some(&false));
        // The next request is a new number: request 2 is abandoned, not resent.
        assert_eq!(journal.next_request, 3);
        let after = journal_with(&[
            json!({"event":"send","request":1}),
            json!({"event":"abandoned","request":1}),
        ]);
        assert_eq!(after.sent.get(&1), Some(&true));
        assert_eq!(after.next_request, 2);
    }

    #[test]
    fn a_paid_write_without_an_outcome_stays_open_with_its_submitter() {
        let journal = journal_with(&[
            json!({"event":"deciding","op":4,"tool":"mini_doc_link","arguments":{"from":"lab-index","to":"x"}}),
            json!({"event":"paid","op":4}),
            json!({"event":"submitter","op":4,"pid":4242}),
            json!({"event":"deciding","op":5,"tool":"mini_say","arguments":{"text":"hi"}}),
            json!({"event":"unpaid","op":5,"reason":"out of budget: refused"}),
        ]);
        let open = &journal.ops[&4];
        assert!(open.paid && open.resolved.is_none() && open.submitter == Some(4242));
        assert_eq!(journal.ops[&5].resolved.as_deref(), Some("not-attempted"));
        assert_eq!(journal.next_op, 6);
    }

    #[test]
    fn a_gone_pid_is_not_a_submitter() {
        assert!(!submitter_alive(u32::MAX - 1, "hr-1"));
        // This test process is alive but is not a `mini shell` for hr-1.
        assert!(!submitter_alive(std::process::id(), "hr-1"));
    }

    #[test]
    fn the_provider_is_loopback_only() {
        let provider = Provider { url: "http://example.com:80/v1".into(), model: "m".into() };
        assert!(complete(&provider, &json!({})).unwrap_err().contains("loopback"));
    }

    #[test]
    fn the_function_list_is_the_room_tools() {
        let names: Vec<String> = functions().as_array().unwrap().iter()
            .map(|f| f["function"]["name"].as_str().unwrap().to_owned()).collect();
        assert_eq!(names.len(), 7);
        assert!(names.contains(&"mini_doc_link".to_owned()));
    }
}
