//! The room CONCIERGE (PLACE §2.10, §5 row 6): a deterministic program the
//! controller binary runs as a runner holding `delegate` under a room R.
//!
//! Program: read R's tariff (`week`, `period`) and the till's incoming ledger
//! (Host op 180: fleet turns that paid `A_R`, topic `renew`); for each entry
//! whose asset is the pinned credit asset and whose amount is at least
//! `week`, delegate `member` under R to the entry's signer with
//! `notAfter = max(entry.height, that subject's current notAfter) + period`
//! (a re-issue extends). A smaller payment is journaled `underpaid` and issues
//! nothing. When `week = 0` the room is free: each filed request from a
//! subject the Host lists as a standing member of R (`who`, a signed read)
//! issues `height + period`.
//!
//! Like M5's tools, every act is the pinned `mini` client run against the
//! concierge's own workspace: signed reads, proposals, submissions, exact
//! lookups. The concierge decides nothing the Host does not re-check: the
//! window is enforced by the kernel (`Admissible.validUntil`), and the
//! delegation is admitted only under the founder's grant to the concierge.
//! What the kernel does not yet check is that each delegation followed a
//! payment (K-BOOK-SLOTS, PLACE §4.8); until then the concierge answers for
//! that with its JOURNAL: one line per decision naming the ledger entry
//! (height, transaction, payer, signer, amount) it acted on.
//!
//! Restart: the journal is re-read; a decision whose delegation was not
//! recorded is re-run under the same proposal id, which the client resolves
//! by exact lookup (never a second send).
use crate::Result;
use serde::Deserialize;
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, SystemTime, UNIX_EPOCH};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Config {
    /// The pinned `mini` client.
    pub mini: PathBuf,
    /// The concierge's own workspace (its key, its pinned Host and socket).
    pub workspace: PathBuf,
    /// The program `room concierge` wrote (`minidregg-concierge-program-v1`).
    pub program: PathBuf,
    /// Where the founder's grants and free-room requests arrive.
    pub inbox: PathBuf,
    /// Where issued member references are left, one directory per subject.
    pub outbox: PathBuf,
    /// The journal: one JSON line per decision.
    pub journal: PathBuf,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Program {
    #[serde(rename = "type")]
    kind: String,
    room: String,
    concierge: String,
    till: String,
    topic: String,
    member_verbs: Vec<String>,
    refs: ProgramRefs,
}

#[derive(Deserialize)]
struct ProgramRefs {
    room: String,
    till: String,
}

/// One ledger entry as the Host's op 180 states it.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Entry {
    pub height: u128,
    pub transaction: String,
    pub subject: String,
    pub payer: String,
    pub asset: String,
    pub amount: u128,
}

#[derive(Debug, PartialEq)]
pub(crate) enum Decision {
    Issue { not_after: u128 },
    Underpaid { week: u128 },
    WrongAsset { asset: String },
}

/// The program's rule for one paid entry. Pure: the journal and the Host
/// supply every input.
pub(crate) fn decide(entry: &Entry, credit_asset: &str, week: u128, period: u128, current: Option<u128>) -> Decision {
    if entry.asset != credit_asset {
        return Decision::WrongAsset { asset: entry.asset.clone() };
    }
    if entry.amount < week {
        return Decision::Underpaid { week };
    }
    let from = current.map_or(entry.height, |after| after.max(entry.height));
    Decision::Issue { not_after: from + period }
}

fn number(value: &Value, key: &str) -> Result<u128> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{key} absent"))?
        .parse()
        .map_err(|_| format!("{key} is not a decimal"))
}

fn string(value: &Value, key: &str) -> Result<String> {
    value
        .get(key)
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("{key} absent"))
}

fn now() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

/// The journal: decisions keyed by the input they acted on.
struct Journal {
    path: PathBuf,
    /// Keys (`ledger:HEIGHT`, `request:FILE`) with a final decision.
    decided: BTreeSet<String>,
    /// Subject → greatest notAfter this concierge issued it.
    windows: BTreeMap<String, u128>,
    /// The greatest ledger height decided.
    cursor: u128,
}

impl Journal {
    fn open(path: &Path) -> Result<Self> {
        let mut journal = Journal { path: path.to_owned(), decided: BTreeSet::new(), windows: BTreeMap::new(), cursor: 0 };
        let Ok(text) = fs::read_to_string(path) else { return Ok(journal) };
        for (number_, line) in text.lines().enumerate() {
            let value: Value = serde_json::from_str(line)
                .map_err(|error| format!("journal line {}: {error}", number_ + 1))?;
            let decision = value.get("decision").and_then(Value::as_str).unwrap_or("");
            if decision == "deciding" {
                continue;
            }
            let key = string(&value, "key")?;
            if decision == "issued" {
                let subject = string(&value, "subject")?;
                let after = number(&value, "notAfter")?;
                let held = journal.windows.entry(subject).or_insert(0);
                *held = (*held).max(after);
            }
            if let Some(height) = key.strip_prefix("ledger:") {
                let height: u128 = height.parse().map_err(|_| "journal ledger key".to_owned())?;
                journal.cursor = journal.cursor.max(height);
            }
            journal.decided.insert(key);
        }
        Ok(journal)
    }

    fn append(&mut self, mut value: Value) -> Result<()> {
        value["at"] = json!(now());
        let mut line = serde_json::to_vec(&value).map_err(|e| e.to_string())?;
        line.push(b'\n');
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .map_err(|e| format!("{}: {e}", self.path.display()))?;
        file.write_all(&line).and_then(|_| file.sync_all()).map_err(|e| e.to_string())?;
        if let Some(decision) = value.get("decision").and_then(Value::as_str) {
            if decision != "deciding" {
                let key = string(&value, "key")?;
                if decision == "issued" {
                    let held = self.windows.entry(string(&value, "subject")?).or_insert(0);
                    *held = (*held).max(number(&value, "notAfter")?);
                }
                if let Some(height) = key.strip_prefix("ledger:") {
                    self.cursor = self.cursor.max(height.parse().unwrap_or(0));
                }
                self.decided.insert(key);
            }
        }
        Ok(())
    }
}

struct Runner<'a> {
    config: &'a Config,
}

impl Runner<'_> {
    /// Run the pinned client; stdout parsed as the LAST JSON value it printed.
    fn mini(&self, args: &[&str]) -> Result<(Value, String)> {
        let output = Command::new(&self.config.mini)
            .args(args)
            .output()
            .map_err(|e| format!("{}: {e}", self.config.mini.display()))?;
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        if !output.status.success() {
            let tail: Vec<&str> = stderr.lines().rev().take(3).collect();
            return Err(format!(
                "mini {} exited {}: {}",
                args.first().copied().unwrap_or(""),
                output.status.code().unwrap_or(-1),
                tail.into_iter().rev().collect::<Vec<_>>().join(" | ")
            ));
        }
        // The client prints pretty JSON documents and plain lines; the value
        // is the last document that starts at a line beginning with `{`.
        let mut starts: Vec<usize> = stdout.match_indices("\n{").map(|(at, _)| at + 1).collect();
        if stdout.starts_with('{') {
            starts.insert(0, 0);
        }
        let value = starts
            .iter()
            .rev()
            .find_map(|&at| serde_json::Deserializer::from_str(&stdout[at..]).into_iter::<Value>().next()?.ok())
            .unwrap_or(Value::Null);
        Ok((value, stdout))
    }

    fn dir(&self) -> String {
        self.config.workspace.display().to_string()
    }
}

/// The credit asset the Host pins (`asset` in the workspace's pinned config;
/// "0" when absent, as the fleet reads it).
fn credit_asset(workspace: &Path) -> Result<String> {
    let ws: Value = serde_json::from_slice(&fs::read(workspace.join("workspace.json")).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    let config = ws.get("config").and_then(Value::as_str).ok_or("workspace lacks config")?;
    let config: Value = serde_json::from_slice(&fs::read(config).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    Ok(config
        .get("asset")
        .and_then(|value| value.as_str().map(str::to_owned).or_else(|| value.as_u64().map(|n| n.to_string())))
        .unwrap_or_else(|| "0".into()))
}

/// One pass of the program. Returns the decisions it journaled.
pub(crate) fn step(config: &Config) -> Result<Vec<Value>> {
    let program: Program = serde_json::from_slice(&fs::read(&config.program).map_err(|e| format!("{}: {e}", config.program.display()))?)
        .map_err(|e| format!("program: {e}"))?;
    if program.kind != "minidregg-concierge-program-v1" {
        return Err("unknown concierge program version".into());
    }
    let run = Runner { config };
    let dir = run.dir();
    let inbox = config.inbox.display().to_string();
    let outbox = config.outbox.display().to_string();
    // The founder's grants (room, till) arrive as references; adopt them once.
    run.mini(&["credit", "--action", "adopt", "--dir", &dir, "--inbox", &inbox])?;
    let me: Value = serde_json::from_slice(&fs::read(config.workspace.join("workspace.json")).map_err(|e| e.to_string())?)
        .map_err(|e| e.to_string())?;
    if me.get("subject").and_then(Value::as_str) != Some(program.concierge.as_str()) {
        return Err("the program names another concierge subject than this workspace".into());
    }
    let mut journal = Journal::open(&config.journal)?;
    let (room, _) = run.mini(&["credit", "--action", "room", "--dir", &dir, "--room", &program.refs.room])?;
    if string(&room, "room")? != program.room {
        return Err("the room reference names another room than the program".into());
    }
    let tariff = room.get("tariff").cloned().unwrap_or(Value::Null);
    let week = number(&tariff, "week")?;
    let period = number(&tariff, "period")?;
    if string(&tariff, "till")? != program.till {
        return Err("the room's till field differs from the program's till".into());
    }
    let height = number(&room, "height")?;
    let asset = credit_asset(&config.workspace)?;
    let verbs = program.member_verbs.join(",");
    let mut decisions = Vec::new();

    // Paid renewals: the till's incoming ledger above the journal's cursor.
    let since = journal.cursor.to_string();
    let (ledger, _) = run.mini(&[
        "credit", "--action", "ledger", "--dir", &dir, "--account", &program.refs.till, "--topic", &program.topic,
        "--since", &since,
    ])?;
    let ledger_tip = number(&ledger, "tip")?;
    for raw in ledger.get("entries").and_then(Value::as_array).into_iter().flatten() {
        let entry = Entry {
            height: number(raw, "height")?,
            transaction: string(raw, "transactionId")?,
            subject: string(raw, "subject")?,
            payer: string(raw, "payer")?,
            asset: string(raw, "asset")?,
            amount: number(raw, "amount")?,
        };
        let key = format!("ledger:{}", entry.height);
        if journal.decided.contains(&key) {
            continue;
        }
        let basis = json!({"height":entry.height.to_string(),"transactionId":entry.transaction,
            "subject":entry.subject,"payer":entry.payer,"asset":entry.asset,
            "amount":entry.amount.to_string(),"payload":raw.get("payloadText"),
            "ledgerTip":ledger_tip.to_string()});
        let decision = decide(&entry, &asset, week, period, journal.windows.get(&entry.subject).copied());
        let line = match decision {
            Decision::Underpaid { week } => json!({"key":key,"decision":"underpaid","entry":basis,
                "week":week.to_string(),"subject":entry.subject}),
            Decision::WrongAsset { asset: paid } => json!({"key":key,"decision":"wrong-asset","entry":basis,
                "creditAsset":asset,"paidAsset":paid,"subject":entry.subject}),
            Decision::Issue { not_after } => {
                let id = format!("renew-h{}", entry.height);
                journal.append(json!({"key":key,"decision":"deciding","entry":basis,"subject":entry.subject,
                    "notAfter":not_after.to_string(),"proposal":id}))?;
                match issue(&run, &dir, &program, &entry.subject, not_after, &id, &verbs, &outbox) {
                    Ok(window) => json!({"key":key,"decision":"issued","entry":basis,"subject":entry.subject,
                        "notAfter":not_after.to_string(),"period":period.to_string(),"week":week.to_string(),
                        "proposal":id,"window":window}),
                    Err(error) => {
                        // Not final: the next pass re-runs the same proposal
                        // id, which looks the attempt up instead of resending.
                        journal.append(json!({"key":key,"decision":"deciding","error":error,"proposal":id}))?;
                        return Err(format!("issuing {id}: {error}"));
                    }
                }
            }
        };
        journal.append(line.clone())?;
        decisions.push(line);
    }

    // A free room: filed requests from standing members.
    if week == 0 {
        let mut requests = Vec::new();
        if let Ok(entries) = fs::read_dir(&config.inbox) {
            for entry in entries.flatten() {
                let path = entry.path();
                let name = entry.file_name().to_string_lossy().into_owned();
                if !name.starts_with("request-") || !name.ends_with(".json") {
                    continue;
                }
                let Ok(value) = serde_json::from_slice::<Value>(&fs::read(&path).unwrap_or_default()) else { continue };
                if value.get("type").and_then(Value::as_str) == Some("minidregg-room-request-v1")
                    && value.get("room").and_then(Value::as_str) == Some(program.room.as_str())
                {
                    requests.push((name, value));
                }
            }
        }
        requests.sort_by(|a, b| a.0.cmp(&b.0));
        let mut members: Option<BTreeSet<String>> = None;
        for (name, request) in requests {
            let key = format!("request:{name}");
            if journal.decided.contains(&key) {
                continue;
            }
            let subject = string(&request, "subject")?;
            if members.is_none() {
                let (who, _) = run.mini(&["workspace", "--action", "who", "--dir", &dir, "--name", &program.refs.room])?;
                members = Some(
                    who.get("members")
                        .and_then(Value::as_array)
                        .into_iter()
                        .flatten()
                        .filter_map(|m| m.get("subject").and_then(Value::as_str).map(str::to_owned))
                        .collect(),
                );
            }
            let standing = members.as_ref().is_some_and(|set| set.contains(&subject));
            let line = if !standing {
                json!({"key":key,"decision":"not-a-member","request":request,"subject":subject,
                    "basis":"the Host's who view of the room at height ".to_owned() + &height.to_string()})
            } else {
                let current = journal.windows.get(&subject).copied();
                if current.is_some_and(|after| after >= height) {
                    json!({"key":key,"decision":"already-a-member","request":request,"subject":subject,
                        "notAfter":current.map(|a| a.to_string())})
                } else {
                    let not_after = height + period;
                    let id = format!("free-{}-h{height}", &subject[subject.len().saturating_sub(12)..]);
                    journal.append(json!({"key":key,"decision":"deciding","request":request,"subject":subject,
                        "notAfter":not_after.to_string(),"proposal":id}))?;
                    let window = issue(&run, &dir, &program, &subject, not_after, &id, &verbs, &outbox)
                        .map_err(|error| format!("issuing {id}: {error}"))?;
                    json!({"key":key,"decision":"issued","request":request,"subject":subject,
                        "notAfter":not_after.to_string(),"period":period.to_string(),"week":"0",
                        "proposal":id,"window":window,
                        "basis":"free room: a standing member in the Host's who view at height ".to_owned() + &height.to_string()})
                }
            };
            journal.append(line.clone())?;
            decisions.push(line);
        }
    }
    Ok(decisions)
}

#[allow(clippy::too_many_arguments)]
fn issue(
    run: &Runner<'_>,
    dir: &str,
    program: &Program,
    subject: &str,
    not_after: u128,
    id: &str,
    verbs: &str,
    outbox: &str,
) -> Result<Value> {
    let not_after = not_after.to_string();
    let _ = verbs; // the client issues `credit::MEMBER_VERBS`; the program records them
    run.mini(&[
        "credit", "--action", "renew", "--dir", dir, "--room", &program.refs.room, "--subject", subject,
        "--not-after", &not_after, "--proposal-id", id, "--outbox", outbox,
    ])?;
    let record = Path::new(dir).join("proposals").join(id).join("window.json");
    let window: Value = serde_json::from_slice(&fs::read(&record).map_err(|e| format!("{}: {e}", record.display()))?)
        .map_err(|e| e.to_string())?;
    if window.get("type").and_then(Value::as_str) != Some("minidregg-room-window-v1")
        || window.get("notAfter").and_then(Value::as_str) != Some(not_after.as_str())
        || window.get("subject").and_then(Value::as_str) != Some(subject)
    {
        return Err("the client's window record differs from the decision".into());
    }
    Ok(json!({"capability":window["capability"],"receipt":window["receipt"],
        "reference":window["reference"],"delivered":window["delivered"]}))
}

pub(crate) fn load(path: &Path) -> Result<Config> {
    let bytes = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let value: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if value.get("type").and_then(Value::as_str) != Some("minidregg-concierge-controller-v1") {
        return Err("concierge config type must be minidregg-concierge-controller-v1".into());
    }
    let mut value = value;
    value.as_object_mut().map(|object| object.remove("type"));
    serde_json::from_value(value).map_err(|e| format!("concierge config: {e}"))
}

/// `grain-runtime concierge step CONFIG` (one pass, decisions printed) or
/// `grain-runtime concierge serve CONFIG [SECONDS]` (a pass every SECONDS,
/// default 5; a failed pass is logged and retried).
pub(crate) fn main(args: &[std::ffi::OsString]) -> Result<()> {
    let mode = args.first().and_then(|a| a.to_str()).ok_or("concierge step|serve CONFIG [SECONDS]")?;
    let config = load(Path::new(args.get(1).ok_or("concierge needs CONFIG")?))?;
    match mode {
        "step" => {
            let decisions = step(&config)?;
            println!("{}", serde_json::to_string_pretty(&json!({"type":"minidregg-concierge-pass-v1",
                "decisions":decisions})).map_err(|e| e.to_string())?);
            Ok(())
        }
        "serve" => {
            let seconds: u64 = match args.get(2) {
                Some(value) => value.to_str().and_then(|v| v.parse().ok()).ok_or("SECONDS must be a number")?,
                None => 5,
            };
            loop {
                match step(&config) {
                    Ok(decisions) => {
                        for decision in decisions {
                            println!("{decision}");
                        }
                    }
                    Err(error) => eprintln!("concierge pass: {error}"),
                }
                std::thread::sleep(Duration::from_secs(seconds));
            }
        }
        _ => Err("concierge mode is step or serve".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(height: u128, amount: u128) -> Entry {
        Entry { height, transaction: "9".into(), subject: "77".into(), payer: "5".into(), asset: "0".into(), amount }
    }

    #[test]
    fn a_week_is_issued_from_the_paying_height() {
        assert_eq!(decide(&entry(40, 100), "0", 100, 12, None), Decision::Issue { not_after: 52 });
    }

    #[test]
    fn a_renewal_after_expiry_starts_again_from_its_height() {
        assert_eq!(decide(&entry(70, 100), "0", 100, 12, Some(52)), Decision::Issue { not_after: 82 });
    }

    #[test]
    fn an_early_renewal_extends_the_window() {
        assert_eq!(decide(&entry(45, 100), "0", 100, 12, Some(52)), Decision::Issue { not_after: 64 });
    }

    #[test]
    fn an_underpayment_issues_nothing() {
        assert_eq!(decide(&entry(40, 99), "0", 100, 12, None), Decision::Underpaid { week: 100 });
    }

    #[test]
    fn another_asset_is_not_credit() {
        let mut paid = entry(40, 1000);
        paid.asset = "3".into();
        assert_eq!(decide(&paid, "0", 100, 12, None), Decision::WrongAsset { asset: "3".into() });
    }

    #[test]
    fn the_journal_restores_windows_and_cursor() {
        let dir = std::env::temp_dir().join(format!("concierge-journal-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let path = dir.join("journal.jsonl");
        let mut journal = Journal::open(&path).unwrap();
        journal.append(json!({"key":"ledger:40","decision":"deciding","subject":"77","notAfter":"52"})).unwrap();
        journal.append(json!({"key":"ledger:40","decision":"issued","subject":"77","notAfter":"52"})).unwrap();
        journal.append(json!({"key":"ledger:44","decision":"underpaid","subject":"78"})).unwrap();
        journal.append(json!({"key":"ledger:50","decision":"deciding","subject":"79","notAfter":"62"})).unwrap();
        let reopened = Journal::open(&path).unwrap();
        assert_eq!(reopened.cursor, 44);
        assert_eq!(reopened.windows.get("77"), Some(&52));
        assert!(reopened.decided.contains("ledger:44"));
        // an undecided issue is re-run on restart, not skipped
        assert!(!reopened.decided.contains("ledger:50"));
        fs::remove_dir_all(&dir).unwrap();
    }
}
