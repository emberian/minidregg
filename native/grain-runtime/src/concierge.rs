//! The room CONCIERGE (docs/PLACE.md §2.10, §5 item 6): a deterministic program the
//! controller binary runs as a runner holding `delegate` under a room R.
//!
//! Program: read the till's incoming ledger (Host op 180: fleet turns that
//! paid `A_R`, topic `renew`). Each payment's memo (`credit::renew_memo`,
//! signed with it) names the room, the week price the payer read and the
//! height `H` it read it at. The decision reads R's tariff AT `H` (a signed
//! `at` read), never the current one, so it does not depend on when this pass
//! runs. A payment is honoured when the asset is the pinned credit asset, it
//! landed within `PRICE_SLACK` heights of `H`, the quoted price is the tariff's
//! `week` at `H`, the amount covers it, and the signer is a subject the room
//! admits (a standing grant under R in the Host's signed `who` view, or
//! `open = 1` at `H`): delegate `member` under R to the signer with
//! `notAfter = max(entry.height, that subject's current notAfter) + period`
//! (period at `H`; a re-issue extends). Any other payment is REFUNDED from the
//! till to the payer (topic `refund`), journaled with its reason: the till
//! never keeps a payment it did not honour. A kicked subject holds no standing
//! grant (`room kick` revokes every one), so its payment is refunded. When
//! `week = 0` the room is free: each filed request from a subject the Host
//! lists as a standing member of R issues `height + period`.
//!
//! Like M5's tools, every act is the pinned `mini` client run against the
//! concierge's own workspace: signed reads, proposals, submissions, exact
//! lookups. The concierge decides nothing the Host does not re-check: the
//! window is enforced by the kernel (`Admissible.validUntil`), and the
//! delegation is admitted only under the founder's grant to the concierge.
//! What the kernel does not yet check is that each delegation followed a
//! payment (K-BOOK-SLOTS, docs/PLACE.md §4.8); until then the concierge answers for
//! that with its JOURNAL: one line per decision naming the ledger entry
//! (height, transaction, payer, signer, amount) it acted on. Every decision
//! is keyed on the entry's ledger `transactionId` (`ledger-tx:T`); the
//! proposal id (`renew-t` and a digest of T), the refund memo and the refund's operation
//! record all derive from it, never from the height.
//!
//! Restart: the journal is re-read; a decision whose delegation was not
//! recorded is re-run under the same proposal id, which the client resolves
//! by exact lookup (never a second send). A refund is a recorded operation
//! (`credit --action refund --operation-record`): once begun it is resolved
//! only by `credit --action lookup-operation` on that record. Confirmed is
//! `refunded`; a Host refusal is a final `refund-failed`; typed contention, or
//! no submit marker once the sending child was reaped, starts a new record
//! generation; anything else stays `refund-undecided` and is looked up again
//! on the next pass. A pass that died while its refund child ran is re-driven
//! on the next tick: every pass holds `JOURNAL.lock` and each child inherits
//! it, so taking the lock proves the old pass and its children exited, and
//! the begun generation's record is looked up (no submit marker: a new
//! generation is sent; a crash after submit is found by the lookup, never paid
//! twice). After eight generations a refund is named `refund-stalled` and the
//! payment stays in the till. A journal written under the old `ledger:HEIGHT` key is
//! refused at load (re-genesis; no migration).
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
    /// The room's chat roster, kept by the founder (operator custody: the
    /// founder's workspace on the same account). With it, each subject this
    /// concierge issues a window gets a stream and a roster row (`chat invite
    /// ROOM SUBJECT --roster-only`: no grant, the window is the grant), and the
    /// window's reference is left in `memberHomes/SUBJECT/requests/ROOM-invite.json`
    /// when that home exists; the member joins with `chat join ROOM @ROOM-invite.json`.
    #[serde(default)]
    pub roster: Option<RosterConfig>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct RosterConfig {
    /// The room's name in the founder's workspace.
    pub room: String,
    pub host: PathBuf,
    pub config: PathBuf,
    pub socket: PathBuf,
    pub workspace: PathBuf,
    pub home: PathBuf,
    #[serde(default)]
    pub member_homes: Option<PathBuf>,
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

/// How many heights a payment may land after the height its price was read
/// at: the same honest authoring-to-admission gap a birth's `birthSlack`
/// tolerates (64 admissions; the deployed clock ticks once a minute).
pub(crate) const PRICE_SLACK: u128 = 64;

/// What a payment's signed memo quotes: `room R week W at H`.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Quote {
    pub room: String,
    pub week: u128,
    pub at: u128,
}

pub(crate) fn parse_quote(payload: Option<&str>) -> Option<Quote> {
    let words: Vec<&str> = payload?.split_whitespace().collect();
    match words.as_slice() {
        ["room", room, "week", week, "at", at] => Some(Quote {
            room: (*room).to_owned(),
            week: week.parse().ok()?,
            at: at.parse().ok()?,
        }),
        _ => None,
    }
}

/// The tariff as it stood at the quoted height.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Priced {
    pub week: u128,
    pub period: u128,
    pub open: bool,
}

#[derive(Debug, PartialEq)]
pub(crate) enum Decision {
    Issue { not_after: u128, period: u128, week: u128 },
    Refund { reason: &'static str },
}

/// Whether a payment's quote can be priced at all: it names this room and
/// landed within `PRICE_SLACK` heights after the height it quotes.
pub(crate) fn quote_in_window(entry: &Entry, room: &str, quote: Option<&Quote>) -> Option<&'static str> {
    let Some(quote) = quote else { return Some("unquoted") };
    if quote.room != room {
        return Some("unquoted");
    }
    if quote.at > entry.height || entry.height - quote.at > PRICE_SLACK {
        return Some("stale-quote");
    }
    None
}

/// The program's rule for one paid entry. Pure: the journal and the Host
/// supply every input; `priced` is the tariff AT the quoted height, so the
/// rule's answer is the same whenever the pass runs.
pub(crate) fn decide(
    entry: &Entry,
    credit_asset: &str,
    room: &str,
    quote: Option<&Quote>,
    priced: Option<&Priced>,
    admitted: bool,
    current: Option<u128>,
) -> Decision {
    if entry.asset != credit_asset {
        return Decision::Refund { reason: "wrong-asset" };
    }
    if let Some(reason) = quote_in_window(entry, room, quote) {
        return Decision::Refund { reason };
    }
    let (Some(quote), Some(priced)) = (quote, priced) else {
        return Decision::Refund { reason: "no-tariff-at-height" };
    };
    if priced.week == 0 {
        return Decision::Refund { reason: "free-room" };
    }
    if quote.week != priced.week {
        return Decision::Refund { reason: "quote-differs" };
    }
    if entry.amount < priced.week {
        return Decision::Refund { reason: "underpaid" };
    }
    if !admitted && !priced.open {
        return Decision::Refund { reason: "not-admitted" };
    }
    let from = current.map_or(entry.height, |after| after.max(entry.height));
    Decision::Issue { not_after: from + priced.period, period: priced.period, week: priced.week }
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

/// The ledger key of one payment: the transaction the Lean ledger names
/// (`FleetIncomingEntry.transactionId`, Kernel/NativeHost.lean). One accepted
/// record yields at most one entry, so the transaction is the payment's
/// identity; proposal ids, refund memos and operation records derive from it.
pub(crate) fn ledger_key(transaction: &str) -> String {
    format!("ledger-tx:{transaction}")
}

/// A refund begun and not yet decided: replayed from the journal on restart
/// and resolved only by exact lookup of its operation record.
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Refunding {
    pub generation: u64,
    pub height: u128,
    pub refund: Value,
    pub reason: String,
    pub entry: Value,
    pub subject: String,
    /// The `credit refund` child of this generation was reaped (it returned,
    /// failed or was killed): an absent submit marker then proves no send.
    pub submitter_stopped: bool,
}

/// The journal: decisions keyed by the input they acted on.
struct Journal {
    path: PathBuf,
    /// Keys (`ledger-tx:TRANSACTION`, `request:FILE`) with a final decision.
    decided: BTreeSet<String>,
    /// Subject → greatest notAfter this concierge issued it.
    windows: BTreeMap<String, u128>,
    /// Ledger keys whose refund was begun and not decided.
    refunding: BTreeMap<String, Refunding>,
    /// Ledger keys begun (any decision kind) and not decided, with heights:
    /// the cursor never passes one of them.
    open: BTreeMap<String, u128>,
    /// The greatest ledger height decided.
    decided_height: u128,
    /// Subjects given a stream and a roster row (`roster:SUBJECT`).
    rostered: BTreeSet<String>,
}

impl Journal {
    fn open(path: &Path) -> Result<Self> {
        let mut journal = Journal {
            path: path.to_owned(),
            decided: BTreeSet::new(),
            windows: BTreeMap::new(),
            refunding: BTreeMap::new(),
            open: BTreeMap::new(),
            decided_height: 0,
            rostered: BTreeSet::new(),
        };
        let Ok(text) = fs::read_to_string(path) else { return Ok(journal) };
        for (number_, line) in text.lines().enumerate() {
            let value: Value = serde_json::from_str(line)
                .map_err(|error| format!("journal line {}: {error}", number_ + 1))?;
            journal.apply(&value).map_err(|error| format!("journal line {}: {error}", number_ + 1))?;
        }
        Ok(journal)
    }

    /// The cursor the next ledger read starts above: the greatest decided
    /// height, but never at or past a begun-and-undecided entry.
    fn cursor(&self) -> u128 {
        let floor = self.open.values().min().map(|h| h.saturating_sub(1));
        floor.map_or(self.decided_height, |f| f.min(self.decided_height))
    }

    fn apply(&mut self, value: &Value) -> Result<()> {
        let key = string(value, "key")?;
        if key.starts_with("ledger:") {
            return Err(format!(
                "{key}: this journal was written under the height key (ledger:HEIGHT); \
                 the concierge now keys payments on the ledger transactionId. Start a fresh \
                 journal at a re-genesis; it is not migrated"));
        }
        let decision = value.get("decision").and_then(Value::as_str).unwrap_or("");
        let height = value.get("height").and_then(Value::as_str).map(str::parse::<u128>).transpose()
            .map_err(|_| "journal height is not a decimal".to_owned())?;
        match decision {
            "deciding" => {
                if let Some(height) = height { self.open.insert(key.clone(), height); }
                if let Some(refund) = value.get("refund") {
                    self.refunding.insert(key.clone(), Refunding {
                        generation: value.get("generation").and_then(Value::as_u64).ok_or("refund generation absent")?,
                        height: height.ok_or("refund height absent")?,
                        refund: refund.clone(),
                        reason: string(value, "reason")?,
                        entry: value.get("entry").cloned().unwrap_or(Value::Null),
                        subject: string(value, "subject")?,
                        submitter_stopped: false,
                    });
                }
            }
            "refund-submitter-stopped" => {
                let generation = value.get("generation").and_then(Value::as_u64).ok_or("generation absent")?;
                if let Some(open) = self.refunding.get_mut(&key) {
                    if open.generation == generation { open.submitter_stopped = true; }
                }
            }
            // Not final: the refund stays open and the next pass looks it up.
            "refund-undecided" => {}
            _ => {
                if decision == "issued" {
                    let held = self.windows.entry(string(value, "subject")?).or_insert(0);
                    *held = (*held).max(number(value, "notAfter")?);
                }
                if decision == "rostered" {
                    self.rostered.insert(string(value, "subject")?);
                }
                if key.starts_with("ledger-tx:") {
                    let height = height.ok_or("decided ledger line has no height")?;
                    self.decided_height = self.decided_height.max(height);
                }
                self.refunding.remove(&key);
                self.open.remove(&key);
                self.decided.insert(key);
            }
        }
        Ok(())
    }

    fn append(&mut self, mut value: Value) -> Result<()> {
        self.apply(&value)?;
        value["at"] = json!(now());
        let mut line = serde_json::to_vec(&value).map_err(|e| e.to_string())?;
        line.push(b'\n');
        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.path)
            .map_err(|e| format!("{}: {e}", self.path.display()))?;
        file.write_all(&line).map_err(|e| e.to_string())?;
        Ok(())
    }
}

struct Runner<'a> {
    config: &'a Config,
    /// The pass lock's descriptor, inherited by every child: the lock stays
    /// held until the pass AND every client it started have exited.
    lock: Option<std::os::unix::io::RawFd>,
}

/// One concierge pass at a time, held across its children. `flock` belongs
/// to the open file description, which each `mini` child inherits (its
/// close-on-exec flag is cleared for it), so a later pass that takes the lock
/// knows the previous pass and every refund child it started have exited:
/// a begun refund whose submitter was never seen to stop is then proven
/// stopped, and exact lookup of its record decides it.
pub(crate) struct PassLock(fs::File);

pub(crate) fn lock_pass(config: &Config) -> Result<PassLock> {
    use std::os::unix::fs::OpenOptionsExt;
    use std::os::unix::io::AsRawFd;
    let path = config.journal.with_extension("lock");
    let file = OpenOptions::new().create(true).truncate(false).write(true).mode(0o600).open(&path)
        .map_err(|e| format!("{}: {e}", path.display()))?;
    if unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0 {
        return Err(format!(
            "{} is held: a previous concierge pass or a refund child it started is still running; the next tick retries",
            path.display()));
    }
    Ok(PassLock(file))
}

impl PassLock {
    fn fd(&self) -> std::os::unix::io::RawFd {
        use std::os::unix::io::AsRawFd;
        self.0.as_raw_fd()
    }
}

/// The child keeps the pass lock: clear close-on-exec on its descriptor.
fn inherit_lock(command: &mut Command, fd: std::os::unix::io::RawFd) {
    use std::os::unix::process::CommandExt;
    unsafe {
        command.pre_exec(move || {
            if libc::fcntl(fd, libc::F_SETFD, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
}

/// Holding the pass lock proves every earlier submitter exited: mark each
/// begun refund generation whose stop was never journaled.
fn prove_previous_submitters_stopped(journal: &mut Journal, _lock: &PassLock) -> Result<()> {
    let unproven: Vec<(String, u64)> = journal.refunding.iter()
        .filter(|(_, open)| !open.submitter_stopped)
        .map(|(key, open)| (key.clone(), open.generation)).collect();
    for (key, generation) in unproven {
        journal.append(json!({"key":key,"decision":"refund-submitter-stopped","generation":generation,
            "basis":"pass lock taken: the previous pass and every child holding its lock have exited"}))?;
    }
    Ok(())
}

impl Runner<'_> {
    /// Run the pinned client; stdout parsed as the LAST JSON value it printed.
    fn mini(&self, args: &[&str]) -> Result<(Value, String)> {
        let mut command = Command::new(&self.config.mini);
        command.args(args);
        if let Some(fd) = self.lock {
            inherit_lock(&mut command, fd);
        }
        let output = crate::deadline::output(&mut command, crate::deadline::NATIVE_CALL)
            .map_err(|e| crate::deadline::describe(&self.config.mini.display().to_string(), e))?;
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
    let lock = lock_pass(config)?;
    let run = Runner { config, lock: Some(lock.fd()) };
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
    prove_previous_submitters_stopped(&mut journal, &lock)?;
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
    // The subjects the room admits now: a standing grant under R in the Host's
    // signed `who` view (a kicked subject holds none).
    let mut members: Option<BTreeSet<String>> = None;
    let height = number(&room, "height")?;
    let asset = credit_asset(&config.workspace)?;
    let verbs = program.member_verbs.join(",");
    let mut decisions = Vec::new();

    // Paid renewals: the till's incoming ledger above the journal's cursor.
    let since = journal.cursor().to_string();
    let (ledger, _) = run.mini(&[
        "credit", "--action", "ledger", "--dir", &dir, "--account", &program.refs.till, "--topic", &program.topic,
        "--since", &since,
    ])?;
    let ledger_tip = number(&ledger, "tip")?;
    let records = refund_records(config)?;
    for raw in ledger.get("entries").and_then(Value::as_array).into_iter().flatten() {
        let entry = Entry {
            height: number(raw, "height")?,
            transaction: string(raw, "transactionId")?,
            subject: string(raw, "subject")?,
            payer: string(raw, "payer")?,
            asset: string(raw, "asset")?,
            amount: number(raw, "amount")?,
        };
        if entry.transaction.is_empty() || !entry.transaction.bytes().all(|b| b.is_ascii_digit()) {
            return Err("ledger transactionId is not a decimal".into());
        }
        let key = ledger_key(&entry.transaction);
        if journal.decided.contains(&key) {
            continue;
        }
        let height = entry.height.to_string();
        // A refund begun before (this pass or a previous process) is resolved
        // only by exact lookup of its operation record; it is never re-decided
        // and never re-sent under a fresh nonce.
        if let Some(open) = journal.refunding.get(&key).cloned() {
            let line = drive_refund(&run, &dir, &program, &records, &mut journal, &key, open)?;
            decisions.push(line);
            continue;
        }
        let basis = json!({"height":height,"transactionId":entry.transaction,
            "subject":entry.subject,"payer":entry.payer,"asset":entry.asset,
            "amount":entry.amount.to_string(),"payload":raw.get("payloadText"),
            "ledgerTip":ledger_tip.to_string()});
        let quote = parse_quote(raw.get("payloadText").and_then(Value::as_str));
        let priced = match (&quote, quote_in_window(&entry, &program.room, quote.as_ref())) {
            (Some(quote), None) => {
                let at = quote.at.to_string();
                let (then, _) = run.mini(&["credit", "--action", "room", "--dir", &dir, "--room", &program.refs.room, "--at", &at])?;
                let then = then.get("tariff").cloned().unwrap_or(Value::Null);
                Some(Priced {
                    week: number(&then, "week").unwrap_or(0),
                    period: number(&then, "period").unwrap_or(period),
                    open: then.get("open").and_then(Value::as_str) == Some("1"),
                })
            }
            _ => None,
        };
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
        let admitted = members.as_ref().is_some_and(|set| set.contains(&entry.subject));
        let decision = decide(&entry, &asset, &program.room, quote.as_ref(), priced.as_ref(), admitted,
            journal.windows.get(&entry.subject).copied());
        let line = match decision {
            Decision::Refund { reason } => {
                let memo = refund_memo(&program.room, &entry.transaction, reason);
                let refund = json!({"to":entry.payer,"amount":entry.amount.to_string(),"asset":entry.asset,"memo":memo,
                    "quote":quote.as_ref().map(|q| json!({"room":q.room,"week":q.week.to_string(),"at":q.at.to_string()})),
                    "tariffAtQuote":priced.as_ref().map(|p| json!({"week":p.week.to_string(),"period":p.period.to_string(),"open":p.open})),
                    "admitted":admitted});
                journal.append(json!({"key":key,"decision":"deciding","height":height,"entry":basis,
                    "subject":entry.subject,"reason":reason,"refund":refund,"generation":0}))?;
                let open = journal.refunding.get(&key).cloned().ok_or("refund was not journaled as begun")?;
                decisions.push(drive_refund(&run, &dir, &program, &records, &mut journal, &key, open)?);
                continue;
            }
            Decision::Issue { not_after, period, week } => {
                let id = renew_id(&entry.transaction)?;
                journal.append(json!({"key":key,"decision":"deciding","height":height,"entry":basis,"subject":entry.subject,
                    "notAfter":not_after.to_string(),"proposal":id}))?;
                match issue(&run, &dir, &program, &entry.subject, not_after, &id, &verbs, &outbox) {
                    Ok(window) => json!({"key":key,"decision":"issued","height":height,"entry":basis,"subject":entry.subject,
                        "notAfter":not_after.to_string(),"period":period.to_string(),"week":week.to_string(),
                        "priceReadAt":quote.as_ref().map(|q| q.at.to_string()),
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
    if let Some(roster) = &config.roster {
        // After the decisions: a failed roster write never blocks a payment's
        // decision; the next pass retries it (the write is idempotent).
        let pending: Vec<String> = journal.windows.keys().filter(|s| !journal.rostered.contains(*s)).cloned().collect();
        for subject in pending {
            let line = format!("chat invite {} {subject} --roster-only", roster.room);
            match run.mini(&[
                "shell", "--socket", &roster.socket.display().to_string(), "--host", &roster.host.display().to_string(),
                "--config", &roster.config.display().to_string(), "--workspace", &roster.workspace.display().to_string(),
                "--home", &roster.home.display().to_string(), "--line", &line,
            ]) {
                Ok(_) => {
                    let decided = json!({"key":format!("roster:{subject}"),"decision":"rostered","subject":subject});
                    journal.append(decided.clone())?;
                    decisions.push(decided);
                }
                Err(error) => decisions.push(json!({"key":format!("roster:{subject}"),"decision":"roster-pending","subject":subject,"error":error})),
            }
        }
        if let Some(homes) = &roster.member_homes {
            for subject in journal.windows.keys() {
                deliver_window(&config.outbox, homes, &roster.room, subject)?;
            }
        }
    }
    Ok(decisions)
}

/// The newest window reference this concierge left for `subject`, copied to
/// `homes/SUBJECT/requests/ROOM-invite.json` when that home exists.
fn deliver_window(outbox: &Path, homes: &Path, room: &str, subject: &str) -> Result<()> {
    let home = homes.join(subject);
    if !home.is_dir() {
        return Ok(());
    }
    let Ok(entries) = fs::read_dir(outbox.join(subject)) else { return Ok(()) };
    let newest = entries
        .filter_map(|e| e.ok())
        .filter(|e| e.file_name().to_str().is_some_and(|n| n.starts_with("renew-t") && n.ends_with(".json")))
        .filter_map(|e| Some((e.metadata().ok()?.modified().ok()?, e.path())))
        .max();
    let Some((_, source)) = newest else { return Ok(()) };
    let bytes = fs::read(&source).map_err(|e| format!("{}: {e}", source.display()))?;
    let requests = home.join("requests");
    fs::create_dir_all(&requests).map_err(|e| format!("{}: {e}", requests.display()))?;
    let target = requests.join(format!("{room}-invite.json"));
    if fs::read(&target).ok().as_deref() == Some(bytes.as_slice()) {
        return Ok(());
    }
    let staged = requests.join(format!(".{room}-invite.json.tmp"));
    {
        use std::os::unix::fs::OpenOptionsExt;
        let mut file = OpenOptions::new().write(true).create(true).truncate(true).mode(0o600).open(&staged)
            .map_err(|e| format!("{}: {e}", staged.display()))?;
        file.write_all(&bytes).map_err(|e| e.to_string())?;
    }
    fs::rename(&staged, &target).map_err(|e| format!("{}: {e}", target.display()))
}

/// The refund memo: names the room, the payment's ledger transaction and the
/// reason, so two refunds never share a memo.
pub(crate) fn refund_memo(room: &str, transaction: &str, reason: &str) -> String {
    format!("refund room {room} ledger-tx:{transaction} {reason}")
}

/// The private directory holding refund operation records (beside the journal).
fn refund_records(config: &Config) -> Result<PathBuf> {
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
    let parent = config.journal.parent().ok_or("concierge journal has no parent directory")?;
    let dir = parent.join("refund-operations");
    match fs::DirBuilder::new().mode(0o700).create(&dir) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {}
        Err(error) => return Err(format!("{}: {error}", dir.display())),
    }
    let meta = fs::symlink_metadata(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
    if !meta.is_dir() || meta.permissions().mode() & 0o077 != 0 {
        return Err(format!("{} must be a private directory", dir.display()));
    }
    Ok(dir)
}

/// The operation record of one refund generation. A generation is replaced
/// only after its record is decided with no effect (typed contention, or no
/// submit marker once its submitter was reaped).
pub(crate) fn refund_record(records: &Path, transaction: &str, generation: u64) -> PathBuf {
    records.join(format!("{transaction}-g{generation}.json"))
}

/// What exact lookup of a refund's operation record decided.
#[derive(Debug, PartialEq)]
pub(crate) enum RefundLookup {
    /// The refund is admitted: the payer is repaid.
    Confirmed(Value),
    /// The Host refused this refund (not contention): final, named.
    Refused(Value),
    /// Decided with no effect; a NEW generation may be sent.
    NoEffect(&'static str),
    /// Nothing decided: the record stays, the next pass looks it up again.
    Undecided(String),
}

/// Classify `mini credit --action lookup-operation` output (the client's
/// `minidregg-operation-recovery-v1`). Pure.
pub(crate) fn classify_refund(recovery: &Value, submitter_stopped: bool) -> RefundLookup {
    match recovery.get("status").and_then(Value::as_str) {
        Some("confirmed") => RefundLookup::Confirmed(recovery.clone()),
        Some("refused") if recovery["outcome"]["type"] == "contention" => RefundLookup::NoEffect("contention"),
        Some("refused") => RefundLookup::Refused(recovery.clone()),
        Some("not-submitted") if submitter_stopped => RefundLookup::NoEffect("not-submitted"),
        Some("not-submitted") => RefundLookup::Undecided(
            "no submit marker, but the previous submitter was not proven stopped".into()),
        Some(other) => RefundLookup::Undecided(format!("lookup status {other}")),
        None => RefundLookup::Undecided("lookup returned no status".into()),
    }
}

/// How many fresh generations one pass may send after decided no-effect
/// outcomes (contention) before it leaves the refund open for the next pass.
const REFUND_GENERATIONS_PER_PASS: u64 = 3;
/// How many generations a refund gets in all before the concierge stops
/// driving it and names it `refund-stalled` (the payment stays in the till).
const REFUND_GENERATIONS_MAX: u64 = 8;

/// Drive one begun refund to a decision. Each generation is sent at most
/// once under its own operation record; after any send the child is reaped
/// and the record is looked up, never re-sent. Returns the final journal
/// line, or an error (journaled `refund-undecided`) that stops the pass.
fn drive_refund(
    run: &Runner<'_>,
    dir: &str,
    program: &Program,
    records: &Path,
    journal: &mut Journal,
    key: &str,
    mut open: Refunding,
) -> Result<Value> {
    let transaction = key.strip_prefix("ledger-tx:").ok_or("refund key is not a ledger transaction")?.to_owned();
    let height = open.height.to_string();
    let mut sent_this_pass = 0u64;
    loop {
        let record = refund_record(records, &transaction, open.generation);
        let record_text = record.display().to_string();
        if !record.exists() && open.generation >= REFUND_GENERATIONS_MAX {
            let line = json!({"key":key,"decision":"refund-stalled","height":height,"reason":open.reason,
                "entry":open.entry,"subject":open.subject,"refund":open.refund,"generation":open.generation,
                "notice":format!("the refund of {} to {} was not admitted in {REFUND_GENERATIONS_MAX} generations; the payment stays in the till for the operator",
                    open.refund.get("amount").and_then(Value::as_str).unwrap_or("?"), open.refund.get("to").and_then(Value::as_str).unwrap_or("?"))});
            journal.append(line.clone())?;
            return Ok(line);
        }
        if !record.exists() {
            if sent_this_pass >= REFUND_GENERATIONS_PER_PASS {
                return Err(format!("refund {key}: {sent_this_pass} generations decided without effect this pass; retried next pass"));
            }
            sent_this_pass += 1;
            let refund = &open.refund;
            let field = |name: &str| refund.get(name).and_then(Value::as_str).map(str::to_owned)
                .ok_or_else(|| format!("journaled refund lacks {name}"));
            let (to, amount, asset, memo) = (field("to")?, field("amount")?, field("asset")?, field("memo")?);
            let sent = run.mini(&["credit", "--action", "refund", "--dir", dir, "--account", &program.refs.till,
                "--to", &to, "--amount", &amount, "--asset", &asset, "--memo", &memo,
                "--operation-record", &record_text]);
            // The child has returned (or was reaped): the submitter is stopped.
            journal.append(json!({"key":key,"decision":"refund-submitter-stopped","generation":open.generation}))?;
            open.submitter_stopped = true;
            if let Ok((done, _)) = &sent {
                if let Some(transaction_id) = done.get("transaction").filter(|t| t.is_string()) {
                    let line = refunded(key, &height, &open, json!({"transaction":transaction_id,"result":done}));
                    journal.append(line.clone())?;
                    return Ok(line);
                }
            }
        }
        if !record.exists() {
            // The client refused before creating a record (malformed request,
            // missing reference): nothing was signed. Not final.
            journal.append(json!({"key":key,"decision":"refund-undecided","generation":open.generation,
                "error":"the refund left no operation record"}))?;
            return Err(format!("refund {key}: the client created no operation record"));
        }
        let lookup = run.mini(&["credit", "--action", "lookup-operation", "--dir", dir, "--operation-record", &record_text]);
        let decided = match lookup {
            Ok((recovery, _)) => classify_refund(&recovery, open.submitter_stopped),
            Err(error) => RefundLookup::Undecided(format!("lookup failed: {error}")),
        };
        match decided {
            RefundLookup::Confirmed(recovery) => {
                let line = refunded(key, &height, &open, json!({"recovered":true,"lookup":recovery}));
                journal.append(line.clone())?;
                return Ok(line);
            }
            RefundLookup::Refused(recovery) => {
                let line = json!({"key":key,"decision":"refund-failed","height":height,"reason":open.reason,
                    "entry":open.entry,"subject":open.subject,"refund":open.refund,"generation":open.generation,
                    "hostRefusal":recovery,"final":"the Host refused this refund; the payment stays in the till"});
                journal.append(line.clone())?;
                return Ok(line);
            }
            RefundLookup::NoEffect(why) => {
                open.generation += 1;
                open.submitter_stopped = false;
                journal.append(json!({"key":key,"decision":"deciding","height":height,"entry":open.entry,
                    "subject":open.subject,"reason":open.reason,"refund":open.refund,
                    "generation":open.generation,"previous":why}))?;
            }
            RefundLookup::Undecided(why) => {
                journal.append(json!({"key":key,"decision":"refund-undecided","generation":open.generation,
                    "operationRecord":record_text,"error":why}))?;
                return Err(format!("refund {key} undecided ({why}); the next pass looks up {record_text}"));
            }
        }
    }
}

/// The renewal's proposal id, from the ledger transactionId it acts on. A
/// Host transactionId is a field element (up to 78 digits) and a workspace
/// name is at most 64 characters, so the id carries a digest of it: 32 hex
/// digits, collision-free in practice, the same on every pass and restart.
fn renew_id(transaction: &str) -> Result<String> {
    let digest = crate::sha256_bytes(format!("mini-concierge-renew-v1\0{transaction}").as_bytes())?;
    Ok(format!("renew-t{}", &digest[..32]))
}

fn refunded(key: &str, height: &str, open: &Refunding, evidence: Value) -> Value {
    json!({"key":key,"decision":"refunded","height":height,"reason":open.reason,"entry":open.entry,
        "subject":open.subject,"refund":open.refund,"generation":open.generation,"evidence":evidence})
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

    fn quote(week: u128, at: u128) -> Quote {
        Quote { room: "9".into(), week, at }
    }

    fn priced(week: u128) -> Priced {
        Priced { week, period: 12, open: false }
    }

    fn issue(not_after: u128) -> Decision {
        Decision::Issue { not_after, period: 12, week: 100 }
    }

    #[test]
    fn a_week_is_issued_from_the_paying_height() {
        let q = quote(100, 38);
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&q), Some(&priced(100)), true, None), issue(52));
    }

    #[test]
    fn a_renewal_after_expiry_starts_again_from_its_height() {
        let q = quote(100, 69);
        assert_eq!(decide(&entry(70, 100), "0", "9", Some(&q), Some(&priced(100)), true, Some(52)), issue(82));
    }

    #[test]
    fn an_early_renewal_extends_the_window() {
        let q = quote(100, 44);
        assert_eq!(decide(&entry(45, 100), "0", "9", Some(&q), Some(&priced(100)), true, Some(52)), issue(64));
    }

    #[test]
    fn an_underpayment_is_refunded() {
        let q = quote(100, 38);
        assert_eq!(decide(&entry(40, 99), "0", "9", Some(&q), Some(&priced(100)), true, None),
            Decision::Refund { reason: "underpaid" });
    }

    #[test]
    fn another_asset_is_refunded() {
        let mut paid = entry(40, 1000);
        paid.asset = "3".into();
        let q = quote(100, 38);
        assert_eq!(decide(&paid, "0", "9", Some(&q), Some(&priced(100)), true, None),
            Decision::Refund { reason: "wrong-asset" });
    }

    /// The price race: bob reads 100 at height 38 and pays at 40; the founder
    /// raises the week to 200 at 39. The decision reads the tariff AT 38, so it
    /// is the same whether the pass runs before or after the raise.
    #[test]
    fn a_payment_binds_the_price_it_read() {
        let q = quote(100, 38);
        let at_quote = priced(100);
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&q), Some(&at_quote), true, None), issue(52));
        // A quote that disagrees with the tariff at its own height is refunded,
        // never kept and never honoured at another price.
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&q), Some(&priced(200)), true, None),
            Decision::Refund { reason: "quote-differs" });
    }

    #[test]
    fn an_unquoted_or_stale_payment_is_refunded() {
        assert_eq!(decide(&entry(40, 100), "0", "9", None, None, true, None), Decision::Refund { reason: "unquoted" });
        let other = Quote { room: "8".into(), week: 100, at: 38 };
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&other), Some(&priced(100)), true, None),
            Decision::Refund { reason: "unquoted" });
        let old = quote(100, 200 - PRICE_SLACK - 1);
        assert_eq!(decide(&entry(200, 100), "0", "9", Some(&old), Some(&priced(100)), true, None),
            Decision::Refund { reason: "stale-quote" });
        let edge = quote(100, 200 - PRICE_SLACK);
        assert_eq!(decide(&entry(200, 100), "0", "9", Some(&edge), Some(&priced(100)), true, None),
            Decision::Issue { not_after: 212, period: 12, week: 100 });
        let future = quote(100, 41);
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&future), Some(&priced(100)), true, None),
            Decision::Refund { reason: "stale-quote" });
    }

    /// A kicked or never-invited subject holds no standing grant under the
    /// room: refunded, unless the tariff said `open` at the quoted height.
    #[test]
    fn a_subject_the_room_does_not_admit_is_refunded() {
        let q = quote(100, 38);
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&q), Some(&priced(100)), false, None),
            Decision::Refund { reason: "not-admitted" });
        let open = Priced { week: 100, period: 12, open: true };
        assert_eq!(decide(&entry(40, 100), "0", "9", Some(&q), Some(&open), false, None), issue(52));
    }

    #[test]
    fn the_memo_round_trips() {
        assert_eq!(parse_quote(Some("room 9 week 100 at 38")), Some(quote(100, 38)));
        assert_eq!(parse_quote(Some("room 9")), None);
    }

    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("concierge-{name}-{}-{}", std::process::id(), now()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn the_journal_restores_windows_and_cursor() {
        let dir = scratch("journal");
        let path = dir.join("journal.jsonl");
        let mut journal = Journal::open(&path).unwrap();
        journal.append(json!({"key":"ledger-tx:401","decision":"deciding","height":"40","subject":"77","notAfter":"52"})).unwrap();
        journal.append(json!({"key":"ledger-tx:401","decision":"issued","height":"40","subject":"77","notAfter":"52"})).unwrap();
        journal.append(json!({"key":"ledger-tx:441","decision":"underpaid","height":"44","subject":"78"})).unwrap();
        journal.append(json!({"key":"ledger-tx:501","decision":"deciding","height":"50","subject":"79","notAfter":"62"})).unwrap();
        journal.append(json!({"key":"ledger-tx:511","decision":"deciding","height":"51","subject":"80","reason":"underpaid",
            "refund":{"amount":"100"},"generation":0})).unwrap();
        journal.append(json!({"key":"ledger-tx:600","decision":"refunded","height":"60","subject":"81"})).unwrap();
        let reopened = Journal::open(&path).unwrap();
        // a begun refund is remembered with its generation and never re-decided
        assert_eq!(reopened.refunding.get("ledger-tx:511").map(|r| r.generation), Some(0));
        assert!(!reopened.refunding["ledger-tx:511"].submitter_stopped);
        assert_eq!(reopened.windows.get("77"), Some(&52));
        assert!(reopened.decided.contains("ledger-tx:441"));
        // an undecided issue is re-run on restart, not skipped, and the
        // cursor never passes it even though height 60 was decided
        assert!(!reopened.decided.contains("ledger-tx:501"));
        assert_eq!(reopened.cursor(), 49);
        fs::remove_dir_all(&dir).unwrap();
    }

    /// Two payments the ledger reports at one height (distinct transactions)
    /// are two decisions; deciding one never marks the other decided, and
    /// their proposal ids, memos and records differ.
    #[test]
    fn two_payments_at_one_height_are_both_decided() {
        let dir = scratch("same-height");
        let path = dir.join("journal.jsonl");
        let mut journal = Journal::open(&path).unwrap();
        let (a, b) = (ledger_key("9001"), ledger_key("9002"));
        assert_ne!(a, b);
        journal.append(json!({"key":a,"decision":"deciding","height":"40","subject":"77","notAfter":"52"})).unwrap();
        journal.append(json!({"key":a,"decision":"issued","height":"40","subject":"77","notAfter":"52"})).unwrap();
        assert!(journal.decided.contains(&a));
        assert!(!journal.decided.contains(&b), "the second payment at height 40 must still be decided");
        journal.append(json!({"key":b,"decision":"refunded","height":"40","subject":"78"})).unwrap();
        let reopened = Journal::open(&path).unwrap();
        assert!(reopened.decided.contains(&a) && reopened.decided.contains(&b));
        assert_ne!(refund_memo("9", "9001", "underpaid"), refund_memo("9", "9002", "underpaid"));
        assert_ne!(refund_record(&dir, "9001", 0), refund_record(&dir, "9002", 0));
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_height_keyed_journal_is_refused() {
        let dir = scratch("old-key");
        let path = dir.join("journal.jsonl");
        fs::write(&path, "{\"key\":\"ledger:40\",\"decision\":\"issued\",\"subject\":\"77\",\"notAfter\":\"52\"}\n").unwrap();
        let error = Journal::open(&path).err().expect("an old height-keyed journal must not load");
        assert!(error.contains("height key") && error.contains("transactionId"), "{error}");
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn refund_lookup_classification() {
        let confirmed = json!({"status":"confirmed","outcome":{"type":"confirmed"}});
        assert!(matches!(classify_refund(&confirmed, false), RefundLookup::Confirmed(_)));
        let refused = json!({"status":"refused","outcome":{"type":"refused"}});
        assert!(matches!(classify_refund(&refused, true), RefundLookup::Refused(_)));
        let contention = json!({"status":"refused","outcome":{"type":"contention"}});
        assert_eq!(classify_refund(&contention, true), RefundLookup::NoEffect("contention"));
        let absent = json!({"status":"not-submitted","outcome":null});
        assert_eq!(classify_refund(&absent, true), RefundLookup::NoEffect("not-submitted"));
        // no marker but the sender may still be running: never a new send
        assert!(matches!(classify_refund(&absent, false), RefundLookup::Undecided(_)));
        let uncertain = json!({"status":"uncertain","outcome":null});
        assert!(matches!(classify_refund(&uncertain, true), RefundLookup::Undecided(_)));
    }

    /// A begun refund whose record exists is resolved by `lookup-operation`
    /// on that record; `credit --action refund` is never run again for it.
    #[test]
    fn an_undecided_refund_is_looked_up_not_resent() {
        use std::os::unix::fs::PermissionsExt;
        let dir = scratch("lookup");
        let log = dir.join("calls.log");
        let records = dir.join("refund-operations");
        fs::create_dir(&records).unwrap();
        fs::set_permissions(&records, fs::Permissions::from_mode(0o700)).unwrap();
        // generation 0 was sent by a previous process: its record exists.
        fs::write(refund_record(&records, "9001", 0), "{}").unwrap();
        let state = dir.join("lookups");
        let fake = dir.join("mini");
        fs::write(&fake, format!("#!/bin/sh\necho \"$*\" >>{log}\ncase \"$*\" in\n\
*lookup-operation*) n=$(cat {state} 2>/dev/null || echo 0); n=$((n+1)); echo $n >{state};\n\
  if [ $n = 1 ]; then echo '{{\"status\":\"uncertain\",\"outcome\":null}}';\n\
  else echo '{{\"status\":\"confirmed\",\"outcome\":{{\"type\":\"confirmed\"}}}}'; fi ;;\n\
*) exit 9 ;;\nesac\n",
            log = log.display(), state = state.display())).unwrap();
        fs::set_permissions(&fake, fs::Permissions::from_mode(0o700)).unwrap();
        let config = Config { mini: fake, workspace: dir.join("ws"), program: dir.join("program.json"),
            inbox: dir.join("inbox"), outbox: dir.join("outbox"), journal: dir.join("journal.jsonl"), roster: None };
        let program = Program { kind: "minidregg-concierge-program-v1".into(), room: "9".into(), concierge: "5".into(),
            till: "12".into(), topic: "renew".into(), member_verbs: vec![],
            refs: ProgramRefs { room: "lab".into(), till: "lab-till".into() } };
        let run = Runner { config: &config, lock: None };
        let mut journal = Journal::open(&config.journal).unwrap();
        let key = ledger_key("9001");
        journal.append(json!({"key":key,"decision":"deciding","height":"40","subject":"77","reason":"underpaid",
            "refund":{"to":"5","amount":"99","asset":"0","memo":refund_memo("9","9001","underpaid")},"generation":0})).unwrap();
        // pass 1: the lookup is uncertain; the refund stays open, nothing is sent
        let open = journal.refunding[&key].clone();
        assert!(drive_refund(&run, "/ws", &program, &records, &mut journal, &key, open).is_err());
        assert!(!journal.decided.contains(&key));
        // restart: the journal still holds the refund open at generation 0
        let mut journal = Journal::open(&config.journal).unwrap();
        let open = journal.refunding[&key].clone();
        assert_eq!(open.generation, 0);
        let line = drive_refund(&run, "/ws", &program, &records, &mut journal, &key, open).unwrap();
        assert_eq!(line["decision"], "refunded");
        assert!(journal.decided.contains(&key));
        let calls = fs::read_to_string(&log).unwrap();
        assert_eq!(calls.lines().filter(|l| l.contains("lookup-operation")).count(), 2);
        assert!(!calls.contains("--action refund"), "a begun refund must never be sent again: {calls}");
        fs::remove_dir_all(&dir).unwrap();
    }

    /// O43: the concierge pass died while its refund child ran. The child
    /// sealed generation 0 (its record exists) and is killed before submit.
    /// While it lives it holds the pass lock, so the next tick waits; once it
    /// is gone the next tick takes the lock, proves the old submitter stopped,
    /// looks the record up (never submitted), sends generation 1, and exactly
    /// one refund is admitted.
    #[test]
    fn a_refund_child_killed_between_seal_and_submit_is_redriven_on_the_next_tick() {
        use std::os::unix::fs::PermissionsExt;
        let dir = scratch("redrive");
        let log = dir.join("calls.log");
        let records = dir.join("refund-operations");
        fs::create_dir(&records).unwrap();
        fs::set_permissions(&records, fs::Permissions::from_mode(0o700)).unwrap();
        let admitted = dir.join("admitted");
        let fake = dir.join("mini");
        // refund: writes its operation record (the seal), and generation 0
        // then waits to be killed before it submits; generation 1 submits.
        // lookup-operation: generation 0's record has no submit marker.
        fs::write(&fake, format!("#!/bin/sh\necho \"$*\" >>{log}\ncase \"$*\" in\n\
*--action\\ refund*) rec=$(echo \"$*\" | sed 's/.*--operation-record //'); echo '{{}}' >\"$rec\";\n\
  case \"$rec\" in *-g0.json) sleep 30; exit 1 ;; esac; echo admitted >>{admitted}; echo '{{\"transaction\":\"7\"}}' ;;\n\
*lookup-operation*) echo '{{\"status\":\"not-submitted\",\"outcome\":null}}' ;;\n\
*) exit 9 ;;\nesac\n", log = log.display(), admitted = admitted.display())).unwrap();
        fs::set_permissions(&fake, fs::Permissions::from_mode(0o700)).unwrap();
        let config = Config { mini: fake.clone(), workspace: dir.join("ws"), program: dir.join("program.json"),
            inbox: dir.join("inbox"), outbox: dir.join("outbox"), journal: dir.join("journal.jsonl"), roster: None };
        let program = Program { kind: "minidregg-concierge-program-v1".into(), room: "9".into(), concierge: "5".into(),
            till: "12".into(), topic: "renew".into(), member_verbs: vec![],
            refs: ProgramRefs { room: "lab".into(), till: "lab-till".into() } };
        let key = ledger_key("9002");
        // The dying pass: it took the lock, journaled the refund as begun and
        // started generation 0's child, then died (its lock descriptor closes).
        let first = lock_pass(&config).unwrap();
        let mut journal = Journal::open(&config.journal).unwrap();
        journal.append(json!({"key":key,"decision":"deciding","height":"41","subject":"78","reason":"underpaid",
            "refund":{"to":"6","amount":"40","asset":"0","memo":refund_memo("9","9002","underpaid")},"generation":0})).unwrap();
        let record0 = refund_record(&records, "9002", 0);
        let mut child = Command::new(&fake);
        child.args(["credit", "--action", "refund", "--operation-record", &record0.display().to_string()]);
        inherit_lock(&mut child, first.fd());
        {
            use std::os::unix::process::CommandExt;
            child.process_group(0);
        }
        let mut child = child.spawn().unwrap();
        for _ in 0..200 { if record0.exists() { break } std::thread::sleep(Duration::from_millis(10)); }
        assert!(record0.exists(), "generation 0 sealed its record");
        drop(first);
        drop(journal);
        // The next tick while the killed-to-be child lives: the lock is held.
        assert!(lock_pass(&config).is_err(), "a live refund child keeps the pass lock");
        // Killed before submit, with every descendant that holds the lock
        // (the `sleep` inside it would otherwise keep the lock, rightly).
        unsafe { libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL); }
        child.wait().unwrap();
        // The next tick: lock, prove, look up, re-drive.
        let lock = lock_pass(&config).unwrap();
        let run = Runner { config: &config, lock: Some(lock.fd()) };
        let mut journal = Journal::open(&config.journal).unwrap();
        assert!(!journal.refunding[&key].submitter_stopped);
        prove_previous_submitters_stopped(&mut journal, &lock).unwrap();
        let open = journal.refunding[&key].clone();
        let line = drive_refund(&run, "/ws", &program, &records, &mut journal, &key, open).unwrap();
        assert_eq!(line["decision"], "refunded");
        assert_eq!(line["generation"], 1);
        assert_eq!(fs::read_to_string(&admitted).unwrap().lines().count(), 1, "exactly one refund admitted");
        let calls = fs::read_to_string(&log).unwrap();
        assert_eq!(calls.lines().filter(|l| l.contains("lookup-operation")).count(), 1);
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_refund_that_never_lands_is_named_stalled_after_its_generations() {
        let dir = scratch("stalled");
        let records = dir.join("refund-operations");
        fs::create_dir(&records).unwrap();
        let config = Config { mini: "/nonexistent".into(), workspace: dir.join("ws"), program: dir.join("program.json"),
            inbox: dir.join("inbox"), outbox: dir.join("outbox"), journal: dir.join("journal.jsonl"), roster: None };
        let program = Program { kind: "minidregg-concierge-program-v1".into(), room: "9".into(), concierge: "5".into(),
            till: "12".into(), topic: "renew".into(), member_verbs: vec![],
            refs: ProgramRefs { room: "lab".into(), till: "lab-till".into() } };
        let key = ledger_key("9003");
        let mut journal = Journal::open(&config.journal).unwrap();
        journal.append(json!({"key":key,"decision":"deciding","height":"42","subject":"79","reason":"underpaid",
            "refund":{"to":"6","amount":"40","asset":"0","memo":"m"},"generation":REFUND_GENERATIONS_MAX})).unwrap();
        let open = journal.refunding[&key].clone();
        let run = Runner { config: &config, lock: None };
        let line = drive_refund(&run, "/ws", &program, &records, &mut journal, &key, open).unwrap();
        assert_eq!(line["decision"], "refund-stalled");
        assert!(line["notice"].as_str().unwrap().contains("stays in the till"));
        assert!(journal.decided.contains(&key));
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn a_renewal_id_from_a_full_transaction_id_is_a_workspace_name() {
        let tx = "65521247787507393155002196623437335179160280648006500683460654464838909513152";
        let id = renew_id(tx).unwrap();
        assert!(id.len() <= 64 && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'), "{id}");
        assert_eq!(id, renew_id(tx).unwrap());
        assert_ne!(id, renew_id("65521247787507393155002196623437335179160280648006500683460654464838909513153").unwrap());
    }

    #[test]
    fn an_issued_window_is_rostered_once_and_its_newest_reference_reaches_the_members_home() {
        let dir = std::env::temp_dir().join(format!("concierge-roster-{}-{}", std::process::id(), now()));
        fs::create_dir_all(dir.join("outbox/77")).unwrap();
        fs::create_dir_all(dir.join("homes/77")).unwrap();
        let mut journal = Journal::open(&dir.join("journal.jsonl")).unwrap();
        journal.append(json!({"key":"ledger-tx:401","decision":"issued","height":"40","subject":"77","notAfter":"52"})).unwrap();
        assert!(!journal.rostered.contains("77"));
        journal.append(json!({"key":"roster:77","decision":"rostered","subject":"77"})).unwrap();
        let reopened = Journal::open(&dir.join("journal.jsonl")).unwrap();
        assert!(reopened.rostered.contains("77") && reopened.windows["77"] == 52);
        fs::write(dir.join("outbox/77/renew-t401.json"), b"{\"recipient\":\"77\",\"n\":1}").unwrap();
        std::thread::sleep(Duration::from_millis(20));
        fs::write(dir.join("outbox/77/renew-t402.json"), b"{\"recipient\":\"77\",\"n\":2}").unwrap();
        deliver_window(&dir.join("outbox"), &dir.join("homes"), "subscribers", "77").unwrap();
        assert_eq!(fs::read(dir.join("homes/77/requests/subscribers-invite.json")).unwrap(), b"{\"recipient\":\"77\",\"n\":2}");
        // No home: nothing is delivered and nothing fails.
        deliver_window(&dir.join("outbox"), &dir.join("homes"), "subscribers", "78").unwrap();
        let _ = fs::remove_dir_all(&dir);
    }
}
