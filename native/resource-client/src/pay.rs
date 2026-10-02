//! PAY P4: the client side of the payment rail (PAY.md §2.2–§2.5, §3.4, §5).
//!
//! Every verb runs through a participant workspace (`mini workspace --action init`) whose
//! session socket reaches the Host's pay operations:
//!
//! | op | purpose |
//! |---|---|
//! | 103 / 104 / 105 / 106 | book-or-assignment plan, detached assembly, submit, receipt-only lookup |
//! | 107 | the public pay view (roots, tariff, nextFree, book) |
//! | 129 | the public clock view (the deployment clock: now, slot) |
//! | 108 / 109 / 110 / 111 | observation plan, assembly, submit, receipt-only lookup |
//! | 112 | the public enrollment view (entries, journal) |
//! | 117 / 118 / 119 / 120 | the observer's self-enrollment of ONE enrollment-index record: plan, assembly, submit, receipt-only lookup (operator socket only) |
//!
//! Mini owns every codec: the client authors and inspects through the Host (`author`/`inspect`,
//! ops 7/8) and signs the plan header the Host prints. It decides nothing about a payment; it
//! reads the Host's refusal and chooses what to do next (retry, wait, drop, or stop).
//!
//! Retained state lives in the workspace:
//! - `attempts/pay-{assign,book,report}-…/`: one directory per signed call (view, command,
//!   plan, signature, ingress, submit marker, outcome, the client's `decision.json`);
//! - `pay/address-ACCOUNT.json`: the index a subject was assigned (the public view withholds
//!   the assignment map, so the assignee keeps it from its own signed command);
//! - `pay/receipts/SIGNATURE.ADDRESS`: a symlink to the attempt that decided that transfer.
//!   This is the directory the watcher reads as its receipts (`pay-watcher` `load_receipts`);
//! - `pay/quarantine/SIGNATURE.ADDRESS.json`: a record the kernel refused on its own merits.
//!
//! Records at the tariff's enrollment index (PAY §11) never go into a report: the observation
//! receiver refuses them (`enrolIndexNeedsReceiver`). Each one is submitted ALONE through ops
//! 117-120 under the observer's `C_enrol`, and the kernel's `decideEnrol` decides enrol, renew or
//! journal. The client carries bytes and reads the answer; it decides nothing about the payment.

use super::*;
use crate::workspace;
use std::os::unix::fs::symlink;

const ASSIGN_OPS: Ops = Ops {
    plan: 103,
    assemble: 104,
    submit: 105,
    lookup: 106,
};
const OBSERVE_OPS: Ops = Ops {
    plan: 108,
    assemble: 109,
    submit: 110,
    lookup: 111,
};
const ENROL_OPS: Ops = Ops {
    plan: 117,
    assemble: 118,
    submit: 119,
    lookup: 120,
};
const VIEW_OP: u8 = 107;
/// The public clock view (K-CLOCK): the deployment clock's `{now, slot}`.
const CLOCK_VIEW_OP: u8 = 129;
const ENROLMENT_VIEW_OP: u8 = 112;

/// The durable preflight's refusal of a spent nullifier, exactly as the Host renders it
/// (phase `durable`). On a report whose tip is newer than the clock it can only be an
/// observation's nullifier (see `observe`), which means the transfer was already credited.
const ALREADY_CONSUMED: &str = "Minidregg.Kernel.DurableDataIntent.RejectReason.durable \
    (Minidregg.Kernel.DurableCommitProtocol.RejectReason.alreadyConsumed)";
const REJECT_PREFIXES: [&str; 4] = [
    "Minidregg.Kernel.PayObservation.Reject.",
    "Minidregg.Kernel.PayAssignmentReceiver.Reject.",
    "Minidregg.Kernel.PayBookReceiver.Reject.",
    "Minidregg.Kernel.PayEnrolReceiver.Reject.",
];
/// Refusals decided by one observation on its own (`PayObservation.decideObservation`, and the
/// Book admission of its credit). A report carrying such a record is refused whole.
const PER_OBSERVATION: [&str; 11] = [
    "malformedObservation",
    "wrongMint",
    "wrongTokenProgram",
    "unknownIndex",
    "addressMismatch",
    "unassignedIndex",
    "payerIsIssuer",
    "zeroAmount",
    "observationAfterTip",
    "bookAdmission",
    "enrolIndexNeedsReceiver",
];

#[derive(Clone, Copy)]
struct Ops {
    plan: u8,
    assemble: u8,
    submit: u8,
    lookup: u8,
}

/// The workspace a pay verb runs as.
struct Session {
    root: PathBuf,
    workspace: Value,
    host: PathBuf,
    config: PathBuf,
    socket: PathBuf,
    key: PathBuf,
    subject: String,
    /// The owner-private operator socket of the same Host (`mini serve --operator-socket`):
    /// the only route to ops 117-120.
    operator_socket: Option<PathBuf>,
}

impl Session {
    fn open(root: &Path) -> Result<Self> {
        Self::open_for_audit(root, false)
    }

    fn open_for_audit(root: &Path, offline: bool) -> Result<Self> {
        let root = absolute(root)?;
        let workspace = if offline {
            workspace::load_retained(&root)?.snapshot().clone()
        } else {
            workspace::load(&root)?
        };
        let socket = SOCKET
            .get()
            .cloned()
            .ok_or("pay verbs need a workspace with a pinned session socket")?;
        let session = Session {
            host: workspace::member_path(&workspace, "host")?,
            config: workspace::member_path(&workspace, "config")?,
            key: workspace::member_path(&workspace, "key")?,
            subject: workspace::member(&workspace, "subject")?.to_owned(),
            operator_socket: None,
            socket,
            workspace,
            root,
        };
        for directory in [
            session.pay_dir(),
            session.receipts_dir(),
            session.quarantine_dir(),
        ] {
            if !directory.exists() {
                workspace::make_private_dir(&directory)?;
            }
            workspace::private_dir(&directory)?;
        }
        Ok(session)
    }

    fn pay_dir(&self) -> PathBuf {
        self.root.join("pay")
    }

    fn receipts_dir(&self) -> PathBuf {
        self.root.join("pay").join("receipts")
    }

    fn quarantine_dir(&self) -> PathBuf {
        self.root.join("pay").join("quarantine")
    }

    fn call(&self, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
        let socket = if (ENROL_OPS.plan..=ENROL_OPS.lookup).contains(&operation) {
            self.operator_socket
                .as_ref()
                .ok_or("ops 117-120 need --operator-socket (they are not on the public socket)")?
        } else {
            &self.socket
        };
        session_invoke(&self.host, socket, &self.config, operation, payload)
    }

    fn new_attempt(&self, stem: &str) -> Result<PathBuf> {
        for _ in 0..8 {
            let attempt = self
                .root
                .join("attempts")
                .join(format!("pay-{stem}-{}", workspace::random_nonce()?));
            if !attempt.exists() {
                workspace::make_private_dir(&attempt)?;
                return Ok(attempt);
            }
        }
        Err("could not allocate a distinct pay attempt name".into())
    }

    fn inspect(&self, kind: &str, input: &Path, output: &Path) -> Result<Value> {
        inspect(&self.host, &self.config, kind, input, output)
    }
}

fn retain_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    create_private(path, &bytes)
}

/// Publish complete decision evidence before a receipt can acknowledge it to the
/// watcher. A crash leaves an unused stage or the complete immutable value.
fn publish_decision_json(path: &Path, value: &Value) -> Result<()> {
    if path.exists() {
        return if workspace::bounded_json(path)? == *value { Ok(()) }
            else { Err("retained payment decision differs; refusing to replace it".into()) };
    }
    let parent = path.parent().ok_or("payment decision has no parent")?;
    let stage = parent.join(format!(".decision-stage-{}.json", workspace::random_nonce()?));
    retain_json(&stage, value)?;
    match fs::hard_link(&stage, path) {
        Ok(()) => {},
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            if workspace::bounded_json(path)? != *value {
                return Err("concurrent payment decision differs; refusing to replace it".into());
            }
        },
        Err(error) => return Err(format!("cannot publish payment decision: {error}")),
    }
    sync_directory_ancestors(parent)?;
    fs::remove_file(&stage).map_err(|error| format!("cannot remove own decision stage: {error}"))?;
    sync_directory_ancestors(parent)
}

fn frame_body(frame: &[u8], operation: u8) -> Result<&[u8]> {
    match frame {
        [actual, body @ ..] if *actual == operation => Ok(body),
        [255, body @ ..] => Err(format!(
            "Host refused op{operation} before a decision: {}",
            String::from_utf8_lossy(body)
        )),
        _ => Err(format!("op{operation} returned an invalid frame")),
    }
}

fn text(value: &Value, field: &str) -> Result<String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| format!("Host JSON lacks {field}"))
}

fn number(value: &Value, field: &str) -> Result<u128> {
    let raw = match value.get(field) {
        Some(Value::String(text)) => text.clone(),
        Some(Value::Number(number)) => number.to_string(),
        _ => return Err(format!("{field} must be an unsigned integer")),
    };
    if raw.is_empty() || (raw.len() > 1 && raw.starts_with('0')) {
        return Err(format!("{field} must be a canonical unsigned integer"));
    }
    raw.parse::<u128>()
        .map_err(|_| format!("{field} must be an unsigned integer below 2^128"))
}

fn hex_exact(value: &str, bytes: usize, field: &str) -> Result<Vec<u8>> {
    if value.len() != bytes * 2 || value.bytes().any(|b| b.is_ascii_uppercase()) {
        return Err(format!("{field} must be {bytes} bytes of lowercase hex"));
    }
    decode_hex(value).map_err(|_| format!("{field} must be {bytes} bytes of lowercase hex"))
}

fn base58(bytes: &[u8]) -> String {
    bs58::encode(bytes).into_string()
}

/// A 32-byte key given as lowercase hex or as base58 (the operator's spelling of addresses
/// and mints); the Host takes hex.
fn key_hex(value: &str, field: &str) -> Result<String> {
    if value.len() == 64 {
        return hex_exact(value, 32, field).map(|bytes| hex(&bytes));
    }
    let bytes = bs58::decode(value)
        .into_vec()
        .map_err(|_| format!("{field} is neither 64 hex digits nor base58"))?;
    if bytes.len() != 32 {
        return Err(format!("{field} does not decode to 32 bytes"));
    }
    Ok(hex(&bytes))
}

// ---------------------------------------------------------------- the Host's answer

/// The client's reading of one Host outcome.
enum Answer {
    Confirmed(Value),
    /// A refusal: the named reason when the detail is one of the pay receivers' own
    /// `Reject` constructors or the durable nullifier refusal, and the raw text either way.
    Refused {
        reason: Option<String>,
        phase: String,
        detail: String,
    },
    /// The Host did not decide (uncertain, unavailable, contention, absent) or the transport
    /// lost the reply. The attempt is retained for an exact lookup.
    Undecided(String),
}

impl Answer {
    fn reason(&self) -> Option<&str> {
        match self {
            Answer::Refused { reason, .. } => reason.as_deref(),
            _ => None,
        }
    }

    fn render(&self) -> String {
        match self {
            Answer::Confirmed(value) => format!(
                "confirmed {}",
                value
                    .get("confirmation")
                    .and_then(Value::as_str)
                    .unwrap_or("?")
            ),
            Answer::Refused {
                reason,
                phase,
                detail,
            } => match reason {
                Some(reason) => format!("refused {reason} (phase {phase})"),
                None => format!("refused unnamed: {detail} (phase {phase})"),
            },
            Answer::Undecided(detail) => format!("undecided {detail}"),
        }
    }
}

/// The reason a refusal names, read from the Host's own rendering: the durable
/// already-consumed refusal, or a pay receiver's `Reject` constructor. Anything else is
/// unnamed and is never treated as one of the reasons the client acts on.
fn refusal_reason(phase: &str, detail: &str) -> Option<String> {
    // Lean's `repr` is a pretty-printer: a long reason wraps onto an indented second line.
    let detail = detail.split_whitespace().collect::<Vec<_>>().join(" ");
    let detail = detail.as_str();
    if phase == "durable" && detail == ALREADY_CONSUMED {
        return Some("alreadyConsumed".into());
    }
    REJECT_PREFIXES.iter().find_map(|prefix| {
        let rest = detail.strip_prefix(prefix)?;
        let name: String = rest
            .chars()
            .take_while(|c| c.is_ascii_alphanumeric())
            .collect();
        let tail = &rest[name.len()..];
        if name.is_empty() || !(tail.is_empty() || tail.starts_with(' ')) {
            return None;
        }
        // The self-enrollment receiver wraps the decision's and the verifier's own reasons:
        // `decision (Minidregg.Kernel.PayEnrolDecision.Reject.belowJournalFloor)` reads
        // `decision:belowJournalFloor`.
        if *prefix == "Minidregg.Kernel.PayEnrolReceiver.Reject."
            && matches!(name.as_str(), "decision" | "verifier")
        {
            let inner = tail.trim_start().strip_prefix('(')?;
            let path: String = inner
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '.')
                .collect();
            let leaf = path.rsplit('.').next().filter(|leaf| !leaf.is_empty())?;
            return Some(format!("{name}:{leaf}"));
        }
        Some(name)
    })
}

fn hex_text(value: &Value, field: &str) -> String {
    value
        .get(field)
        .and_then(Value::as_str)
        .and_then(|text| decode_hex(text).ok())
        .map(|bytes| String::from_utf8_lossy(&bytes).into_owned())
        .unwrap_or_default()
}

fn answer(outcome: Value) -> Answer {
    match outcome.get("type").and_then(Value::as_str) {
        Some("confirmed") => Answer::Confirmed(outcome),
        Some("refused") => {
            let phase = hex_text(&outcome, "phase");
            let detail = hex_text(&outcome, "detail")
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" ");
            // A blind submission (op 105, MR's rule) answers the uniform `undisclosed`
            // frame; the Host's reason field says so and nothing else is named.
            let reason = match outcome.get("reason").and_then(Value::as_str) {
                Some("undisclosed") => Some("undisclosed".to_owned()),
                _ => refusal_reason(&phase, &detail),
            };
            Answer::Refused {
                reason,
                phase,
                detail,
            }
        }
        Some(kind) => Answer::Undecided(format!("{kind} {}", hex_text(&outcome, "detail"))),
        None => Answer::Undecided("outcome without a type".into()),
    }
}

// ---------------------------------------------------------------- one signed call

/// Read the public pay view (op 107) and the deployment clock (op 129) into
/// `directory/{view,clock}.{bin,json}`. The pay cell keeps no clock on final
/// (the clock cell does), so the view this returns and retains carries the
/// clock cell's `{slot, now}` as `clock`: the tick and status logic read it there.
fn read_view(session: &Session, directory: &Path) -> Result<Value> {
    let frame = session.call(VIEW_OP, &[])?;
    let body = frame_body(&frame, VIEW_OP)?;
    let bin = directory.join("view.bin");
    create_private(&bin, body)?;
    let mut view = session.inspect("pay-view", &bin, &directory.join("pay-view.json"))?;
    let frame = session.call(CLOCK_VIEW_OP, &[])?;
    let body = frame_body(&frame, CLOCK_VIEW_OP)?;
    let clock_bin = directory.join("clock.bin");
    create_private(&clock_bin, body)?;
    let clock = session.inspect("clock-view", &clock_bin, &directory.join("clock.json"))?;
    view["clock"] = json!({"slot": text(&clock, "slot")?, "now": text(&clock, "now")?});
    create_private(
        &directory.join("view.json"),
        &serde_json::to_vec_pretty(&view).map_err(|error| error.to_string())?,
    )?;
    Ok(view)
}

/// A view for a read-only verb: read into a scratch directory under `pay/`, then dropped.
fn scratch_view(session: &Session) -> Result<Value> {
    let scratch = session
        .pay_dir()
        .join(format!(".view-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&scratch)?;
    let result = read_view(session, &scratch);
    let _ = fs::remove_dir_all(&scratch);
    result
}

/// Author `command` as `kind`, get the Host's plan, sign its header with the workspace key and
/// assemble the ingress. Every byte is retained in `directory`.
fn prepare(
    session: &Session,
    directory: &Path,
    kind: &str,
    command: &Value,
    ops: Ops,
) -> Result<Vec<u8>> {
    let source = directory.join("command.json");
    retain_json(&source, command)?;
    let command_bin = directory.join("command.bin");
    author(
        &session.host,
        &session.config,
        OsStr::new(kind),
        &source,
        &command_bin,
    )?;
    let command_bytes = fs::read(&command_bin).map_err(|error| error.to_string())?;
    let frame = session.call(ops.plan, &command_bytes)?;
    let plan = frame_body(&frame, ops.plan)?.to_vec();
    let plan_bin = directory.join("plan.bin");
    create_private(&plan_bin, &plan)?;
    let plan_view = session.inspect("pay-plan", &plan_bin, &directory.join("plan.json"))?;
    if text(&plan_view, "commandBytes")? != hex(&command_bytes) {
        return Err("the Host's plan is not for the authored command".into());
    }
    let header = decode_hex(
        plan_view
            .get("header")
            .and_then(|header| header.get("canonical"))
            .and_then(Value::as_str)
            .ok_or("the Host's plan has no canonical header")?,
    )?;
    let signature = read_secret(&session.key)?.sign(&header).to_bytes();
    create_private(&directory.join("signature.bin"), &signature)?;
    let length: u32 = plan.len().try_into().map_err(|_| "plan too large")?;
    let mut pair = length.to_le_bytes().to_vec();
    pair.extend_from_slice(&plan);
    pair.extend_from_slice(&signature);
    let frame = session.call(ops.assemble, &pair)?;
    let ingress = frame_body(&frame, ops.assemble)?.to_vec();
    create_private(&directory.join("ingress.bin"), &ingress)?;
    sync_directory_ancestors(directory)?;
    Ok(ingress)
}

/// Submit a prepared ingress once. The marker is durable before the frame leaves, so a crash
/// after this point is resolved by an exact lookup, never by a blind resubmit of new bytes.
fn submit_once(session: &Session, directory: &Path, ops: Ops) -> Result<Answer> {
    let ingress = fs::read(directory.join("ingress.bin")).map_err(|error| error.to_string())?;
    retain_json(
        &directory.join("submit-marker.json"),
        &json!({"type":"minidregg-pay-submit-v1","operation":ops.submit,
            "ingressSha256":hex(&sha2::Sha256::digest(&ingress))}),
    )?;
    sync_directory_ancestors(directory)?;
    let frame = match session.call(ops.submit, &ingress) {
        Ok(frame) => frame,
        Err(error) => return Ok(Answer::Undecided(format!("transport: {error}"))),
    };
    retained_outcome(session, directory, "outcome", &frame, ops.submit)
}

fn retained_outcome(
    session: &Session,
    directory: &Path,
    stem: &str,
    frame: &[u8],
    operation: u8,
) -> Result<Answer> {
    let body = frame_body(frame, operation)?;
    let bin = directory.join(format!("{stem}.bin"));
    create_private(&bin, body)?;
    sync_directory_ancestors(directory)?;
    let value = session.inspect("outcome", &bin, &directory.join(format!("{stem}.json")))?;
    Ok(answer(value))
}

/// The receipt-only lookup of a retained ingress (op 106 / 111). `absent` means the Host
/// never accepted it.
fn lookup(session: &Session, directory: &Path, ops: Ops) -> Result<Answer> {
    let ingress = fs::read(directory.join("ingress.bin")).map_err(|error| error.to_string())?;
    let stem = (0..10_000)
        .map(|index| format!("lookup-{index:04}"))
        .find(|stem| !directory.join(format!("{stem}.bin")).exists())
        .ok_or("lookup names exhausted")?;
    let frame = session.call(ops.lookup, &ingress)?;
    retained_outcome(session, directory, &stem, &frame, ops.lookup)
}

fn decide(directory: &Path, decision: &str, answer: &Answer) -> Result<()> {
    let path = directory.join("decision.json");
    if path.exists() {
        let retained = workspace::bounded_json(&path)?;
        if retained["type"] != "minidregg-pay-decision-v1" || retained["decision"] != decision {
            return Err("retained payment decision mismatch".into());
        }
        return Ok(());
    }
    publish_decision_json(
        &path,
        &json!({"type":"minidregg-pay-decision-v1","decision":decision,"host":answer.render()}),
    )
}

fn decision(directory: &Path) -> Option<String> {
    let value = workspace::bounded_json(&directory.join("decision.json")).ok()?;
    value
        .get("decision")
        .and_then(Value::as_str)
        .map(str::to_owned)
}

fn pay_attempts(session: &Session, stem: &str) -> Result<Vec<PathBuf>> {
    let mut found = Vec::new();
    let prefix = format!("pay-{stem}-");
    for entry in fs::read_dir(session.root.join("attempts")).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        if entry.file_name().to_string_lossy().starts_with(&prefix) {
            found.push(entry.path());
        }
    }
    found.sort();
    Ok(found)
}

// ---------------------------------------------------------------- pay address / status

fn account_reference(session: &Session, name: Option<&str>) -> Result<Value> {
    if let Some(name) = name {
        let reference = workspace::reference(&session.root, name)?;
        if workspace::member(&reference, "kind")? != "account" {
            return Err(format!("reference {name} is not an account"));
        }
        return Ok(reference);
    }
    let mut accounts = Vec::new();
    for entry in fs::read_dir(session.root.join("refs")).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let file = entry.file_name().to_string_lossy().into_owned();
        if let Some(name) = file.strip_suffix(".json") {
            let reference = workspace::reference(&session.root, name)?;
            if workspace::member(&reference, "kind")? == "account" {
                accounts.push(reference);
            }
        }
    }
    match accounts.len() {
        1 => Ok(accounts.remove(0)),
        0 => Err("the workspace holds no account reference; import one or pass --account".into()),
        _ => Err("the workspace holds several account references; pass --account NAME".into()),
    }
}

fn address_path(session: &Session, account: &str) -> PathBuf {
    session.pay_dir().join(format!("address-{account}.json"))
}

fn print_address(record: &Value) -> Result<()> {
    let tariff = record.get("tariff").ok_or("retained address lacks its tariff")?;
    println!(
        "index {} → {}",
        text(record, "index")?,
        text(record, "base58")?
    );
    println!(
        "send the token with mint {} (token program {}) to this address from a wallet you control.",
        base58(&hex_exact(&text(tariff, "mint")?, 32, "mint")?),
        base58(&hex_exact(&text(tariff, "tokenProgram")?, 32, "tokenProgram")?)
    );
    println!(
        "1 atomic unit ({} decimals) = {} credit; at most {} atomic units are credited per payment.",
        text(tariff, "decimals")?,
        text(tariff, "creditPerAtomic")?,
        text(tariff, "maxPerObservation")?
    );
    Ok(())
}

fn finish_address(session: &Session, attempt: &Path, account: &str) -> Result<()> {
    let view = workspace::bounded_json(&attempt.join("view.json"))?;
    let command = workspace::bounded_json(&attempt.join("command.json"))?;
    let index = text(&command, "index")?;
    let row: usize = index.parse().map_err(|_| "assigned index out of range")?;
    let address = view
        .get("book")
        .and_then(Value::as_array)
        .and_then(|book| book.get(row))
        .and_then(Value::as_str)
        .ok_or("the assigned index is not in the view's book")?;
    let bytes = hex_exact(address, 32, "book address")?;
    let record = json!({"type":"minidregg-pay-address-v1","account":account,"index":index,
        "address":address,"base58":base58(&bytes),"tariff":view.get("tariff"),
        "attempt":utf8_path(attempt)?});
    retain_json(&address_path(session, account), &record)?;
    print_address(&record)
}

fn address(session: &Session, account_name: Option<&str>) -> Result<()> {
    let reference = account_reference(session, account_name)?;
    let account = workspace::member(&reference, "target")?.to_owned();
    let capability = workspace::member(
        &reference,
        if reference.get("operationCapability").is_some() {
            "operationCapability"
        } else {
            "observeCapability"
        },
    )?
    .to_owned();
    let retained = address_path(session, &account);
    if retained.exists() {
        return print_address(&workspace::bounded_json(&retained)?);
    }
    // A request whose answer was lost: settle it by exact lookup before asking again.
    for attempt in pay_attempts(session, "assign")? {
        if decision(&attempt).is_some() || !attempt.join("submit-marker.json").exists() {
            continue;
        }
        let command = workspace::bounded_json(&attempt.join("command.json"))?;
        if text(&command, "account")? != account {
            continue;
        }
        match lookup(session, &attempt, ASSIGN_OPS)? {
            found @ Answer::Confirmed(_) => {
                decide(&attempt, "assigned", &found)?;
                return finish_address(session, &attempt, &account);
            }
            other => decide(&attempt, "abandoned", &other)?,
        }
    }
    let mut retried = false;
    loop {
        let attempt = session.new_attempt("assign")?;
        let view = read_view(session, &attempt)?;
        let command = json!({"subject":session.subject,"capability":capability,
            "account":account,"index":text(&view, "nextFree")?,
            "nonce":workspace::random_nonce()?,
            "expectedAuthorityRoot":text(&view, "authorityRoot")?,
            "expectedPayRoot":text(&view, "payRoot")?});
        prepare(session, &attempt, "pay-assign", &command, ASSIGN_OPS)?;
        let result = submit_once(session, &attempt, ASSIGN_OPS)?;
        match &result {
            Answer::Confirmed(_) => {
                decide(&attempt, "assigned", &result)?;
                return finish_address(session, &attempt, &account);
            }
            Answer::Refused { .. }
                if !retried
                    && matches!(
                        result.reason(),
                        Some("stalePay" | "staleAuthority" | "indexNotNext")
                    ) =>
            {
                decide(&attempt, "retried", &result)?;
                retried = true;
            }
            Answer::Refused { .. } => {
                decide(&attempt, "refused", &result)?;
                set_exit(3);
                return Err(format!("pay address {}", result.render()));
            }
            Answer::Undecided(_) => {
                set_exit(4);
                return Err(format!(
                    "pay address {}; the next `pay address` looks it up ({})",
                    result.render(),
                    attempt.display()
                ));
            }
        }
    }
}

fn status(session: &Session, account_name: Option<&str>) -> Result<()> {
    let view = scratch_view(session)?;
    let reference = account_reference(session, account_name)?;
    let account = workspace::member(&reference, "target")?.to_owned();
    let retained = address_path(session, &account);
    if retained.exists() {
        let record = workspace::bounded_json(&retained)?;
        println!(
            "account {account}  index {}  address {}",
            text(&record, "index")?,
            text(&record, "base58")?
        );
    } else {
        println!("account {account}  no deposit address yet (`pay address`)");
    }
    let tariff = view.get("tariff").filter(|tariff| !tariff.is_null());
    let asset = tariff
        .map(|tariff| text(tariff, "asset"))
        .transpose()?
        .unwrap_or_else(|| "0".into());
    let (resource, _, _) = workspace::signed_view(
        &session.root,
        &session.workspace,
        &reference,
        "resource",
    )?;
    let balance = resource
        .get("balances")
        .and_then(Value::as_array)
        .and_then(|rows| {
            rows.iter().find_map(|row| {
                let row = row.as_array()?;
                (row.first()?.as_str()? == asset).then(|| row.get(1)?.as_str().map(str::to_owned))?
            })
        })
        .unwrap_or_else(|| "0".into());
    println!("credit {balance}  (asset {asset})");
    match view.get("clock").filter(|clock| !clock.is_null()) {
        Some(clock) => println!(
            "clock slot {}  now {}",
            text(clock, "slot")?,
            text(clock, "now")?
        ),
        None => println!("clock unavailable"),
    }
    match tariff {
        Some(tariff) => println!(
            "tariff v{}  valid {}",
            text(tariff, "version")?,
            tariff.get("valid").and_then(Value::as_bool).unwrap_or(false)
        ),
        None => println!("tariff unavailable"),
    }
    Ok(())
}

// ---------------------------------------------------------------- pay book (operator)

fn book(session: &Session, source: &Path) -> Result<()> {
    let request = workspace::bounded_json(source)?;
    let control = text(&request, "control")?;
    let book: Vec<String> = request
        .get("book")
        .and_then(Value::as_array)
        .ok_or("pay book source needs a book array (may be empty)")?
        .iter()
        .enumerate()
        .map(|(row, value)| {
            key_hex(
                value.as_str().ok_or("book rows are strings")?,
                &format!("book[{row}]"),
            )
        })
        .collect::<Result<_>>()?;
    let tariff = match request.get("tariff") {
        None | Some(Value::Null) => Value::Null,
        Some(tariff) => {
            let mut tariff = tariff.clone();
            for field in ["mint", "tokenProgram"] {
                let spelled = key_hex(&text(&tariff, field)?, field)?;
                tariff[field] = Value::String(spelled);
            }
            tariff
        }
    };
    let mut retried = false;
    loop {
        let attempt = session.new_attempt("book")?;
        let view = read_view(session, &attempt)?;
        let command = json!({"sponsor":session.subject,"control":control,
            "nonce":workspace::random_nonce()?,
            "expectedFactoryRoot":text(&view, "factoryRoot")?,
            "expectedAuthorityRoot":text(&view, "authorityRoot")?,
            "expectedPayRoot":text(&view, "payRoot")?,
            "bookStart":text(&view, "bookSize")?,"book":book,"tariff":tariff});
        prepare(session, &attempt, "pay-book", &command, ASSIGN_OPS)?;
        let result = submit_once(session, &attempt, ASSIGN_OPS)?;
        match &result {
            Answer::Confirmed(_) => {
                decide(&attempt, "installed", &result)?;
                println!(
                    "pay book {}: {} row(s) from index {}{}",
                    result.render(),
                    book.len(),
                    text(&view, "bookSize")?,
                    if tariff.is_null() { "" } else { " and the tariff" }
                );
                return Ok(());
            }
            Answer::Refused { .. }
                if !retried
                    && matches!(
                        result.reason(),
                        Some("stalePay" | "staleAuthority" | "bookIndexPresent")
                    ) =>
            {
                decide(&attempt, "retried", &result)?;
                retried = true;
            }
            Answer::Refused { .. } => {
                decide(&attempt, "refused", &result)?;
                set_exit(3);
                return Err(format!("pay book {}", result.render()));
            }
            Answer::Undecided(_) => {
                set_exit(4);
                return Err(format!(
                    "pay book {}; look it up before retrying ({})",
                    result.render(),
                    attempt.display()
                ));
            }
        }
    }
}

// ---------------------------------------------------------------- the watcher's config

struct WatchOptions {
    min_endpoints: Option<u128>,
    max_pages: Option<u128>,
    page_size: Option<u128>,
    enrol: Option<(u128, u128)>,
}

/// The watcher's configuration, derived from the signed pay view: the tariff's asset, the
/// ASSIGNED book rows (indices below `nextFree`; assignment is sequential), and this
/// workspace's receipts directory. A row nobody holds yet is not watched, so a payment to it is
/// read once someone is assigned it.
fn watch_config(session: &Session, out: &Path, options: WatchOptions) -> Result<()> {
    let view = scratch_view(session)?;
    let tariff = view
        .get("tariff")
        .filter(|tariff| !tariff.is_null())
        .ok_or("the pay cell has no tariff yet")?;
    let rows = view
        .get("book")
        .and_then(Value::as_array)
        .ok_or("pay view lacks its book")?;
    let assigned: usize = text(&view, "nextFree")?
        .parse()
        .map_err(|_| "nextFree out of range")?;
    let enrol_index = options
        .enrol
        .map(|(index, _)| usize::try_from(index).map_err(|_| "enrol index out of range"))
        .transpose()?;
    let mut book = Vec::new();
    for (index, row) in rows.iter().enumerate() {
        if index < assigned || Some(index) == enrol_index {
            let bytes = hex_exact(row.as_str().ok_or("book row")?, 32, "book row")?;
            book.push(json!({"index":index,"address":base58(&bytes)}));
        }
    }
    if let Some(index) = enrol_index {
        if index >= rows.len() {
            return Err("--enrol-index names no book row".into());
        }
    }
    let mut config = json!({
        "asset": {
            "mint": base58(&hex_exact(&text(tariff, "mint")?, 32, "mint")?),
            "tokenProgram": base58(&hex_exact(&text(tariff, "tokenProgram")?, 32, "tokenProgram")?),
        },
        "book": book,
        "receiptsDir": utf8_path(&session.receipts_dir())?,
    });
    for (field, value) in [
        ("minEndpoints", options.min_endpoints),
        ("maxPages", options.max_pages),
        ("pageSize", options.page_size),
    ] {
        if let Some(value) = value {
            config[field] = json!(value as u64);
        }
    }
    if let Some((index, floor)) = options.enrol {
        config["enrol"] = json!({"index":index as u64,"journalFloor":floor as u64,
            "cursorFile":utf8_path(&session.pay_dir().join("enrol-cursor.json"))?});
    }
    let mut bytes = serde_json::to_vec_pretty(&config).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let temporary = out.with_extension("tmp");
    let _ = fs::remove_file(&temporary);
    create_private(&temporary, &bytes)?;
    fs::rename(&temporary, out)
        .map_err(|error| format!("cannot install {}: {error}", out.display()))?;
    println!("{}", out.display());
    Ok(())
}

// ---------------------------------------------------------------- pay observe

/// One watcher record: the value as emitted (retained whole), and the pair its nullifier and
/// receipt name bind.
#[derive(Clone)]
struct Record {
    value: Value,
    signature: String,
    address: String,
    index: u128,
    amount: u128,
}

impl Record {
    fn parse(value: &Value) -> Result<Self> {
        let signature = text(value, "signature")?;
        let address = text(value, "address")?;
        hex_exact(&signature, 64, "record signature")?;
        hex_exact(&address, 32, "record address")?;
        Ok(Record {
            index: number(value, "index")?,
            amount: number(value, "amount")?,
            value: value.clone(),
            signature,
            address,
        })
    }

    fn name(&self) -> String {
        format!("{}.{}", self.signature, self.address)
    }

    /// The report's record (`DREGG/PAY/OBSERVATION/v2`): the watcher's fields as emitted,
    /// `memo` and `memoError` included.
    fn kernel(&self) -> Value {
        self.value.clone()
    }

    fn short(&self) -> String {
        format!("{}…", &self.signature[..16])
    }
}

#[derive(Default)]
struct Tally {
    reports: usize,
    credited: usize,
    already: usize,
    quarantined: usize,
    waiting: Option<String>,
    /// Self-enrollment submissions and the kernel's decisions (PAY §11).
    enrol_submissions: usize,
    enrolled: usize,
    renewed: usize,
    journalled: usize,
    claims_retained: usize,
    /// Enrollment-index records still undecided when this run stopped (the tip was spent).
    enrol_pending: usize,
}

struct Tip {
    value: Value,
    slot: u128,
}

fn tip_of(file: &Value) -> Result<Tip> {
    let value = file.get("tip").ok_or("observations file lacks tip")?.clone();
    let slot = number(&value, "slot")?;
    number(&value, "blockTime")?;
    Ok(Tip { value, slot })
}

fn clock_slot(view: &Value) -> Result<u128> {
    view.get("clock")
        .filter(|clock| !clock.is_null())
        .ok_or_else(|| "the pay cell has no clock".to_owned())
        .and_then(|clock| number(clock, "slot"))
}

fn receipt_path(session: &Session, record: &Record) -> PathBuf {
    session.receipts_dir().join(record.name())
}

/// Record that the kernel decided `record` in `attempt`: a symlink named by the transfer, to
/// the attempt. The first decider wins; a second link for the same transfer is not made.
fn receipt(session: &Session, record: &Record, attempt: &Path) -> Result<()> {
    let path = receipt_path(session, record);
    if fs::symlink_metadata(&path).is_ok() {
        return Ok(());
    }
    symlink(attempt, &path)
        .map_err(|error| format!("cannot write receipt {}: {error}", path.display()))?;
    File::open(session.receipts_dir())
        .and_then(|directory| directory.sync_all())
        .map_err(|error| format!("cannot sync receipts: {error}"))
}

fn quarantine(session: &Session, record: &Record, attempt: &Path, reason: &str) -> Result<()> {
    let path = session
        .quarantine_dir()
        .join(format!("{}.json", record.name()));
    if !path.exists() {
        retain_json(
            &path,
            &json!({"type":"minidregg-pay-quarantine-v1","reason":reason,
                "attempt":utf8_path(attempt)?,"record":record.value}),
        )?;
    }
    Ok(())
}

fn report_command(
    session: &Session,
    capability: &str,
    view: &Value,
    tip: &Tip,
    records: &[Record],
) -> Result<Value> {
    Ok(json!({"observer":session.subject,"capability":capability,
        "nonce":workspace::random_nonce()?,
        "expectedAuthorityRoot":text(view, "authorityRoot")?,
        "expectedPayRoot":text(view, "payRoot")?,
        "tip":tip.value,
        "observations":records.iter().map(Record::kernel).collect::<Vec<_>>()}))
}

/// Build (and retain) one report over `records` at `tip`, re-reading the pay view first:
/// every report writes the pay cell, so the root it pins must be read immediately before.
fn build_report(
    session: &Session,
    capability: &str,
    tip: &Tip,
    records: &[Record],
) -> Result<(PathBuf, Value)> {
    let attempt = session.new_attempt(&format!("report-{}", tip.slot))?;
    let view = read_view(session, &attempt)?;
    retain_json(
        &attempt.join("records.json"),
        &json!({"tip":tip.value,
            "observations":records.iter().map(|record| record.value.clone()).collect::<Vec<_>>()}),
    )?;
    let command = report_command(session, capability, &view, tip, records)?;
    prepare(session, &attempt, "pay-observation", &command, OBSERVE_OPS)?;
    Ok((attempt, view))
}

fn retained_records(attempt: &Path) -> Result<Vec<Record>> {
    let value = workspace::bounded_json(&attempt.join("records.json"))?;
    value
        .get("observations")
        .and_then(Value::as_array)
        .ok_or("retained report lacks its observations")?
        .iter()
        .map(Record::parse)
        .collect()
}

fn credited(session: &Session, attempt: &Path, records: &[Record], tally: &mut Tally) -> Result<()> {
    for record in records {
        receipt(session, record, attempt)?;
        println!(
            "credited\t{}\t{}\t{}\t{}",
            record.index,
            record.short(),
            record.amount,
            attempt.display()
        );
        tally.credited += 1;
    }
    if records.is_empty() {
        println!("heartbeat\t{}", attempt.display());
    }
    Ok(())
}

/// Settle every report whose submit answer was lost (the process died, or the transport
/// failed): a confirmed lookup is a credit and gets its receipts; `absent` means the Host never
/// accepted it, and its records are simply observed again. A confirmed report whose receipts
/// were not all written (a crash between the outcome and the links) is completed here too.
fn resolve_pending(session: &Session, tally: &mut Tally) -> Result<()> {
    resolve_pending_enrolments(session, tally)?;
    for attempt in pay_attempts(session, "report")? {
        match decision(&attempt).as_deref() {
            Some("credited") => {
                for record in retained_records(&attempt)? {
                    receipt(session, &record, &attempt)?;
                }
                continue;
            }
            Some(_) => continue,
            None => {}
        }
        if !attempt.join("submit-marker.json").exists() {
            continue;
        }
        let records = retained_records(&attempt)?;
        let result = lookup(session, &attempt, OBSERVE_OPS)?;
        match &result {
            Answer::Confirmed(_) => {
                decide(&attempt, "credited", &result)?;
                println!("resolved\t{}\tconfirmed by lookup", attempt.display());
                credited(session, &attempt, &records, tally)?;
            }
            Answer::Undecided(detail) if detail.starts_with("absent") => {
                decide(&attempt, "absent", &result)?;
                println!("resolved\t{}\tabsent: observed again", attempt.display());
            }
            _ => {
                println!("undecided\t{}\t{}", attempt.display(), result.render());
                set_exit(4);
            }
        }
    }
    Ok(())
}

enum Step {
    /// The tip was consumed by an accepted report (a credit or a heartbeat).
    Done,
    /// The tip is still unspent; observe again with what is left.
    Again,
    /// Stop this tick (waiting, refused, or undecided).
    Stop,
}

/// Submit a report and act on the Host's answer.
fn report_once(
    session: &Session,
    capability: &str,
    tip: &Tip,
    records: &[Record],
    tally: &mut Tally,
) -> Result<(Answer, PathBuf, Value)> {
    let (attempt, view) = build_report(session, capability, tip, records)?;
    tally.reports += 1;
    let result = submit_once(session, &attempt, OBSERVE_OPS)?;
    Ok((result, attempt, view))
}

fn waiting(tally: &mut Tally, reason: &str, tip: &Tip, view: &Value) {
    let clock = clock_slot(view)
        .map(|slot| slot.to_string())
        .unwrap_or_else(|_| "?".into());
    println!("waiting\t{reason}\ttip {} clock {clock}", tip.slot);
    tally.waiting = Some(reason.into());
}

/// Probe `records` one per report, in order, after a whole report was refused by a reason
/// that one of them caused (a spent nullifier, or a per-observation refusal the client cannot
/// attribute from the batch). A refused report consumes nothing, so probing is free until one
/// is accepted; that one consumes the tip, and the rest wait for the next tick.
fn probe(
    session: &Session,
    capability: &str,
    tip: &Tip,
    records: &[Record],
    tally: &mut Tally,
) -> Result<Step> {
    for record in records {
        let mut stale = false;
        loop {
            let single = std::slice::from_ref(record);
            let (result, attempt, view) = report_once(session, capability, tip, single, tally)?;
            match (&result, result.reason()) {
                (Answer::Confirmed(_), _) => {
                    decide(&attempt, "credited", &result)?;
                    credited(session, &attempt, single, tally)?;
                    return Ok(Step::Done);
                }
                (_, Some("alreadyConsumed")) if clock_slot(&view)? == tip.slot => {
                    decide(&attempt, "waiting", &result)?;
                    waiting(tally, "tipReported", tip, &view);
                    return Ok(Step::Stop);
                }
                (_, Some(reason))
                    if reason == "alreadyConsumed" || PER_OBSERVATION.contains(&reason) =>
                {
                    settle_one(session, record, &attempt, &result, reason, tally)?;
                }
                (_, Some("stalePay" | "staleAuthority")) if !stale => {
                    decide(&attempt, "retried", &result)?;
                    stale = true;
                    continue;
                }
                (_, Some(reason @ ("tickTooSoon" | "tipBehindClock"))) => {
                    decide(&attempt, "waiting", &result)?;
                    waiting(tally, reason, tip, &view);
                    return Ok(Step::Stop);
                }
                _ => return stop(&attempt, &result),
            }
            break;
        }
    }
    Ok(Step::Again)
}

/// A one-record report refused because of that record: a spent nullifier (at a tip newer than
/// the clock) means it was already credited, and gets its receipt; a per-observation reason
/// quarantines it.
fn settle_one(
    session: &Session,
    record: &Record,
    attempt: &Path,
    result: &Answer,
    reason: &str,
    tally: &mut Tally,
) -> Result<()> {
    if reason == "alreadyConsumed" {
        decide(attempt, "alreadyCredited", result)?;
        receipt(session, record, attempt)?;
        println!(
            "already-credited\t{}\t{}\tkernel\t{}",
            record.index,
            record.short(),
            attempt.display()
        );
        tally.already += 1;
    } else {
        decide(attempt, "quarantined", result)?;
        quarantine(session, record, attempt, reason)?;
        println!(
            "quarantined\t{}\t{}\t{reason}\t{}",
            record.index,
            record.short(),
            attempt.display()
        );
        tally.quarantined += 1;
        set_exit(3);
    }
    Ok(())
}

fn stop(attempt: &Path, result: &Answer) -> Result<Step> {
    match result {
        Answer::Undecided(_) => {
            println!("undecided\t{}\t{}", attempt.display(), result.render());
            set_exit(4);
        }
        _ => {
            decide(attempt, "refused", result)?;
            println!("refused\t{}\t{}", attempt.display(), result.render());
            set_exit(3);
        }
    }
    Ok(Step::Stop)
}

/// The watcher's submit path: every record read at one tip goes into ONE report (the tick
/// nullifier spends the tip slot, so an accepted report is the only one at that tip).
fn observe(
    session: &Session,
    capability: &str,
    enrol_capability: Option<&str>,
    file: &Value,
    hold: bool,
) -> Result<()> {
    let mut tally = Tally::default();
    resolve_pending(session, &mut tally)?;
    let tip = tip_of(file)?;
    let mut records: Vec<Record> = Vec::new();
    for value in file
        .get("observations")
        .and_then(Value::as_array)
        .ok_or("observations file lacks observations")?
    {
        let record = Record::parse(value)?;
        if records.iter().any(|seen| seen.name() == record.name()) {
            continue;
        }
        if fs::symlink_metadata(receipt_path(session, &record)).is_ok() {
            println!(
                "already-credited\t{}\t{}\treceipt",
                record.index,
                record.short()
            );
            tally.already += 1;
            continue;
        }
        records.push(record);
    }
    // Route by the tariff's enrollment index: those records go to the self-enrollment
    // receiver one at a time; the observation receiver would refuse a report carrying one.
    let enrol_index = if records.is_empty() {
        None
    } else {
        enrol_index_of(&scratch_view(session)?)?
    };
    let (enrol, records): (Vec<Record>, Vec<Record>) = records
        .into_iter()
        .partition(|record| Some(record.index) == enrol_index);
    if hold {
        let (attempt, _) = build_report(session, capability, &tip, &records)?;
        println!("held\t{}\t{} record(s)", attempt.display(), records.len());
        return Ok(());
    }
    // Ordinary records first, exactly as before. With none and an enrollment record waiting,
    // the enrollment is this tip's submission (it advances the clock as a heartbeat would).
    let step = if records.is_empty() && !enrol.is_empty() {
        Step::Again
    } else {
        observe_records(session, capability, &tip, records, &mut tally, None)?
    };
    let step = match (step, enrol.is_empty()) {
        (step, true) => step,
        (Step::Again, false) => match enrol_capability {
            Some(enrol_capability) => {
                enrol_records(session, enrol_capability, &tip, &enrol, &mut tally)?
            }
            None => {
                for record in &enrol {
                    println!(
                        "enrol-unconfigured\t{}\t{}\tneeds --enrol-capability and --operator-socket",
                        record.index,
                        record.short()
                    );
                }
                tally.enrol_pending = enrol.len();
                tally.waiting = Some("enrolUnconfigured".into());
                set_exit(3);
                Step::Stop
            }
        },
        (step, false) => {
            // The tip is spent (or this tick stopped): every enrollment record waits for the
            // next tip. The tick script asks the watcher again while this line appears.
            tally.enrol_pending = enrol.len();
            step
        }
    };
    if tally.enrol_pending > 0 {
        println!("enrol-pending\t{}\tnext tip", tally.enrol_pending);
    }
    summary(&tip, &tally, step);
    Ok(())
}

// ---------------------------------------------------------------- self-enrollment (PAY §11)

/// The tariff's enrollment index, from the public pay view; `None` = self-enrollment off.
fn enrol_index_of(view: &Value) -> Result<Option<u128>> {
    let Some(tariff) = view.get("tariff").filter(|tariff| !tariff.is_null()) else {
        return Ok(None);
    };
    match tariff.get("enrolIndex") {
        None | Some(Value::Null) => Ok(None),
        Some(_) => number(tariff, "enrolIndex").map(Some),
    }
}

/// Read the public enrollment view (op 112) into `directory/STEM.{bin,json}`.
fn read_enrolment_view(session: &Session, directory: &Path, stem: &str) -> Result<Value> {
    let frame = session.call(ENROLMENT_VIEW_OP, &[])?;
    let body = frame_body(&frame, ENROLMENT_VIEW_OP)?;
    let bin = directory.join(format!("{stem}.bin"));
    create_private(&bin, body)?;
    session.inspect("pay-enrolment-view", &bin, &directory.join(format!("{stem}.json")))
}

/// The Mini key a record's memo names, as the Host's own codec reads it; `None` when the
/// record carries no memo or the memo does not parse (the kernel journals those).
fn memo_key(session: &Session, record: &Record, directory: &Path) -> Result<Option<String>> {
    let Some(memo) = record.value.get("memo").and_then(Value::as_str) else {
        return Ok(None);
    };
    let bin = directory.join("memo.bin");
    if !bin.exists() {
        create_private(&bin, &decode_hex(memo)?)?;
    }
    let parsed = session.inspect("pay-enrol-memo", &bin, &directory.join("memo.json"))?;
    Ok(if parsed.get("accepted").and_then(Value::as_bool) == Some(true) {
        Some(text(&parsed, "miniKey")?)
    } else {
        None
    })
}

/// Extract only the stable identity from the exact canonical v2 memo. This
/// selects a read-only source lookup; it is not signature verification or an
/// admission decision. Confirmed op119/120 plus op181 own those facts.
fn v2_memo_identity(record: &Record) -> Result<Option<String>> {
    let Some(encoded) = record.value.get("memo").and_then(Value::as_str) else {
        return Ok(None);
    };
    let bytes = decode_hex(encoded)?;
    let Ok(text) = std::str::from_utf8(&bytes) else { return Ok(None); };
    Ok(crate::pay_memo_v2::SignedMemo::parse(text).ok()
        .map(|memo| hex(&memo.unsigned.identity_key)))
}

fn v2_status_request(record: &Record, identity: &str) -> Value {
    json!({"identityKey":identity, "signature":record.signature,
        "originalRecipient":record.address})
}

fn v2_enrol_classification(record: &Record, status: &crate::pay_status::Status)
    -> Result<(&'static str, Value)> {
    use crate::pay_status::{Authorization, Mode, Payment};
    let coordinates = status.payment.coordinates()
        .ok_or("confirmed v2 observation lacks an exact source payment decision")?;
    if !coordinates.amount_atomic.matches_u128(record.amount)
        || !coordinates.index.matches_u128(record.index)
        || !coordinates.slot.matches_u128(number(&record.value, "slot")?) {
        return Err("source payment coordinates differ from retained observation".into());
    }
    let decision = match &status.payment {
        Payment::Pending(_) => "claimRetained",
        Payment::Consumed(value) => match value.authorization {
            // A later acceptance may already exist when recovering the original
            // observer receipt. Its mint belongs to that independent operation.
            Authorization::AcceptCurrentQuote => "claimRetained",
            Authorization::OriginalMemo => match value.mode {
                Mode::Enrol => "enrolled", Mode::Renew => "renewed",
            },
        },
        Payment::JournalNegative(_) => "journalled",
        Payment::NotRequested | Payment::Unknown => unreachable!("no coordinates"),
    };
    let detail = json!({"miniKey":hex(&status.identity_key),
        "sourceStatus":status.raw, "reason":status.raw["payment"]["reason"],
        "amount":coordinates.amount_atomic.as_str(),
        "subject":status.raw["entry"]["subject"],
        "lease":{"expiresAt":status.raw["entry"]["leaseUntil"]},
        "index":status.raw["entry"]["index"],
        "message":status.pending_message().unwrap_or_else(||
            if decision == "claimRetained" {
                "Payment received; a later claim acceptance consumed it. Do not send this deposit again.".into()
            } else { String::new() })});
    Ok((decision, detail))
}

fn v2_enrol_decision(session: &Session, attempt: &Path, record: &Record)
    -> Result<Option<(&'static str, Value)>> {
    let Some(identity) = v2_memo_identity(record)? else { return Ok(None); };
    let request = v2_status_request(record, &identity);
    let path = attempt.join("enrol-status-v2.json");
    let value = if path.exists() {
        workspace::bounded_json(&path)?
    } else {
        let payload = serde_json::to_vec(&request).map_err(|e| e.to_string())?;
        let frame = session.call(181, &payload)?;
        let body = frame_body(&frame, 181)?;
        if body.len() > 8192 { return Err("source paid status exceeds its bound".into()); }
        serde_json::from_slice(body).map_err(|e| format!("invalid source paid status: {e}"))?
    };
    let status = crate::pay_status::parse(&value, &request)?;
    let classified = v2_enrol_classification(record, &status)?;
    // Once published, use this exact status on recovery. Never replace an
    // observer's zero-mint decision with a later claim's independent mint.
    publish_decision_json(&path, &status.raw)?;
    Ok(Some(classified))
}

/// What the kernel decided for a CONFIRMED self-enrollment, read back from the enrollment
/// view the Host serves: a journal row named by the transfer, or the memo key's entry (new
/// = enrolled, present before = renewed). The client does not re-derive the decision.
fn enrol_decided(
    session: &Session,
    attempt: &Path,
    record: &Record,
    result: &Answer,
    tally: &mut Tally,
) -> Result<()> {
    let (decision, detail) = if let Some(classified) = v2_enrol_decision(session, attempt, record)? {
        classified
    } else {
    let after = read_enrolment_view(session, attempt, "enrolment-after")?;
    let before = workspace::bounded_json(&attempt.join("enrolment-before.json"))?;
    let journal = after
        .get("journal")
        .and_then(Value::as_array)
        .and_then(|rows| {
            rows.iter().find(|row| {
                row.get("signature").and_then(Value::as_str) == Some(record.signature.as_str())
                    && row.get("address").and_then(Value::as_str) == Some(record.address.as_str())
            })
        });
    let entry_of = |view: &Value, key: &str| -> Option<Value> {
        view.get("entries")?
            .as_array()?
            .iter()
            .find(|entry| entry.get("miniKey").and_then(Value::as_str) == Some(key))
            .cloned()
    };
    match journal {
        Some(row) => (
            "journalled",
            json!({"reason": row.get("reason"), "amount": row.get("amount")}),
        ),
        None => {
            let key = memo_key(session, record, attempt)?
                .ok_or("a confirmed self-enrollment with no journal row names no Mini key")?;
            let entry = entry_of(&after, &key)
                .ok_or("a confirmed self-enrollment is in neither the journal nor the entries")?;
            let decision = if entry_of(&before, &key).is_some() {
                "renewed"
            } else {
                "enrolled"
            };
            (
                decision,
                json!({"miniKey": key, "subject": entry.get("subject"), "lease": entry.get("lease"),
                    "index": entry.get("index")}),
            )
        }
    }
    };
    publish_decision_json(
        &attempt.join("enrol.json"),
        &json!({"type":"minidregg-pay-enrol-decision-v1","decision":decision,"detail":detail}),
    )?;
    decide(attempt, decision, result)?;
    receipt(session, record, attempt)?;
    match decision {
        "journalled" => tally.journalled += 1,
        "renewed" => tally.renewed += 1,
        "claimRetained" => tally.claims_retained += 1,
        _ => tally.enrolled += 1,
    }
    let shown = match decision {
        "claimRetained" => text(&detail, "message")?,
        "journalled" => detail
            .get("reason")
            .and_then(Value::as_str)
            .unwrap_or("?")
            .to_owned(),
        _ => format!(
            "subject {} expiresAt {}",
            detail.get("subject").and_then(Value::as_str).unwrap_or("?"),
            detail
                .get("lease")
                .and_then(|lease| lease.get("expiresAt"))
                .map(Value::to_string)
                .unwrap_or_else(|| "none".into())
        ),
    };
    println!(
        "{decision}\t{}\t{}\t{shown}\t{}",
        record.index,
        record.short(),
        attempt.display()
    );
    Ok(())
}

/// Refusals of the self-enrollment receiver that one record caused and that consumed nothing:
/// the record is quarantined (no receipt: it is read again next tick) and the next record is
/// tried at the same tip.
fn enrol_record_refusal(reason: &str) -> bool {
    reason.starts_with("decision:")
        || matches!(
            reason,
            "keyTaken"
                | "observeGrantTaken"
                | "allocation"
                | "bookAdmission"
                | "birthShape"
                | "grantBatch"
                | "authorityEntries"
                | "renewalRecord"
        )
}

/// Submit the enrollment-index records ONE per submission (ops 117-120, operator socket) at
/// `tip`. The first confirmed decision spends the tip; the rest wait for the next one.
fn enrol_records(
    session: &Session,
    capability: &str,
    tip: &Tip,
    records: &[Record],
    tally: &mut Tally,
) -> Result<Step> {
    for (position, record) in records.iter().enumerate() {
        let mut stale = false;
        loop {
            let attempt = session.new_attempt(&format!("enrol-{}", tip.slot))?;
            let view = read_view(session, &attempt)?;
            read_enrolment_view(session, &attempt, "enrolment-before")?;
            retain_json(
                &attempt.join("records.json"),
                &json!({"tip":tip.value,"observations":[record.value]}),
            )?;
            let command = json!({"observer":session.subject,"capability":capability,
                "nonce":workspace::random_nonce()?,
                "expectedAuthorityRoot":text(&view, "authorityRoot")?,
                "expectedPayRoot":text(&view, "payRoot")?,
                "tip":tip.value,"observation":record.kernel()});
            prepare(session, &attempt, "pay-enrol", &command, ENROL_OPS)?;
            tally.enrol_submissions += 1;
            let result = submit_once(session, &attempt, ENROL_OPS)?;
            match (&result, result.reason()) {
                (Answer::Confirmed(_), _) => {
                    enrol_decided(session, &attempt, record, &result, tally)?;
                    tally.enrol_pending = records.len() - position - 1;
                    return Ok(Step::Done);
                }
                // At a tip equal to the clock the spent nullifier may be the tick's.
                (_, Some("alreadyConsumed")) if clock_slot(&view)? == tip.slot => {
                    decide(&attempt, "waiting", &result)?;
                    waiting(tally, "tipReported", tip, &view);
                    tally.enrol_pending = records.len() - position;
                    return Ok(Step::Stop);
                }
                // A newer tip's tick is unspent, so the spent nullifier is this transfer's:
                // the kernel decided it before (enrolled, renewed or journalled).
                (_, Some("alreadyConsumed")) => {
                    decide(&attempt, "alreadyDecided", &result)?;
                    receipt(session, record, &attempt)?;
                    println!(
                        "already-decided\t{}\t{}\tkernel\t{}",
                        record.index,
                        record.short(),
                        attempt.display()
                    );
                    tally.already += 1;
                }
                (_, Some("stalePay" | "staleAuthority")) if !stale => {
                    decide(&attempt, "retried", &result)?;
                    stale = true;
                    continue;
                }
                (_, Some("tipBehindClock")) => {
                    decide(&attempt, "waiting", &result)?;
                    waiting(tally, "tipBehindClock", tip, &view);
                    tally.enrol_pending = records.len() - position;
                    return Ok(Step::Stop);
                }
                // The native verifier failed: nothing was decided or consumed; retry next tick.
                (_, Some(reason)) if reason.starts_with("verifier:") => {
                    decide(&attempt, "waiting", &result)?;
                    waiting(tally, "verifierUnavailable", tip, &view);
                    tally.enrol_pending = records.len() - position;
                    set_exit(4);
                    return Ok(Step::Stop);
                }
                (_, Some(reason)) if enrol_record_refusal(reason) => {
                    decide(&attempt, "quarantined", &result)?;
                    quarantine(session, record, &attempt, reason)?;
                    println!(
                        "quarantined\t{}\t{}\t{reason}\t{}",
                        record.index,
                        record.short(),
                        attempt.display()
                    );
                    tally.quarantined += 1;
                    set_exit(3);
                }
                _ => {
                    tally.enrol_pending = records.len() - position;
                    return stop(&attempt, &result);
                }
            }
            break;
        }
    }
    Ok(Step::Again)
}

/// Settle every self-enrollment whose submit answer was lost (op 120), and re-derive the
/// receipts of every decided one.
fn resolve_pending_enrolments(session: &Session, tally: &mut Tally) -> Result<()> {
    for attempt in pay_attempts(session, "enrol")? {
        match decision(&attempt).as_deref() {
            Some("enrolled" | "renewed" | "journalled" | "claimRetained" | "alreadyDecided") => {
                for record in retained_records(&attempt)? {
                    receipt(session, &record, &attempt)?;
                }
                continue;
            }
            Some(_) => continue,
            None => {}
        }
        if !attempt.join("submit-marker.json").exists() {
            continue;
        }
        if session.operator_socket.is_none() {
            println!(
                "undecided\t{}\tself-enrollment lookup needs --operator-socket",
                attempt.display()
            );
            set_exit(4);
            continue;
        }
        let records = retained_records(&attempt)?;
        let record = records
            .first()
            .ok_or("a self-enrollment attempt retains no record")?;
        let result = lookup(session, &attempt, ENROL_OPS)?;
        match &result {
            Answer::Confirmed(_) => {
                println!("resolved\t{}\tconfirmed by lookup", attempt.display());
                enrol_decided(session, &attempt, record, &result, tally)?;
            }
            Answer::Undecided(detail) if detail.starts_with("absent") => {
                decide(&attempt, "absent", &result)?;
                println!("resolved\t{}\tabsent: observed again", attempt.display());
            }
            _ => {
                println!("undecided\t{}\t{}", attempt.display(), result.render());
                set_exit(4);
            }
        }
    }
    Ok(())
}

/// Submit a report built earlier with `--hold`, then carry on as `observe` would.
fn resume(session: &Session, capability: &str, attempt: &Path) -> Result<()> {
    let mut tally = Tally::default();
    let attempt = absolute(attempt)?;
    if !attempt.starts_with(session.root.join("attempts"))
        || attempt.join("submit-marker.json").exists()
        || decision(&attempt).is_some()
    {
        return Err("--resume takes a held, never-submitted report attempt of this workspace".into());
    }
    let retained = workspace::bounded_json(&attempt.join("records.json"))?;
    let tip = tip_of(&retained)?;
    let records = retained_records(&attempt)?;
    let view = workspace::bounded_json(&attempt.join("view.json"))?;
    tally.reports += 1;
    let result = submit_once(session, &attempt, OBSERVE_OPS)?;
    let step = observe_records(
        session,
        capability,
        &tip,
        records,
        &mut tally,
        Some((attempt, view, result)),
    )?;
    summary(&tip, &tally, step);
    Ok(())
}

fn summary(tip: &Tip, tally: &Tally, step: Step) {
    // The self-enrollment counts appear only when this run touched the enrollment index, so
    // a tick without one reads exactly as before.
    let enrol = if tally.enrol_submissions + tally.enrol_pending > 0 {
        format!(
            " enrol-submissions {} enrolled {} renewed {} journalled {} claims-retained {} enrol-pending {}",
            tally.enrol_submissions,
            tally.enrolled,
            tally.renewed,
            tally.journalled,
            tally.claims_retained,
            tally.enrol_pending
        )
    } else {
        String::new()
    };
    println!(
        "pay observe: tip {} reports {} credited {} already-credited {} quarantined {}{enrol}{}",
        tip.slot,
        tally.reports,
        tally.credited,
        tally.already,
        tally.quarantined,
        match (step, &tally.waiting) {
            (_, Some(reason)) => format!(" waiting {reason}"),
            (Step::Done, None) => " tip consumed".into(),
            _ => String::new(),
        }
    );
}

fn observe_records(
    session: &Session,
    capability: &str,
    tip: &Tip,
    mut records: Vec<Record>,
    tally: &mut Tally,
    mut first: Option<(PathBuf, Value, Answer)>,
) -> Result<Step> {
    let mut stale = false;
    for _ in 0..(2 * records.len() + 4) {
        let (attempt, view, result) = match first.take() {
            Some(submitted) => submitted,
            None => {
                let (result, attempt, view) =
                    report_once(session, capability, tip, &records, tally)?;
                (attempt, view, result)
            }
        };
        match (&result, result.reason()) {
            (Answer::Confirmed(_), _) => {
                decide(&attempt, "credited", &result)?;
                credited(session, &attempt, &records, tally)?;
                return Ok(Step::Done);
            }
            (_, Some("stalePay" | "staleAuthority")) if !stale => {
                decide(&attempt, "retried", &result)?;
                println!("stale\t{}\t{}", attempt.display(), result.render());
                stale = true;
            }
            (_, Some(reason @ ("tickTooSoon" | "tipBehindClock"))) => {
                decide(&attempt, "waiting", &result)?;
                waiting(tally, reason, tip, &view);
                return Ok(Step::Stop);
            }
            // The tick nullifier of a tip at the clock is spent by the report that set the
            // clock; a newer tip's cannot be, so there the spent nullifier is a record's.
            (_, Some("alreadyConsumed")) if clock_slot(&view)? == tip.slot => {
                decide(&attempt, "waiting", &result)?;
                waiting(tally, "tipReported", tip, &view);
                return Ok(Step::Stop);
            }
            // A report of one record is its own probe.
            (_, Some(reason))
                if records.len() == 1
                    && (reason == "alreadyConsumed" || PER_OBSERVATION.contains(&reason)) =>
            {
                settle_one(session, &records[0], &attempt, &result, reason, tally)?;
                records.clear();
            }
            (_, Some(reason))
                if !records.is_empty()
                    && (reason == "alreadyConsumed" || PER_OBSERVATION.contains(&reason)) =>
            {
                decide(&attempt, "probed", &result)?;
                println!("probing\t{}\t{} record(s): {reason}", attempt.display(), records.len());
                match probe(session, capability, tip, &records, tally)? {
                    Step::Again => records.clear(),
                    step => return Ok(step),
                }
            }
            _ => return stop(&attempt, &result),
        }
    }
    Err("pay observe did not settle within its report bound".into())
}

// ---------------------------------------------------------------- pay audit

/// The credit a confirmed report minted, from its retained records and the tariff of the view
/// it pinned (the report's expected pay root fixes the tariff it was decided under):
/// `creditFor amount = min amount maxPerObservation * creditPerAtomic` (PAY §2.3).
fn report_credit(attempt: &Path) -> Result<(u128, u128, usize)> {
    let view = workspace::bounded_json(&attempt.join("view.json"))?;
    let tariff = view
        .get("tariff")
        .filter(|tariff| !tariff.is_null())
        .ok_or("a credited report pinned no tariff")?;
    let cap = number(tariff, "maxPerObservation")?;
    let rate = number(tariff, "creditPerAtomic")?;
    let records = retained_records(attempt)?;
    let mut credit = 0u128;
    let mut residual = 0u128;
    for record in &records {
        credit += record.amount.min(cap) * rate;
        residual += record.amount.saturating_sub(cap);
    }
    Ok((credit, residual, records.len()))
}

/// The inventory identifies source origins, not separate mint events. Multiple
/// retained observer attempts for one transfer are reconciled exactly once.
fn v2_audit_origins(session: &Session) -> Result<Vec<(Record, String)>> {
    let mut origins = std::collections::BTreeMap::<String, (Record, String)>::new();
    for attempt in pay_attempts(session, "enrol")? {
        if !attempt.join("records.json").exists() { continue; }
        for record in retained_records(&attempt)? {
            let Some(identity) = v2_memo_identity(&record)? else { continue; };
            if let Some((prior, owner)) = origins.get(&record.name()) {
                if owner != &identity || prior.amount != record.amount || prior.index != record.index
                    || number(&prior.value, "slot")? != number(&record.value, "slot")? {
                    return Err("retained attempts disagree about one payment origin".into());
                }
            } else {
                origins.insert(record.name(), (record, identity));
            }
        }
    }
    Ok(origins.into_values().collect())
}

/// Bound each source row while reading, with no lifetime inventory ceiling.
fn audit_json_line(reader: &mut impl std::io::BufRead, hash: &mut sha2::Sha256) -> Result<Option<Value>> {
    let mut bytes = Vec::new();
    loop {
        let buffer = reader.fill_buf().map_err(|e|e.to_string())?;
        if buffer.is_empty() {
            return if bytes.is_empty() { Ok(None) } else { Err("source audit lacks final newline".into()) };
        }
        let end = buffer.iter().position(|b| *b == b'\n');
        let count = end.map_or(buffer.len(), |n|n+1);
        if bytes.len() + count > 8193 { return Err("source audit row exceeds bound".into()); }
        bytes.extend_from_slice(&buffer[..count]);
        reader.consume(count);
        if end.is_some() {
            hash.update(&bytes);
            return serde_json::from_slice(&bytes).map(Some).map_err(|e|format!("source audit JSON: {e}"));
        }
    }
}

struct PaidAudit {
    statuses: Vec<crate::pay_status::Status>,
    verified_ledger: Option<Value>,
}

/// Offline source audit performs full signed-history re-admission once and
/// derives every status plus the ledger from the same verified opened image.
fn v2_audit_source(session: &Session, origins: &[(Record, String)], offline: bool) -> Result<PaidAudit> {
    let requests: Vec<Value> = origins.iter().map(|(record, identity)| v2_status_request(record, identity)).collect();
    if !offline {
        let mut statuses = Vec::new();
        for request in &requests {
            let payload = serde_json::to_vec(request).map_err(|e|e.to_string())?;
            let frame = session.call(181, &payload)?;
            let bytes = frame_body(&frame, 181)?;
            if bytes.len() > 8192 { return Err("source paid status exceeds its bound".into()); }
            let value = serde_json::from_slice(bytes).map_err(|e|format!("source paid status: {e}"))?;
            statuses.push(crate::pay_status::parse(&value, request)?);
        }
        return Ok(PaidAudit { statuses, verified_ledger: None });
    }
    let directory = session.pay_dir().join(format!("audit-{}",workspace::random_nonce()?));
    workspace::make_private_dir(&directory)?;
    let input = directory.join("requests.jsonl");
    let output = directory.join("source-audit.jsonl");
    let mut input_bytes = Vec::new();
    for request in &requests {
        input_bytes.extend(serde_json::to_vec(request).map_err(|e|e.to_string())?);
        input_bytes.push(b'\n');
    }
    create_private(&input, &input_bytes)?;
    let host_sha = host_image_sha256(&session.host)?;
    let config_sha = hex(&sha2::Sha256::digest(fs::read(&session.config).map_err(|e|e.to_string())?));
    let result = Command::new(&session.host).arg(&session.config).arg("pay-claim-audit")
        .arg(&input).arg(&output).output().map_err(|e|format!("cannot run source paid audit: {e}"))?;
    create_private(&directory.join("stdout.txt"), &result.stdout)?;
    create_private(&directory.join("stderr.txt"), &result.stderr)?;
    if !result.status.success() {
        return Err(format!("source paid history audit refused; evidence retained at {}",directory.display()));
    }
    if host_image_sha256(&session.host)? != host_sha
        || hex(&sha2::Sha256::digest(fs::read(&session.config).map_err(|e|e.to_string())?)) != config_sha {
        return Err("Host or exact config changed during source paid audit".into());
    }
    let metadata = fs::symlink_metadata(&output).map_err(|e|e.to_string())?;
    if !metadata.file_type().is_file() {
        return Err("source paid audit file is not regular".into());
    }
    let mut reader = std::io::BufReader::new(fs::File::open(&output).map_err(|e|e.to_string())?);
    let mut source_hash = sha2::Sha256::new();
    let value = audit_json_line(&mut reader, &mut source_hash)?.ok_or("source audit lacks header")?;
    if value["type"] != "payClaimAudit" { return Err("source paid audit type mismatch".into()); }
    for field in ["domain","semantics","expectedSeed","auditedHeight","worldRoot"] {
        crate::pay_status::Nat::parse(&text(&value, field)?)?;
    }
    let mut statuses = Vec::new();
    for request in &requests {
        let row = audit_json_line(&mut reader, &mut source_hash)?.ok_or("source audit is truncated")?;
        statuses.push(crate::pay_status::parse(&row, request)?);
    }
    let footer = audit_json_line(&mut reader, &mut source_hash)?.ok_or("source audit lacks completion")?;
    if footer != json!({"type":"payClaimAuditComplete","origins":requests.len().to_string()})
        || audit_json_line(&mut reader, &mut source_hash)?.is_some() {
        return Err("source audit response count or completion mismatch".into());
    }
    publish_decision_json(&directory.join("provenance.json"),&json!({
        "type":"minidregg-source-paid-audit-v1","hostSha256":host_sha,"configSha256":config_sha,
        "sourceOutputSha256":hex(&source_hash.finalize()),
        "domain":value["domain"],"semantics":value["semantics"],"expectedSeed":value["expectedSeed"],
        "auditedHeight":value["auditedHeight"],"worldRoot":value["worldRoot"]}))?;
    println!("host-audit\tfully re-admitted {} accepted records; source image {}\t{}",
        text(&value,"auditedHeight")?,text(&value,"worldRoot")?,directory.display());
    Ok(PaidAudit { statuses, verified_ledger: Some(value["ledger"].clone()) })
}

fn consumed_origin_credit(record: &Record, status: &crate::pay_status::Status) -> Result<(u128, u128)> {
    use crate::pay_status::{Authorization, Payment};
    if let Some(coordinates) = status.payment.coordinates() {
        if !coordinates.amount_atomic.matches_u128(record.amount)
            || !coordinates.slot.matches_u128(number(&record.value,"slot")?)
            || !coordinates.index.matches_u128(record.index) {
            return Err("source audit origin differs from retained observation".into());
        }
    }
    match &status.payment {
        Payment::Consumed(value) => {
            let credit = value.minted_credit.to_u128()?;
            match value.authorization {
                Authorization::OriginalMemo => Ok((credit, 0)),
                Authorization::AcceptCurrentQuote => {
                    if value.accepted_request.is_none() { return Err("claim consumption lacks its accepted semantic request".into()); }
                    Ok((0, credit))
                },
            }
        },
        Payment::Pending(_) | Payment::JournalNegative(_) | Payment::Unknown => Ok((0,0)),
        Payment::NotRequested => Err("audit omitted exact payment locator".into()),
    }
}

fn verified_ledger_identity(session: &Session, now: &Value, credited: u128) -> Result<usize> {
    let genesis = workspace::bounded_json(&session.config.parent().ok_or("config has no directory")?
        .join("pay-ledger-genesis.json"))?;
    let well = |value:&Value| -> Result<i128> { text(value,"well")?.parse().map_err(|_|"ledger well is not an integer".into()) };
    let now = well(now)?;
    let genesis = well(&genesis)?;
    let credit = i128::try_from(credited).map_err(|_|"credited total exceeds audit range")?;
    let expected = genesis.checked_sub(credit).ok_or("audit well arithmetic overflow")?;
    let holds = now == expected;
    println!("ledger\twell_now={now}\twell_genesis={genesis}\tcredited={credit}\t{}",
        if holds { "identity holds on fully audited image" } else { "FINDING: identity fails" });
    Ok(usize::from(!holds))
}

fn audit(session: &Session, offline: bool) -> Result<()> {
    let v2_origins = v2_audit_origins(session)?;
    let source = if v2_origins.is_empty() { None }
        else { Some(v2_audit_source(session, &v2_origins, offline)?) };
    let mut credited = 0u128;
    let mut residual = 0u128;
    let mut transfers = 0usize;
    let mut findings = 0usize;
    for attempt in pay_attempts(session, "report")? {
        if decision(&attempt).as_deref() != Some("credited") {
            continue;
        }
        let (credit, over, count) = report_credit(&attempt)?;
        credited += credit;
        residual += over;
        transfers += count;
        if !offline {
            let result = lookup(session, &attempt, OBSERVE_OPS)?;
            let replayed = matches!(&result, Answer::Confirmed(value)
                if value.get("confirmation").and_then(Value::as_str) == Some("replayed"));
            if !replayed {
                findings += 1;
            }
            println!(
                "report\t{}\t{count} transfer(s)\t+{credit}\t{}",
                attempt.display(),
                if replayed { "journaled" } else { "FINDING: not journaled" }
            );
        }
    }
    // Self-enrollments: an enrolment or a renewal mints `creditFor amount` into the
    // enrollment float exactly as a credited report does; a journal row mints nothing. Each
    // decided submission must replay through op 120 (operator socket).
    for attempt in pay_attempts(session, "enrol")? {
        // V2 credit is read once from the immutable source consumption index,
        // including independent claim acceptance after this observer's receipt.
        if attempt.join("records.json").exists() && retained_records(&attempt)?.iter()
            .map(v2_memo_identity).collect::<Result<Vec<_>>>()?.iter().any(Option::is_some) {
            continue;
        }
        let decided = decision(&attempt);
        let minted = matches!(decided.as_deref(), Some("enrolled" | "renewed"));
        if !minted && decided.as_deref() != Some("journalled") {
            continue;
        }
        let (credit, over, count) = if minted {
            report_credit(&attempt)?
        } else {
            (0, 0, 1)
        };
        credited += credit;
        residual += over;
        transfers += count;
        if !offline {
            let result = lookup(session, &attempt, ENROL_OPS)?;
            let replayed = matches!(&result, Answer::Confirmed(value)
                if value.get("confirmation").and_then(Value::as_str) == Some("replayed"));
            if !replayed {
                findings += 1;
            }
            println!(
                "enrol\t{}\t{}\t+{credit}\t{}",
                attempt.display(),
                decided.as_deref().unwrap_or("?"),
                if replayed { "journaled" } else { "FINDING: not journaled" }
            );
        }
    }
    if let Some(source) = &source {
        let mut observer_credit = 0u128;
        let mut claim_credit = 0u128;
        for ((record, _), status) in v2_origins.iter().zip(&source.statuses) {
            let (observer, claim) = consumed_origin_credit(record, status)?;
            observer_credit = observer_credit.checked_add(observer).ok_or("observer credit audit overflow")?;
            claim_credit = claim_credit.checked_add(claim).ok_or("claim credit audit overflow")?;
            transfers += 1;
            println!("origin\t{}\t{}\tobserver+{observer}\tclaim+{claim}",
                record.name(),status.raw["payment"]["state"].as_str().unwrap_or("?"));
        }
        credited = credited.checked_add(observer_credit).and_then(|n|n.checked_add(claim_credit))
            .ok_or("total paid credit audit overflow")?;
        println!("v2 consumed origins\tobserver credit {observer_credit}\tindependent claim credit {claim_credit}");
    }
    let quarantined = fs::read_dir(session.quarantine_dir())
        .map_err(|error| error.to_string())?
        .count();
    println!(
        "credited {credited} over {transfers} transfer(s); over-cap residual {residual} atomic; \
         quarantined {quarantined}"
    );
    if offline {
        findings += if let Some(ledger) = source.as_ref().and_then(|e|e.verified_ledger.as_ref()) {
            verified_ledger_identity(session, ledger, credited)?
        } else { ledger_identity(session, credited)? };
    }
    if findings > 0 {
        set_exit(3);
        return Err(format!("pay audit: {findings} finding(s)"));
    }
    println!("pay audit: no findings");
    Ok(())
}

/// The ledger side, read by the Host from the Store (the Host must not be serving it):
/// `-well_now = -well_genesis + Σ credited` (`well_tracks_observed`), with the genesis ledger
/// `mini bootstrap` retained beside the pinned config, and the Host's own re-admission audit.
fn ledger_identity(session: &Session, credited: u128) -> Result<usize> {
    let scratch = session
        .pay_dir()
        .join(format!(".ledger-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&scratch)?;
    let ledger_path = scratch.join("pay-ledger.json");
    let ledger = Command::new(&session.host)
        .arg(&session.config)
        .arg("pay-ledger")
        .arg(&ledger_path)
        .output()
        .map_err(|error| format!("cannot run the Host: {error}"))?;
    if !ledger.status.success() {
        let _ = fs::remove_dir_all(&scratch);
        return Err(format!(
            "pay-ledger failed (is the Host still serving this Store?): {}",
            String::from_utf8_lossy(&ledger.stderr).trim()
        ));
    }
    let now = workspace::bounded_json(&ledger_path)?;
    let _ = fs::remove_dir_all(&scratch);
    let genesis_path = session
        .config
        .parent()
        .ok_or("pinned config has no directory")?
        .join("pay-ledger-genesis.json");
    let genesis = workspace::bounded_json(&genesis_path)?;
    let well = |value: &Value| -> Result<i128> {
        text(value, "well")?
            .parse::<i128>()
            .map_err(|_| "ledger well is not an integer".to_owned())
    };
    let (now_well, genesis_well) = (well(&now)?, well(&genesis)?);
    let credited = i128::try_from(credited).map_err(|_| "credited sum out of range")?;
    let holds = -now_well == -genesis_well + credited;
    println!(
        "ledger\t-well_now={}\t-well_genesis={}\tcredited={credited}\t{}",
        -now_well,
        -genesis_well,
        if holds { "identity holds" } else { "FINDING: identity fails" }
    );
    let audit = Command::new(&session.host)
        .arg(&session.config)
        .arg("audit")
        .output()
        .map_err(|error| format!("cannot run the Host: {error}"))?;
    let audited = audit.status.success();
    println!(
        "host-audit\t{}",
        if audited {
            String::from_utf8_lossy(&audit.stdout).trim().to_owned()
        } else {
            format!(
                "FINDING: {}",
                String::from_utf8_lossy(&audit.stderr).trim()
            )
        }
    );
    Ok(usize::from(!holds) + usize::from(!audited))
}

// ---------------------------------------------------------------- entry

fn read_observations(from: &OsStr) -> Result<Value> {
    let mut bytes = Vec::new();
    if from == "-" {
        io::stdin()
            .take(16 * 1024 * 1024)
            .read_to_end(&mut bytes)
            .map_err(|error| format!("cannot read observations from stdin: {error}"))?;
    } else {
        File::open(from)
            .and_then(|file| file.take(16 * 1024 * 1024).read_to_end(&mut bytes))
            .map_err(|error| format!("cannot read {}: {error}", Path::new(from).display()))?;
    }
    serde_json::from_slice(&bytes).map_err(|error| format!("invalid observations JSON: {error}"))
}

fn decimal_flag(args: &mut Args, name: &str) -> Result<Option<u128>> {
    args.optional(name)
        .map(|value| {
            let value = value
                .into_string()
                .map_err(|_| format!("--{name} must be UTF-8"))?;
            number(&json!({ "v": value }), "v").map_err(|_| format!("--{name} must be a decimal"))
        })
        .transpose()
}

fn capability(args: &mut Args) -> Result<String> {
    let value = args
        .required("capability")?
        .into_string()
        .map_err(|_| "--capability must be UTF-8")?;
    number(&json!({ "v": value }), "v").map_err(|_| "--capability must be a decimal")?;
    Ok(value)
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "pay action must be UTF-8")?;
    // P6's purse refill is signed by a Book account's owner key, not run from a workspace.
    if action == "refill" {
        return crate::pay_refill::run(args);
    }
    let root = path(args.required("dir")?);
    // The owner-private operator socket of the same Host: the observer's only route to the
    // self-enrollment ops 117-120 (`mini serve --operator-socket`).
    let operator_socket = args
        .optional("operator-socket")
        .map(|socket| absolute(&path(socket)))
        .transpose()?;
    let open = |root: &Path| -> Result<Session> {
        let mut session = Session::open(root)?;
        session.operator_socket = operator_socket.clone();
        Ok(session)
    };
    let account = args
        .optional("account")
        .map(|value| value.into_string().map_err(|_| "--account must be UTF-8"))
        .transpose()?;
    match action.as_str() {
        "address" | "status" => {
            args.finish()?;
            let session = Session::open(&root)?;
            if action == "address" {
                address(&session, account.as_deref())
            } else {
                status(&session, account.as_deref())
            }
        }
        "book" => {
            let source = path(args.required("source")?);
            args.finish()?;
            book(&Session::open(&root)?, &source)
        }
        "watch-config" => {
            let out = absolute(&path(args.required("out")?))?;
            let options = WatchOptions {
                min_endpoints: decimal_flag(&mut args, "min-endpoints")?,
                max_pages: decimal_flag(&mut args, "max-pages")?,
                page_size: decimal_flag(&mut args, "page-size")?,
                enrol: match (
                    decimal_flag(&mut args, "enrol-index")?,
                    decimal_flag(&mut args, "journal-floor")?,
                ) {
                    (Some(index), Some(floor)) => Some((index, floor)),
                    (None, None) => None,
                    _ => return Err("--enrol-index and --journal-floor go together".into()),
                },
            };
            args.finish()?;
            watch_config(&Session::open(&root)?, &out, options)
        }
        "observe" => {
            let capability = capability(&mut args)?;
            let enrol_capability = args
                .optional("enrol-capability")
                .map(|value| {
                    let value = value
                        .into_string()
                        .map_err(|_| "--enrol-capability must be UTF-8")?;
                    number(&json!({ "v": value }), "v")
                        .map_err(|_| "--enrol-capability must be a decimal")?;
                    Ok::<_, String>(value)
                })
                .transpose()?;
            if enrol_capability.is_some() != operator_socket.is_some() {
                return Err("--enrol-capability and --operator-socket go together".into());
            }
            let resume_attempt = args.optional("resume").map(path);
            let from = args.optional("from");
            let hold = args.optional("hold").is_some_and(|value| value == "true");
            args.finish()?;
            let session = open(&root)?;
            match (resume_attempt, from) {
                (Some(attempt), None) if !hold => resume(&session, &capability, &attempt),
                (None, Some(from)) => observe(
                    &session,
                    &capability,
                    enrol_capability.as_deref(),
                    &read_observations(&from)?,
                    hold,
                ),
                _ => Err("pay observe takes --from FILE|- [--hold true], or --resume ATTEMPT".into()),
            }
        }
        "heartbeat" => {
            let capability = capability(&mut args)?;
            let slot = decimal_flag(&mut args, "slot")?.ok_or("missing --slot")?;
            let block_time = decimal_flag(&mut args, "block-time")?.ok_or("missing --block-time")?;
            args.finish()?;
            let file = json!({"tip":{"slot":slot as u64,"blockTime":block_time as u64},
                "observations":[]});
            observe(&open(&root)?, &capability, None, &file, false)
        }
        "audit" => {
            let offline = args.optional("offline").is_some_and(|value| value == "true");
            args.finish()?;
            let session = if offline { Session::open_for_audit(&root, true)? } else { open(&root)? };
            audit(&session, offline)
        }
        other => Err(format!(
            "unknown pay action {other}: address|status|book|watch-config|observe|heartbeat|audit|refill"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source_status_fixture(payment: Value) -> (Record, crate::pay_status::Status) {
        let record = Record::parse(&json!({"signature":hex(&[1;64]),"address":hex(&[2;32]),
            "amount":"522","index":"0","slot":"99"})).unwrap();
        let request = v2_status_request(&record, &hex(&[3;32]));
        let source = crate::pay_status::fixture(&request, payment);
        (record, crate::pay_status::parse(&source, &request).unwrap())
    }

    #[test]
    fn exact_pending_origin_is_decided_without_mint_or_membership_inference() {
        let (record, status) = source_status_fixture(json!({"state":"pendingV2",
            "amountAtomic":"522","slot":"99","index":"0","reason":"termsStale"}));
        let (decision, detail) = v2_enrol_classification(&record, &status).unwrap();
        assert_eq!(decision, "claimRetained");
        assert!(detail["message"].as_str().unwrap().contains("do not pay again"));
        for field in ["amount", "slot", "index"] {
            let mut changed = record.value.clone();
            changed[field] = json!("1");
            assert!(v2_enrol_classification(&Record::parse(&changed).unwrap(), &status).is_err());
        }
    }

    #[test]
    fn later_claim_acceptance_never_becomes_original_observer_mint() {
        let payment = json!({"state":"consumedV2","amountAtomic":"522","slot":"99","index":"0",
            "mode":"enrol","weeks":"1","mintedCredit":"522","birthFee":"7",
            "membershipCredit":"168","creditedRemainder":"347","pricingCommitment":hex(&[4;32]),
            "authorization":"originalMemo","acceptedRequest":null});
        let (record, original) = source_status_fixture(payment.clone());
        assert_eq!(v2_enrol_classification(&record, &original).unwrap().0, "enrolled");
        let mut payment = payment;
        payment["authorization"] = json!("acceptCurrentQuote");
        payment["acceptedRequest"] = json!("01");
        let (_, later) = source_status_fixture(payment);
        assert_eq!(v2_enrol_classification(&record, &later).unwrap().0, "claimRetained");
    }

    #[test]
    fn decision_publication_survives_stages_and_refuses_replacement() {
        let root = std::env::temp_dir().join(format!("mini-pay-decision-{}",workspace::random_nonce().unwrap()));
        workspace::make_private_dir(&root).unwrap();
        create_private(&root.join(".decision-stage-interrupted.json"), b"{partial").unwrap();
        let path = root.join("enrol-status-v2.json");
        let original = json!({"origin":"exact","state":"pendingV2"});
        publish_decision_json(&path, &original).unwrap();
        publish_decision_json(&path, &original).unwrap();
        assert!(publish_decision_json(&path, &json!({"origin":"other"})).is_err());
        assert_eq!(workspace::bounded_json(&path).unwrap(), original);
        assert!(root.join(".decision-stage-interrupted.json").exists());
        decide(&root, "claimRetained", &Answer::Undecided("fixture".into())).unwrap();
        decide(&root, "claimRetained", &Answer::Undecided("replayed fixture".into())).unwrap();
        assert!(decide(&root, "enrolled", &Answer::Undecided("fixture".into())).is_err());
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn a_blind_refusal_reads_undisclosed_and_names_nothing_else() {
        let blind = json!({"type":"refused","reason":"undisclosed",
            "phase":hex("admission".as_bytes()),"detail":hex("request refused".as_bytes())});
        let answer = answer(blind);
        assert_eq!(answer.reason(), Some("undisclosed"));
        assert_eq!(answer.render(), "refused undisclosed (phase admission)");
    }

    #[test]
    fn refusal_reasons_are_read_from_the_hosts_rendering_only() {
        assert_eq!(
            refusal_reason("pay-observation", "Minidregg.Kernel.PayObservation.Reject.stalePay"),
            Some("stalePay".into())
        );
        assert_eq!(
            refusal_reason(
                "pay-assign",
                "Minidregg.Kernel.PayAssignmentReceiver.Reject.signature (x)"
            ),
            Some("signature".into())
        );
        assert_eq!(refusal_reason("durable", ALREADY_CONSUMED), Some("alreadyConsumed".into()));
        // As the Host actually renders it: wrapped by Lean's pretty-printer.
        assert_eq!(
            refusal_reason(
                "durable",
                "Minidregg.Kernel.DurableDataIntent.RejectReason.durable\n  \
                 (Minidregg.Kernel.DurableCommitProtocol.RejectReason.alreadyConsumed)"
            ),
            Some("alreadyConsumed".into())
        );
        // The same text under another phase, prose naming a reason, and a longer identifier are
        // not reasons.
        assert_eq!(refusal_reason("pay-observation", ALREADY_CONSUMED), None);
        assert_eq!(refusal_reason("pay-observation", "the report was stalePay"), None);
        assert_eq!(
            refusal_reason("x", "Minidregg.Kernel.PayObservation.Reject.stalePay.extra"),
            None
        );
    }

    #[test]
    fn self_enrollment_refusals_name_the_decision_and_the_verifier() {
        // As J-PAY-E3's Host rendered them (phase pay-enrol).
        assert_eq!(
            refusal_reason(
                "pay-enrol",
                "Minidregg.Kernel.PayEnrolReceiver.Reject.decision \
                 (Minidregg.Kernel.PayEnrolDecision.Reject.belowJournalFloor)"
            ),
            Some("decision:belowJournalFloor".into())
        );
        assert_eq!(
            refusal_reason(
                "pay-enrol",
                "Minidregg.Kernel.PayEnrolReceiver.Reject.verifier\n  \
                 (Minidregg.Compiler.CredentialSignatureIO.Error.processFailed 70 \"verifier offline\")"
            ),
            Some("verifier:processFailed".into())
        );
        assert_eq!(
            refusal_reason("pay-enrol", "Minidregg.Kernel.PayEnrolReceiver.Reject.stalePay"),
            Some("stalePay".into())
        );
        // A bare `decision` with no inner constructor is not a reason the client acts on.
        assert_eq!(
            refusal_reason("pay-enrol", "Minidregg.Kernel.PayEnrolReceiver.Reject.decision"),
            None
        );
        assert!(enrol_record_refusal("decision:selfEnrolOff"));
        assert!(!enrol_record_refusal("policyRejected"));
        assert!(!enrol_record_refusal("verifier:processFailed"));
    }

    #[test]
    fn the_enrollment_index_comes_from_the_tariff_or_is_off() {
        assert_eq!(enrol_index_of(&json!({"tariff": null})).unwrap(), None);
        assert_eq!(enrol_index_of(&json!({"tariff": {"enrolIndex": null}})).unwrap(), None);
        assert_eq!(enrol_index_of(&json!({"tariff": {"enrolIndex": "0"}})).unwrap(), Some(0));
        assert!(enrol_index_of(&json!({"tariff": {"enrolIndex": "01"}})).is_err());
    }

    #[test]
    fn a_record_reaches_the_kernel_whole_memo_included() {
        let value = json!({"index":0,"address":"11".repeat(32),"signature":"22".repeat(64),
            "slot":1,"blockTime":2,"amount":3,"mint":"33".repeat(32),"tokenProgram":"44".repeat(32),
            "memo":null,"memoError":null});
        let record = Record::parse(&value).unwrap();
        let kernel = record.kernel();
        assert!(kernel.get("memo").is_some() && kernel.get("memoError").is_some());
        assert_eq!(kernel.as_object().unwrap().len(), 10);
        assert_eq!(record.name(), format!("{}.{}", "22".repeat(64), "11".repeat(32)));
        assert!(Record::parse(&json!({"index":0,"address":"AA".repeat(32),
            "signature":"22".repeat(64),"amount":1})).is_err());
    }

    #[test]
    fn keys_accept_hex_or_base58_and_nothing_else() {
        let bytes = [7u8; 32];
        assert_eq!(key_hex(&hex(&bytes), "k").unwrap(), hex(&bytes));
        assert_eq!(key_hex(&base58(&bytes), "k").unwrap(), hex(&bytes));
        assert!(key_hex(&base58(&[7u8; 31]), "k").is_err());
        assert!(key_hex("not a key", "k").is_err());
    }
}
