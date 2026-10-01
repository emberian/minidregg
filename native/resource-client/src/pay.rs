//! PAY P4: the client side of the payment rail (PAY.md §2.2–§2.5, §3.4, §5).
//!
//! Every verb runs through a participant workspace (`mini workspace --action init`) whose
//! session socket reaches the Host's pay operations:
//!
//! | op | purpose |
//! |---|---|
//! | 103 / 104 / 105 / 106 | book-or-assignment plan, detached assembly, submit, receipt-only lookup |
//! | 107 | the public pay view (roots, tariff, clock, nextFree, book) |
//! | 108 / 109 / 110 / 111 | observation plan, assembly, submit, receipt-only lookup |
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
const VIEW_OP: u8 = 107;

/// The durable preflight's refusal of a spent nullifier, exactly as the Host renders it
/// (phase `durable`). On a report whose tip is newer than the clock it can only be an
/// observation's nullifier (see `observe`), which means the transfer was already credited.
const ALREADY_CONSUMED: &str = "Minidregg.Kernel.DurableDataIntent.RejectReason.durable \
    (Minidregg.Kernel.DurableCommitProtocol.RejectReason.alreadyConsumed)";
const REJECT_PREFIXES: [&str; 3] = [
    "Minidregg.Kernel.PayObservation.Reject.",
    "Minidregg.Kernel.PayAssignmentReceiver.Reject.",
    "Minidregg.Kernel.PayBookReceiver.Reject.",
];
/// Refusals decided by one observation on its own (`PayObservation.decideObservation`, and the
/// Book admission of its credit). A report carrying such a record is refused whole.
const PER_OBSERVATION: [&str; 10] = [
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
];
/// Fields the watcher emits that the v1 observation codec (`DREGG/PAY/OBSERVATION/v1`) does
/// not carry. They are retained in the attempt's `records.json`; OBSERVATION/v2 (lane P3b-1)
/// carries them into the report.
const V2_ONLY_FIELDS: [&str; 2] = ["memo", "memoError"];

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
}

impl Session {
    fn open(root: &Path) -> Result<Self> {
        let root = absolute(root)?;
        let workspace = workspace::load(&root)?;
        let socket = SOCKET
            .get()
            .cloned()
            .ok_or("pay verbs need a workspace with a pinned session socket")?;
        let session = Session {
            host: workspace::member_path(&workspace, "host")?,
            config: workspace::member_path(&workspace, "config")?,
            key: workspace::member_path(&workspace, "key")?,
            subject: workspace::member(&workspace, "subject")?.to_owned(),
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
        session_invoke(
            &self.host,
            &self.socket,
            &self.config,
            operation,
            payload,
        )
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
        (!name.is_empty() && (tail.is_empty() || tail.starts_with(' '))).then_some(name)
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
            Answer::Refused {
                reason: refusal_reason(&phase, &detail),
                phase,
                detail,
            }
        }
        Some(kind) => Answer::Undecided(format!("{kind} {}", hex_text(&outcome, "detail"))),
        None => Answer::Undecided("outcome without a type".into()),
    }
}

// ---------------------------------------------------------------- one signed call

/// Read the public pay view (op 107) into `directory/view.{bin,json}`.
fn read_view(session: &Session, directory: &Path) -> Result<Value> {
    let frame = session.call(VIEW_OP, &[])?;
    let body = frame_body(&frame, VIEW_OP)?;
    let bin = directory.join("view.bin");
    create_private(&bin, body)?;
    session.inspect("pay-view", &bin, &directory.join("view.json"))
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
        return Ok(());
    }
    retain_json(
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
            "clock slot {}  blockTime {}",
            text(clock, "slot")?,
            text(clock, "blockTime")?
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

    /// The v1 codec's record: the watcher's fields minus the ones only v2 carries.
    fn v1(&self) -> Value {
        let mut value = self.value.clone();
        if let Some(object) = value.as_object_mut() {
            for field in V2_ONLY_FIELDS {
                object.remove(field);
            }
        }
        value
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
        "observations":records.iter().map(Record::v1).collect::<Vec<_>>()}))
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
fn observe(session: &Session, capability: &str, file: &Value, hold: bool) -> Result<()> {
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
    if hold {
        let (attempt, _) = build_report(session, capability, &tip, &records)?;
        println!("held\t{}\t{} record(s)", attempt.display(), records.len());
        return Ok(());
    }
    let step = observe_records(session, capability, &tip, records, &mut tally, None)?;
    summary(&tip, &tally, step);
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
    println!(
        "pay observe: tip {} reports {} credited {} already-credited {} quarantined {}{}",
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

fn audit(session: &Session, offline: bool) -> Result<()> {
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
    let quarantined = fs::read_dir(session.quarantine_dir())
        .map_err(|error| error.to_string())?
        .count();
    println!(
        "credited {credited} over {transfers} transfer(s); over-cap residual {residual} atomic; \
         quarantined {quarantined}"
    );
    if offline {
        findings += ledger_identity(session, credited)?;
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
    let root = path(args.required("dir")?);
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
            let resume_attempt = args.optional("resume").map(path);
            let from = args.optional("from");
            let hold = args.optional("hold").is_some_and(|value| value == "true");
            args.finish()?;
            let session = Session::open(&root)?;
            match (resume_attempt, from) {
                (Some(attempt), None) if !hold => resume(&session, &capability, &attempt),
                (None, Some(from)) => {
                    observe(&session, &capability, &read_observations(&from)?, hold)
                }
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
            observe(&Session::open(&root)?, &capability, &file, false)
        }
        "audit" => {
            let offline = args.optional("offline").is_some_and(|value| value == "true");
            args.finish()?;
            audit(&Session::open(&root)?, offline)
        }
        other => Err(format!(
            "unknown pay action {other}: address|status|book|watch-config|observe|heartbeat|audit"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn a_v1_record_drops_only_the_fields_v2_carries() {
        let value = json!({"index":0,"address":"11".repeat(32),"signature":"22".repeat(64),
            "slot":1,"blockTime":2,"amount":3,"mint":"33".repeat(32),"tokenProgram":"44".repeat(32),
            "memo":null,"memoError":null});
        let record = Record::parse(&value).unwrap();
        let v1 = record.v1();
        assert!(v1.get("memo").is_none() && v1.get("memoError").is_none());
        assert_eq!(v1.as_object().unwrap().len(), 8);
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
