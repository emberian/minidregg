//! `mini fleet-sign`: the verbs of Bread's `dregg-client-sign` (join, send,
//! transfer) with its CLI shape and its one-JSON-object-on-stdout contract,
//! carried by Mini's fleet turn.
//!
//! Why a signer and not a gateway that forwards Bread's signed bytes: a Bread
//! client signs `Turn::hash` (`dregg-turn-v3`, BLAKE3 over Bread's agent cell,
//! nonce, call forest, computron fee, memo, height deadline and receipt head).
//! None of that names what a Mini fleet signature must bind: the deployment
//! domain, the paying account's law (semantics, policy epoch and revision), the
//! spend capability, the signer's key epoch, the authority pre-root, or a fee
//! equal to the pinned tariff. Admitting it would mean Mini's admission
//! accepting a signature that does not say which law it was given under. So the
//! fleet signs Mini's header with Mini's signer, and this verb keeps the
//! harness-facing shape.
//!
//! A profile is a directory `HOME/profiles/NAME/` holding the agent's Ed25519
//! seed (`key`, `key.pub`), its enrollment attempt (`enroll/`) and its
//! participant workspace (`workspace/`). HOME is `--home`, else
//! `MINI_FLEET_HOME`, else `$HOME/.mini-fleet`; the profile is `--profile`,
//! else `MINI_PROFILE`, else the `HOME/profiles/ACTIVE` file.

use crate::fleet::{self, field, read_json};
use crate::{absolute, generate_key, Args, NextKey, Result, SOCKET};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::io::{self, Write};

const USAGE: &str = "mini fleet-sign: dregg-client-sign's verbs as Mini fleet turns (stdout = exactly one JSON object)\n\n\
  join [--profile P] [--home H] [--fund N] --sponsor-workspace S [--factory-ref F]\n\
       create the profile's key on first use, admit it under the sponsor's factory grant and\n\
       give it an owned account funded with N (default 5000) from the sponsor's account.\n\
       Run where the sponsor's workspace is: admission is signed by the sponsor.\n\
  send [--profile P] [--home H] [--topic S] PAYLOAD...\n\
       commit ONE fleet turn appending PAYLOAD to the profile account's topic S\n\
       (default client-sign); exit 0 only with the exact receipt (turn_hash, receipt_hash)\n\
       a call that repeats an unfinished earlier one answers its receipt (`replayed`)\n\
  transfer --to ACCOUNT --amount N [--profile P] [--home H]\n\
       move N from the profile's account to ACCOUNT (the `cell` another join printed);\n\
       exit 0 only with the exact receipt of this turn\n\
  receipt (--turn-hash HEX64 | --head) [--profile P] [--home H]\n\
       the exact receipt of one transaction, or the profile account's newest fleet turn\n\
  retry --attempt DIR [--profile P] [--home H]\n\
       resubmit the EXACT retained bytes of one attempt; an accepted original answers\n\
       with its original receipt and nothing moves twice\n\n\
env (flags win): MINI_FLEET_HOME, MINI_PROFILE, MINI_FLEET_SPONSOR, MINI_FLEET_FACTORY_REF.\n\
--node-url accepts only unix:/ABSOLUTE/SOCKET, and only the socket the profile is pinned to.";

const VERBS: [&str; 5] = ["join", "send", "transfer", "receipt", "retry"];

/// The account reference name every fleet-sign profile pays from.
const ACCOUNT: &str = "account";

struct Flags {
    verb: String,
    home: PathBuf,
    profile: Option<String>,
    socket: Option<PathBuf>,
    topic: String,
    to: Option<String>,
    amount: Option<String>,
    fund: Option<String>,
    sponsor: Option<PathBuf>,
    factory: String,
    turn_hash: Option<String>,
    head: bool,
    attempt: Option<PathBuf>,
    rest: Vec<String>,
}

fn env_value(name: &str) -> Option<String> {
    env::var(name).ok().filter(|value| !value.is_empty())
}

fn default_home() -> Result<PathBuf> {
    if let Some(home) = env_value("MINI_FLEET_HOME") {
        return Ok(PathBuf::from(home));
    }
    let home = env_value("HOME").ok_or("set --home or MINI_FLEET_HOME (no $HOME)")?;
    Ok(Path::new(&home).join(".mini-fleet"))
}

/// Bread's `--node-url` names an HTTP node. Mini's ingress is the Host's
/// socket that the profile's workspace pins; a URL is refused by name rather
/// than ignored, so a harness pointed at a Bread node never silently talks to
/// a different one.
fn node_socket(value: &str) -> Result<PathBuf> {
    let Some(rest) = value.strip_prefix("unix:") else {
        return Err(format!(
            "--node-url {value}: Mini has no HTTP ingress; the profile is pinned to its Host's \
             socket. Pass unix:/ABSOLUTE/SOCKET or omit --node-url"
        ));
    };
    let socket = PathBuf::from(rest.trim_start_matches("//"));
    if !socket.is_absolute() {
        return Err("--node-url unix: socket must be an absolute path".into());
    }
    Ok(socket)
}

fn parse(argv: Vec<OsString>) -> Result<Flags> {
    let mut argv = argv
        .into_iter()
        .map(|value| value.into_string().map_err(|_| "fleet-sign arguments must be UTF-8".to_owned()))
        .collect::<Result<Vec<_>>>()?
        .into_iter();
    let verb = argv.next().ok_or_else(|| USAGE.to_owned())?;
    if verb == "--help" || verb == "-h" {
        return Err(USAGE.to_owned());
    }
    // The verb is judged before any flag, so a legacy verb with its own flags (helm's
    // `roster --json`) is refused as the verb it is, not as its first unknown flag.
    if !VERBS.contains(&verb.as_str()) {
        return Err(format!("unknown verb '{verb}' (try --help)"));
    }
    let mut flags = Flags {
        verb,
        home: PathBuf::new(),
        profile: env_value("MINI_PROFILE"),
        socket: None,
        topic: "client-sign".into(),
        to: None,
        amount: None,
        fund: None,
        sponsor: env_value("MINI_FLEET_SPONSOR").map(PathBuf::from),
        factory: env_value("MINI_FLEET_FACTORY_REF").unwrap_or_else(|| "factory".into()),
        turn_hash: None,
        head: false,
        attempt: None,
        rest: Vec::new(),
    };
    let mut home = None;
    while let Some(flag) = argv.next() {
        let mut value = |name: &str| argv.next().ok_or_else(|| format!("{name} requires a value"));
        match flag.as_str() {
            "--home" => home = Some(PathBuf::from(value("--home")?)),
            "--profile" => flags.profile = Some(value("--profile")?),
            "--node-url" => flags.socket = Some(node_socket(&value("--node-url")?)?),
            "--topic" => flags.topic = value("--topic")?,
            "--to" => flags.to = Some(value("--to")?),
            "--amount" => flags.amount = Some(value("--amount")?),
            "--fund" => flags.fund = Some(value("--fund")?),
            "--sponsor-workspace" => flags.sponsor = Some(PathBuf::from(value("--sponsor-workspace")?)),
            "--factory-ref" => flags.factory = value("--factory-ref")?,
            "--turn-hash" => flags.turn_hash = Some(value("--turn-hash")?),
            "--head" => flags.head = true,
            "--attempt" => flags.attempt = Some(PathBuf::from(value("--attempt")?)),
            "--token" | "--token-file" => {
                return Err(format!(
                    "{flag}: Mini's ingress takes no bearer token; authority is the profile's \
                     signature under its account grant"
                ))
            }
            "--accept-tentative" => {
                return Err(
                    "--accept-tentative: Mini has one commitment level (an accepted journal \
                     entry of the one Store); there is nothing tentative to accept"
                        .into(),
                )
            }
            "--help" | "-h" => return Err(USAGE.to_owned()),
            other if other.starts_with("--") => return Err(format!("unknown option {other}\n\n{USAGE}")),
            other => flags.rest.push(other.to_owned()),
        }
    }
    flags.home = match home {
        Some(home) => home,
        None => default_home()?,
    };
    flags.home = absolute(&flags.home)?;
    Ok(flags)
}

fn profile_name(flags: &Flags) -> Result<String> {
    let name = match &flags.profile {
        Some(name) => name.clone(),
        None => fs::read_to_string(flags.home.join("profiles").join("ACTIVE"))
            .map(|text| text.trim().to_owned())
            .map_err(|_| "no identity: pass --profile, or set MINI_PROFILE or HOME/profiles/ACTIVE")?,
    };
    if name.is_empty()
        || name.len() > 64
        || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err("a profile name is 1..64 of [A-Za-z0-9_-]".into());
    }
    Ok(name)
}

#[derive(Debug)]
struct Profile {
    name: String,
    dir: PathBuf,
}

impl Profile {
    fn key(&self) -> PathBuf {
        self.dir.join("key")
    }
    fn public(&self) -> PathBuf {
        self.dir.join("key.pub")
    }
    fn enroll(&self) -> PathBuf {
        self.dir.join("enroll")
    }
    fn workspace(&self) -> PathBuf {
        self.dir.join("workspace")
    }
    fn record(&self) -> PathBuf {
        self.workspace().join(format!("join-{ACCOUNT}.json"))
    }
}

fn profile(flags: &Flags) -> Result<Profile> {
    let name = profile_name(flags)?;
    let dir = flags.home.join("profiles").join(&name);
    Ok(Profile { name, dir })
}

/// A joined profile's agent, with the socket check `--node-url` asks for.
fn joined(flags: &Flags, profile: &Profile) -> Result<(fleet::Agent, Value, Value)> {
    if !profile.record().exists() {
        return Err(format!(
            "profile '{}' has not joined (no {}): run `mini fleet-sign join` first",
            profile.name,
            profile.record().display()
        ));
    }
    if let Some(socket) = &flags.socket {
        let _ = SOCKET.set(socket.clone());
    }
    let agent = fleet::agent(&profile.workspace())?;
    let reference = fleet::account(&agent, ACCOUNT)?;
    let record = read_json(&profile.record())?;
    Ok((agent, reference, record))
}

fn decimal(value: &str, label: &str) -> Result<()> {
    if !mini_sdk::decimal::is_canonical(value)
    {
        return Err(format!("{label} must be a canonical decimal"));
    }
    Ok(())
}

fn number(value: &str) -> Value {
    value.parse::<u64>().map(Value::from).unwrap_or_else(|_| json!(value))
}

fn current_balance(agent: &fleet::Agent, reference: &Value) -> Result<String> {
    let (view, _) = fleet::observe(agent, reference)?;
    let (_, asset) = fleet::tariff(agent)?;
    // The view lists only held balances: an account that holds nothing lists no pair (the same
    // reading `mini fleet`'s own account balance makes). helm's `join --fund 0` re-run on a
    // seat that holds 0 must answer balance 0, not an error.
    Ok(fleet::balance(&view, &asset).unwrap_or_else(|| "0".into()))
}

fn join(flags: &Flags) -> Result<Value> {
    if !flags.rest.is_empty() || flags.to.is_some() || flags.amount.is_some() {
        return Err("join takes no payload, --to or --amount".into());
    }
    let profile = profile(flags)?;
    let fund = flags.fund.clone().unwrap_or_else(|| "5000".into());
    decimal(&fund, "--fund")?;
    if profile.record().exists() {
        // Already joined: report the signed current balance. There is no
        // faucet; a balance below the floor is raised by a transfer from a
        // funded account, never by this verb.
        let (agent, reference, record) = joined(flags, &profile)?;
        let balance = current_balance(&agent, &reference)?;
        if balance.parse::<u128>().unwrap_or(0) < fund.parse::<u128>().unwrap_or(0) {
            return Err(format!(
                "profile '{}' holds {balance}, below --fund {fund}; Mini has no faucet: a funded \
                 profile (or the sponsor) moves value with `mini fleet-sign transfer --to {}`",
                profile.name,
                field(&record, "account")?
            ));
        }
        return Ok(json!({
            "joined": true, "node": agent_socket(&agent)?, "profile": profile.name,
            "public_key": record["publicKey"], "cell": record["account"], "subject": record["subject"],
            "materialized": false, "topped_up": false, "joined_in_flight": false,
            "balance": number(&balance), "spend_capability": record["spendCapability"],
        }));
    }
    let sponsor = flags
        .sponsor
        .clone()
        .ok_or("join needs the sponsor's workspace: --sponsor-workspace or MINI_FLEET_SPONSOR")?;
    crate::fsio::ensure_private_dir_all(&profile.dir)?;
    if !profile.key().exists() {
        // K-PREROTATE: the agent key commits to a next key made beside it
        // (hosted: the notice says to move it off the box); fleet join's
        // enrollment plan finds it by the KEY.next.pub convention.
        generate_key(&profile.key(), &profile.public(), None, NextKey::Beside, true)?;
    }
    let args = Args {
        command: OsString::from("fleet"),
        values: [
            ("sponsor-workspace", sponsor.into_os_string()),
            ("factory-ref", OsString::from(&flags.factory)),
            ("name", OsString::from(&profile.name)),
            ("new-key", profile.key().into_os_string()),
            ("enroll-dir", profile.enroll().into_os_string()),
            ("dir", profile.workspace().into_os_string()),
            ("fund", OsString::from(&fund)),
            ("account-name", OsString::from(ACCOUNT)),
        ]
        .into_iter()
        .map(|(key, value)| (OsString::from(format!("--{key}")), value))
        .collect(),
    };
    fleet::join(args)?;
    let record = read_json(&profile.record())?;
    let agent = fleet::agent(&profile.workspace())?;
    Ok(json!({
        "joined": true, "node": agent_socket(&agent)?, "profile": profile.name,
        "public_key": record["publicKey"], "cell": record["account"], "subject": record["subject"],
        "materialized": true, "topped_up": false, "joined_in_flight": false,
        "balance": number(record["balance"].as_str().unwrap_or("0")),
        "spend_capability": record["spendCapability"],
        "enrollment_receipt": record["enrollmentReceipt"], "funding_receipt": record["fundingReceipt"],
    }))
}

fn agent_socket(_agent: &fleet::Agent) -> Result<String> {
    SOCKET
        .get()
        .map(|socket| format!("unix:{}", socket.display()))
        .ok_or_else(|| "no Host socket is pinned".into())
}

/// The 32-octet big-endian image of a canonical decimal below 2^256 (every receipt field is
/// one: a transaction id, an event id, an accepted count, a world root).
fn be256(decimal: &str) -> Result<[u8; 32]> {
    if !mini_sdk::decimal::is_canonical(decimal) {
        return Err(format!("{decimal}: not a canonical decimal"));
    }
    let mut out = [0u8; 32];
    for digit in decimal.bytes() {
        let mut carry = u32::from(digit - b'0');
        for byte in out.iter_mut().rev() {
            let value = u32::from(*byte) * 10 + carry;
            *byte = (value & 0xff) as u8;
            carry = value >> 8;
        }
        if carry != 0 {
            return Err(format!("{decimal}: does not fit 256 bits"));
        }
    }
    Ok(out)
}

/// The canonical decimal of a 32-octet big-endian number (`be256`'s inverse).
fn decimal_of_be256(bytes: [u8; 32]) -> String {
    let mut value = bytes;
    let mut digits = Vec::new();
    while value.iter().any(|byte| *byte != 0) {
        let mut remainder = 0u32;
        for byte in value.iter_mut() {
            let current = (remainder << 8) | u32::from(*byte);
            *byte = (current / 10) as u8;
            remainder = current % 10;
        }
        digits.push(b'0' + remainder as u8);
    }
    if digits.is_empty() {
        return "0".into();
    }
    digits.reverse();
    String::from_utf8(digits).expect("ASCII digits")
}

/// Bread's `turn_hash`: 64 lowercase hex. Here it is Mini's transaction id (derived from the
/// signed identity, never from the answer) as 32 big-endian octets: the same number, in the
/// shape a Bread harness checks (helm `chat._hex64`).
fn turn_hash(transaction: &str) -> Result<String> {
    Ok(crate::hex(&be256(transaction)?))
}

/// A `--turn-hash` argument: the 64-hex form `turn_hash` prints, read back to the decimal
/// transaction id. The decimal form is refused by name: one shape on this surface.
fn transaction_of_turn_hash(value: &str) -> Result<String> {
    if value.len() != 64 || !value.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err(format!(
            "--turn-hash {value}: a turn hash is the 64 hex digits `turn_hash` printed"
        ));
    }
    let bytes = crate::decode_hex(&value.to_ascii_lowercase())?;
    let bytes: [u8; 32] = bytes.try_into().map_err(|_| "--turn-hash: not 32 octets".to_owned())?;
    Ok(decimal_of_be256(bytes))
}

/// The domain of `receipt_hash`.
const RECEIPT_HASH_TAG: &[u8] = b"MINI.FLEET-SIGN.RECEIPT-HASH/v1\0";

/// Bread's `receipt_hash`, defined for Mini: SHA-256 over the tag, then the four receipt
/// fields (transaction id, event id, accepted count, world root), each as 32 big-endian
/// octets. It names the Host's exact receipt: two receipts that differ in any field differ
/// here (fixed width, fixed order, no separator ambiguity).
fn receipt_hash(receipt: &Value) -> Result<String> {
    let mut hasher = Sha256::new();
    hasher.update(RECEIPT_HASH_TAG);
    for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
        hasher.update(be256(field(receipt, key)?)?);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

/// Bread's receipt row, read off Mini's four-field receipt: `turn_hash` and `receipt_hash`
/// in Bread's 64-hex shape (above), the chain index is the accepted count, and the
/// four-field receipt itself is printed as `receipt`. There is no finality ladder;
/// `finality` says what the commitment is.
fn receipt_fields(result: &Value) -> Result<Value> {
    let receipt = &result["receipt"];
    Ok(json!({
        "turn_hash": turn_hash(field(receipt, "transactionId")?)?,
        "receipt_hash": receipt_hash(receipt)?,
        "receipt": receipt,
        "chain_index": number(field(receipt, "acceptedCount")?),
        "finality": "accepted",
    }))
}

/// The four-field receipt of a confirmed exact-resubmission outcome.
fn outcome_receipt(outcome: &Value) -> Value {
    json!({
        "transactionId": outcome["transactionId"], "eventId": outcome["eventId"],
        "acceptedCount": outcome["acceptedCount"], "worldRoot": outcome["worldRoot"],
    })
}

// ---- one operation, at most one commit
//
// A harness retries a call it judged failed (helm `_sign_send` sends a second time). A
// fleet-sign process can die, or lose the Host's answer, after its turn reached the Host,
// and a fresh turn would then commit a second time. So every send and transfer is an
// OPERATION: before its turn, the profile records the operation's identity
// (`operation.json`), and every attempt that may reach the Host is journaled
// (`operation-attempts`, written by `fleet::turn_journaled` after the attempt's submit
// marker and before its one submission). The record is removed only after the answer is
// printed. A later call that finds a record resolves it FIRST, by exact resubmission of
// its live attempt: an accepted original answers `replayed` with its original receipt, a
// never-accepted one is decided now; nothing commits twice. When the later call is the
// SAME operation (same verb and arguments), the resolved receipt is its answer.

const OPERATION_TAG: &[u8] = b"MINI.FLEET-SIGN.OPERATION/v1\0";

/// The identity of one harness call: the verb and every argument that names what it does,
/// each length-prefixed.
fn operation_id(verb: &str, parts: &[&str]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(OPERATION_TAG);
    for part in std::iter::once(verb).chain(parts.iter().copied()) {
        hasher.update((part.len() as u64).to_be_bytes());
        hasher.update(part.as_bytes());
    }
    format!("{:x}", hasher.finalize())
}

impl Profile {
    fn operation(&self) -> PathBuf {
        self.dir.join("operation.json")
    }
    fn operation_attempts(&self) -> PathBuf {
        self.dir.join("operation-attempts")
    }
}

/// The recorded operation of an earlier call that did not finish, if any.
fn pending_operation(profile: &Profile) -> Result<Option<(String, Vec<PathBuf>)>> {
    if !profile.operation().exists() {
        return Ok(None);
    }
    let record = read_json(&profile.operation())?;
    let operation = field(&record, "operation")?.to_owned();
    let attempts = match fs::read_to_string(profile.operation_attempts()) {
        Ok(text) => text.lines().filter(|line| !line.is_empty()).map(PathBuf::from).collect(),
        Err(error) if error.kind() == io::ErrorKind::NotFound => Vec::new(),
        Err(error) => return Err(format!("{}: {error}", profile.operation_attempts().display())),
    };
    Ok(Some((operation, attempts)))
}

/// Resolve an unfinished operation's attempts. Every attempt but the last was superseded
/// (decided, nothing moved: `fleet::turn` journals a new attempt only after the previous one
/// was superseded); the last one is resubmitted exactly. Returns its confirmed outcome, or
/// None when it was never admitted (refused now, or it never reached the Host).
fn resolve(agent: &fleet::Agent, attempts: &[PathBuf]) -> Result<Option<(PathBuf, Value)>> {
    let Some((last, earlier)) = attempts.split_last() else {
        return Ok(None);
    };
    for attempt in earlier {
        if !attempt.join("superseded.json").exists() {
            return Err(format!(
                "unfinished operation: attempt {} is neither superseded nor the last; resolve it with \
                 `mini fleet-sign retry --attempt {}`",
                attempt.display(),
                attempt.display()
            ));
        }
    }
    if last.join("superseded.json").exists() {
        return Ok(None);
    }
    let outcome = fleet::resubmit(agent, last)?;
    Ok(fleet::confirmed(&outcome).then(|| (last.clone(), outcome)))
}

fn write_private(path: &Path, bytes: &[u8]) -> Result<()> {
    let temporary = path.with_extension("tmp");
    fs::write(&temporary, bytes)
        .and_then(|_| fs::File::open(&temporary)?.sync_all())
        .and_then(|_| fs::rename(&temporary, path))
        .map_err(|error| format!("{}: {error}", path.display()))
}

/// Run one operation at most once. `turn` gets the journal path to pass to
/// `fleet::turn_journaled`. Answers `Ok(Ok(result))` for a fresh turn, `Ok(Err((attempt,
/// outcome)))` when an earlier call of the SAME operation had already committed.
fn once(
    profile: &Profile,
    agent: &fleet::Agent,
    operation: &str,
    verb: &str,
    turn: impl FnOnce(&Path) -> Result<Value>,
) -> Result<std::result::Result<Value, (PathBuf, Value)>> {
    if let Some((earlier, attempts)) = pending_operation(profile)? {
        let resolved = resolve(agent, &attempts)?;
        if earlier == operation {
            if let Some(found) = resolved {
                eprintln!("mini fleet-sign: this {verb} was already committed by an earlier call; answering its receipt");
                return Ok(Err(found));
            }
        } else if resolved.is_some() {
            eprintln!(
                "mini fleet-sign: an earlier unfinished operation ({earlier}) was committed; its receipt is in {}",
                attempts.last().map(|p| p.display().to_string()).unwrap_or_default()
            );
        }
        finish(profile)?;
    }
    write_private(
        &profile.operation(),
        serde_json::to_string(&json!({"format":"minidregg-fleet-sign-operation-v1","operation":operation,"verb":verb}))
            .map_err(|error| error.to_string())?
            .as_bytes(),
    )?;
    write_private(&profile.operation_attempts(), b"")?;
    turn(&profile.operation_attempts()).map(Ok)
}

/// The operation's answer is printed: forget it.
fn finish(profile: &Profile) -> Result<()> {
    for path in [profile.operation_attempts(), profile.operation()] {
        match fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => return Err(format!("{}: {error}", path.display())),
        }
    }
    Ok(())
}

fn merge(mut base: Value, extra: Value) -> Value {
    if let (Some(base), Value::Object(extra)) = (base.as_object_mut(), extra) {
        base.extend(extra);
    }
    base
}

fn send(flags: &Flags) -> Result<(Value, Profile)> {
    if flags.rest.is_empty() {
        return Err("send requires a payload".into());
    }
    if flags.amount.is_some() {
        return Err("send takes no --amount: use transfer to move value".into());
    }
    if flags.fund.is_some() {
        return Err("--fund on send: Mini has no faucet; fund a profile at join or by a transfer".into());
    }
    let payload = flags.rest.join(" ");
    let profile = profile(flags)?;
    let (agent, reference, record) = joined(flags, &profile)?;
    // Pug's harness (helm `chat.py` `_sign_send`) passes `--to <the cell join printed>` on every
    // send: Bread's tool took `--to` there only when it named the signer's OWN cell. The same
    // contract holds here: the profile's own account is accepted and means nothing more; any
    // other destination is refused by name, since a send never moves value.
    if let Some(to) = &flags.to {
        if to.len() == 64 && to.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err("--to is a Bread cell id; a Mini account is the decimal `cell` its join printed".into());
        }
        if to != field(&record, "account")? {
            return Err(format!(
                "send posts on the profile's own account and takes --to only as that account \
                 ({}); {to} is another account: use transfer to move value",
                field(&record, "account")?
            ));
        }
    }
    let topic = fleet::topic_bytes(&flags.topic)?;
    if payload.len() > 16_384 {
        return Err("payload exceeds 16384 bytes".into());
    }
    let publication = json!({"topic":crate::hex(&topic),"sequence":"0","payload":crate::hex(payload.as_bytes())});
    let account = field(&record, "account")?.to_owned();
    let operation = operation_id("send", &[&account, &flags.topic, &payload]);
    let base = json!({
        "sent": true, "node": agent_socket(&agent)?, "profile": profile.name,
        "agent_cell": account, "to": account, "topic": flags.topic, "payload": payload,
        "operation": operation,
    });
    let value = match once(&profile, &agent, &operation, "send", |journal| {
        fleet::turn_journaled(&agent, &reference, "send", Value::Null, publication, Some(journal))
    })? {
        Ok(result) => merge(
            merge(base, json!({
                "sequence": number(field(&result["publication"], "sequence")?),
                "fee": number(field(&result, "fee")?),
                "replans": number(field(&result, "replans")?),
                "confirmation": result["confirmation"], "attempt": result["attempt"],
            })),
            receipt_fields(&result)?,
        ),
        Err((attempt, outcome)) => replayed(base, &attempt, &outcome)?,
    };
    Ok((value, profile))
}

/// The answer to a call whose operation an earlier call had already committed.
fn replayed(base: Value, attempt: &Path, outcome: &Value) -> Result<Value> {
    Ok(merge(
        merge(base, json!({"replayed": true, "confirmation": outcome["confirmation"], "attempt": attempt})),
        receipt_fields(&json!({"receipt": outcome_receipt(outcome)}))?,
    ))
}

fn transfer(flags: &Flags) -> Result<(Value, Profile)> {
    if !flags.rest.is_empty() {
        return Err("transfer takes no payload".into());
    }
    if flags.fund.is_some() {
        return Err("--fund on transfer: Mini has no faucet; the source must already hold amount + fee".into());
    }
    let amount = flags.amount.clone().ok_or("transfer requires --amount N")?;
    decimal(&amount, "--amount")?;
    if amount == "0" {
        return Err("transfer requires a positive --amount: a zero transfer moves nothing and still pays the fee".into());
    }
    let to = flags.to.clone().ok_or("transfer requires --to ACCOUNT")?;
    if to.len() == 64 && to.bytes().all(|b| b.is_ascii_hexdigit()) {
        return Err("--to is a Bread cell id; a Mini account is the decimal `cell` its join printed".into());
    }
    decimal(&to, "--to")?;
    let profile = profile(flags)?;
    let (agent, reference, record) = joined(flags, &profile)?;
    let from = field(&record, "account")?.to_owned();
    if to == from {
        return Err(format!(
            "--to {to} is profile '{}'s own account: a self-transfer moves nothing and still pays the fee",
            profile.name
        ));
    }
    let (_, asset) = fleet::tariff(&agent)?;
    let transfer = fleet::transfer_value(&to, &amount, &asset)?;
    let operation = operation_id("transfer", &[&from, &to, &amount, &asset]);
    let base = json!({
        "transferred": true, "committed": true, "node": agent_socket(&agent)?,
        "profile": profile.name, "from": from, "to": to, "amount": number(&amount),
        "operation": operation,
    });
    let value = match once(&profile, &agent, &operation, "transfer", |journal| {
        fleet::turn_journaled(&agent, &reference, "transfer", transfer, Value::Null, Some(journal))
    })? {
        Ok(result) => merge(
            merge(base, json!({
                "fee": number(field(&result, "fee")?),
                "replans": number(field(&result, "replans")?),
                "confirmation": result["confirmation"], "attempt": result["attempt"],
            })),
            receipt_fields(&result)?,
        ),
        Err((attempt, outcome)) => replayed(base, &attempt, &outcome)?,
    };
    Ok((value, profile))
}

fn receipt(flags: &Flags) -> Result<Value> {
    let profile = profile(flags)?;
    let (agent, reference, record) = joined(flags, &profile)?;
    match (&flags.turn_hash, flags.head) {
        (Some(hash), false) => {
            let transaction = transaction_of_turn_hash(hash)?;
            let value = fleet::receipt_by_transaction(&agent, &transaction)?;
            match field(&value, "type")? {
                "confirmed" if field(&value["receipt"], "transactionId")? == transaction => Ok(merge(
                    json!({"found": true, "profile": profile.name}),
                    receipt_fields(&value)?,
                )),
                "confirmed" => Err("the receipt lookup answered for another transaction".into()),
                other => Err(format!("no accepted transaction {hash} ({other})")),
            }
        }
        (None, true) => {
            let value = fleet::head_of(&agent, &reference)?;
            Ok(json!({"profile": profile.name, "cell": record["account"], "head": value}))
        }
        _ => Err("receipt needs exactly one of --turn-hash TX or --head".into()),
    }
}

fn retry(flags: &Flags) -> Result<Value> {
    let attempt = flags.attempt.clone().ok_or("retry requires --attempt DIR")?;
    let profile = profile(flags)?;
    let (agent, _, _) = joined(flags, &profile)?;
    let outcome = fleet::resubmit(&agent, &attempt)?;
    if !fleet::confirmed(&outcome) {
        return Err(format!(
            "exact resubmission was not confirmed ({}); outcome retained in {}",
            field(&outcome, "type")?,
            attempt.display()
        ));
    }
    Ok(merge(
        json!({"retried": true, "profile": profile.name, "confirmation": outcome["confirmation"]}),
        receipt_fields(&json!({"receipt": outcome_receipt(&outcome)}))?,
    ))
}

extern "C" {
    fn dup(fd: i32) -> i32;
    fn dup2(source: i32, target: i32) -> i32;
    fn close(fd: i32) -> i32;
}

/// While held, file descriptor 1 is the process's stderr. The verbs underneath
/// (enrollment, workspace init, birth authoring) report progress on stdout;
/// this verb's contract is exactly one JSON object there, written after the
/// guard is dropped.
struct StdoutToStderr(i32);

impl StdoutToStderr {
    fn hold() -> Result<Self> {
        io::stdout().flush().map_err(|error| error.to_string())?;
        // SAFETY: dup/dup2 on the process's own standard descriptors.
        let saved = unsafe { dup(1) };
        if saved < 0 || unsafe { dup2(2, 1) } < 0 {
            return Err("cannot route progress output to stderr".into());
        }
        Ok(Self(saved))
    }
}

impl Drop for StdoutToStderr {
    fn drop(&mut self) {
        let _ = io::stdout().flush();
        // SAFETY: restores the descriptor saved in `hold`.
        unsafe {
            dup2(self.0, 1);
            close(self.0);
        }
    }
}

/// Bread's signer reads these from the environment, and a harness exports them on every call
/// (helm sets DREGG_NODE_URL, DREGG_API_TOKEN, DREGG_PROFILE and DREGG_COORDINATION_EXEMPT for
/// each signer subprocess). Refusing the ambient environment would refuse every call, so each
/// one that is set is named on stderr as not read; the flags that choose the same things are
/// refused outright, because those are a deliberate per-call act.
const BREAD_ENV: [&str; 6] = [
    "DREGG_NODE_URL",
    "DREGG_API_TOKEN",
    "DREGG_API_TOKEN_FILE",
    "DREGG_NODE_PASSPHRASE",
    "DREGG_COORDINATION_EXEMPT",
    "DREGG_PROFILE",
];

fn note_unread_bread_env() {
    for name in BREAD_ENV {
        if env_value(name).is_some() {
            eprintln!(
                "mini fleet-sign: {name} is set and not read (Bread's signer used it; Mini's \
                 profile, socket and fee come from --profile/MINI_PROFILE, the profile's pinned \
                 Host and the pinned tariff)"
            );
        }
    }
}

pub(crate) fn run(argv: Vec<OsString>) -> Result<()> {
    let flags = parse(argv)?;
    note_unread_bread_env();
    let (value, operation) = {
        let _progress = StdoutToStderr::hold()?;
        match flags.verb.as_str() {
            "join" => join(&flags).map(|value| (value, None)),
            "send" => send(&flags).map(|(value, profile)| (value, Some(profile))),
            "transfer" => transfer(&flags).map(|(value, profile)| (value, Some(profile))),
            "receipt" => receipt(&flags).map(|value| (value, None)),
            "retry" => retry(&flags).map(|value| (value, None)),
            other => Err(format!("unknown verb '{other}' (try --help)")),
        }
    }?;
    let mut stdout = io::stdout();
    writeln!(
        stdout,
        "{}",
        serde_json::to_string(&value).map_err(|error| format!("cannot render result: {error}"))?
    )
    .and_then(|_| stdout.flush())
    .map_err(|error| format!("cannot write the answer: {error}"))?;
    // The answer is out: only now is the operation forgotten (a call that dies before this
    // line leaves it recorded, and the next call resolves it instead of committing again).
    if let Some(profile) = operation {
        finish(&profile)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn argv(words: &[&str]) -> Vec<OsString> {
        words.iter().map(OsString::from).collect()
    }

    fn refusal(words: &[&str]) -> String {
        match parse(argv(words)) {
            Ok(_) => panic!("{words:?} parsed"),
            Err(error) => error,
        }
    }

    #[test]
    fn a_bread_node_url_is_refused_by_name_not_ignored() {
        assert!(refusal(&["send", "--home", "/h", "--node-url", "http://127.0.0.1:8899", "x"])
            .contains("no HTTP ingress"));
        assert!(refusal(&["send", "--home", "/h", "--node-url", "unix:relative.sock", "x"])
            .contains("absolute"));
        let flags = parse(argv(&["send", "--home", "/h", "--node-url", "unix:///run/m.sock", "x"])).unwrap();
        assert_eq!(flags.socket, Some(PathBuf::from("/run/m.sock")));
    }

    #[test]
    fn bread_only_switches_refuse_with_their_reason() {
        assert!(refusal(&["send", "--home", "/h", "--token-file", "/t", "x"]).contains("no bearer token"));
        assert!(refusal(&["send", "--home", "/h", "--token", "t", "x"]).contains("no bearer token"));
        assert!(refusal(&["transfer", "--home", "/h", "--accept-tentative"]).contains("one commitment level"));
        assert!(refusal(&["send", "--home", "/h", "--bogus", "x"]).contains("unknown option"));
    }

    #[test]
    fn a_verb_bread_never_had_is_refused_as_the_verb() {
        for words in [
            &["roster", "--json"][..],
            &["accept", "--home", "/h"][..],
            &["recv"][..],
            &["heartbeat", "--profile", "x"][..],
            &["frobnicate"][..],
        ] {
            let error = refusal(words);
            assert!(error.contains(&format!("unknown verb '{}'", words[0])), "{error}");
        }
    }

    #[test]
    fn bread_environment_names_are_the_ones_the_notice_covers() {
        // helm exports exactly these on every signer subprocess (cell.py ENV_MAP, chat.py _env_extra).
        for name in ["DREGG_NODE_URL", "DREGG_API_TOKEN", "DREGG_NODE_PASSPHRASE", "DREGG_COORDINATION_EXEMPT", "DREGG_PROFILE"] {
            assert!(BREAD_ENV.contains(&name), "{name}");
        }
    }

    #[test]
    fn turn_hash_is_the_transaction_id_in_64_hex_and_reads_back() {
        for decimal in ["0", "1", "255", "256", "65535",
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"] {
            let hash = turn_hash(decimal).unwrap();
            assert_eq!(hash.len(), 64);
            assert!(hash.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f')));
            assert_eq!(transaction_of_turn_hash(&hash).unwrap(), decimal);
        }
        assert_eq!(turn_hash("256").unwrap(), format!("{}0100", "0".repeat(60)));
        assert!(turn_hash("115792089237316195423570985008687907853269984665640564039457584007913129639936")
            .unwrap_err().contains("256 bits"));
        assert!(transaction_of_turn_hash("12345").unwrap_err().contains("64 hex"));
    }

    #[test]
    fn receipt_hash_names_every_field_of_the_receipt() {
        let receipt = json!({"transactionId":"7","eventId":"8","acceptedCount":"9","worldRoot":"10"});
        let hash = receipt_hash(&receipt).unwrap();
        assert_eq!(hash.len(), 64);
        for key in ["transactionId", "eventId", "acceptedCount", "worldRoot"] {
            let mut other = receipt.clone();
            other[key] = json!("11");
            assert_ne!(receipt_hash(&other).unwrap(), hash, "{key}");
        }
        // swapping two fields' values changes it too (fixed order)
        let swapped = json!({"transactionId":"8","eventId":"7","acceptedCount":"9","worldRoot":"10"});
        assert_ne!(receipt_hash(&swapped).unwrap(), hash);
    }

    #[test]
    fn operation_identity_separates_its_arguments() {
        let a = operation_id("send", &["1", "t", "ab"]);
        assert_eq!(a, operation_id("send", &["1", "t", "ab"]));
        assert_ne!(a, operation_id("send", &["1", "ta", "b"]));
        assert_ne!(a, operation_id("transfer", &["1", "t", "ab"]));
        assert_ne!(a, operation_id("send", &["1", "t", "ab", ""]));
    }

    #[test]
    fn payload_words_join_like_bread() {
        let flags = parse(argv(&["send", "--home", "/h", "--topic", "t", "hello", "from", "alpha"])).unwrap();
        assert_eq!(flags.rest.join(" "), "hello from alpha");
        assert_eq!(flags.topic, "t");
    }

    #[test]
    fn profile_names_are_bounded_path_safe_labels() {
        let named = |name: &str| {
            let mut flags = parse(argv(&["join", "--home", "/h"])).unwrap();
            flags.profile = Some(name.into());
            profile_name(&flags)
        };
        assert!(named("alpha-1_b").is_ok());
        for bad in ["", "../x", "a/b", "a b", &"x".repeat(65)] {
            assert!(named(bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn a_bread_cell_id_is_not_read_as_an_account() {
        let mut flags = parse(argv(&["transfer", "--home", "/h", "--amount", "1"])).unwrap();
        flags.to = Some("ab".repeat(32));
        assert!(transfer(&flags).unwrap_err().contains("Bread cell id"));
        flags.to = Some("007".into());
        assert!(transfer(&flags).unwrap_err().contains("canonical decimal"));
    }
}
