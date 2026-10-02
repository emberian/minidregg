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
       (default client-sign); exit 0 only with the exact receipt\n\
  transfer --to ACCOUNT --amount N [--profile P] [--home H]\n\
       move N from the profile's account to ACCOUNT (the `cell` another join printed);\n\
       exit 0 only with the exact receipt of this turn\n\
  receipt (--turn-hash TX | --head) [--profile P] [--home H]\n\
       the exact receipt of one transaction, or the profile account's newest fleet turn\n\
  retry --attempt DIR [--profile P] [--home H]\n\
       resubmit the EXACT retained bytes of one attempt; an accepted original answers\n\
       with its original receipt and nothing moves twice\n\n\
env (flags win): MINI_FLEET_HOME, MINI_PROFILE, MINI_FLEET_SPONSOR, MINI_FLEET_FACTORY_REF.\n\
--node-url accepts only unix:/ABSOLUTE/SOCKET, and only the socket the profile is pinned to.";

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

fn private_dir(path: &Path) -> Result<()> {
    use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
    if !path.exists() {
        fs::DirBuilder::new()
            .recursive(true)
            .mode(0o700)
            .create(path)
            .map_err(|error| format!("cannot create {}: {error}", path.display()))?;
    }
    let mode = fs::metadata(path)
        .map_err(|error| error.to_string())?
        .permissions()
        .mode();
    if mode & 0o077 != 0 {
        return Err(format!("{} must be private (mode 700)", path.display()));
    }
    Ok(())
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
    if value.is_empty()
        || !value.bytes().all(|b| b.is_ascii_digit())
        || (value.len() > 1 && value.starts_with('0'))
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
    fleet::balance(&view, &asset).ok_or_else(|| "the account view lists no balance in the fee asset".into())
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
    private_dir(&profile.dir)?;
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

/// Bread's receipt row, read off Mini's four-field receipt: the turn hash is
/// the transaction id (derived from the signed identity, never from the
/// answer), the chain index is the accepted count. There is no receipt hash
/// and no finality ladder; `finality` says what the commitment is.
fn receipt_fields(result: &Value) -> Result<Value> {
    let receipt = &result["receipt"];
    Ok(json!({
        "turn_hash": field(receipt, "transactionId")?,
        "receipt": receipt,
        "chain_index": number(field(receipt, "acceptedCount")?),
        "finality": "accepted",
    }))
}

fn merge(mut base: Value, extra: Value) -> Value {
    if let (Some(base), Value::Object(extra)) = (base.as_object_mut(), extra) {
        base.extend(extra);
    }
    base
}

fn send(flags: &Flags) -> Result<Value> {
    if flags.rest.is_empty() {
        return Err("send requires a payload".into());
    }
    if flags.to.is_some() || flags.amount.is_some() {
        return Err("send takes no --to: it always posts on the profile's own account".into());
    }
    if flags.fund.is_some() {
        return Err("--fund on send: Mini has no faucet; fund a profile at join or by a transfer".into());
    }
    let payload = flags.rest.join(" ");
    let profile = profile(flags)?;
    let (agent, reference, record) = joined(flags, &profile)?;
    let topic = fleet::topic_bytes(&flags.topic)?;
    if payload.len() > 16_384 {
        return Err("payload exceeds 16384 bytes".into());
    }
    let publication = json!({"topic":crate::hex(&topic),"sequence":"0","payload":crate::hex(payload.as_bytes())});
    let result = fleet::turn(&agent, &reference, "send", Value::Null, publication)?;
    let account = field(&record, "account")?;
    Ok(merge(
        json!({
            "sent": true, "node": agent_socket(&agent)?, "profile": profile.name,
            "agent_cell": account, "to": account, "topic": flags.topic, "payload": payload,
            "sequence": number(field(&result["publication"], "sequence")?),
            "fee": number(field(&result, "fee")?),
            "replans": number(field(&result, "replans")?),
            "confirmation": result["confirmation"], "attempt": result["attempt"],
        }),
        receipt_fields(&result)?,
    ))
}

fn transfer(flags: &Flags) -> Result<Value> {
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
    let result = fleet::turn(&agent, &reference, "transfer", transfer, Value::Null)?;
    Ok(merge(
        json!({
            "transferred": true, "committed": true, "node": agent_socket(&agent)?,
            "profile": profile.name, "from": from, "to": to, "amount": number(&amount),
            "fee": number(field(&result, "fee")?),
            "replans": number(field(&result, "replans")?),
            "confirmation": result["confirmation"], "attempt": result["attempt"],
        }),
        receipt_fields(&result)?,
    ))
}

fn receipt(flags: &Flags) -> Result<Value> {
    let profile = profile(flags)?;
    let (agent, reference, record) = joined(flags, &profile)?;
    match (&flags.turn_hash, flags.head) {
        (Some(transaction), false) => {
            let value = fleet::receipt_by_transaction(&agent, transaction)?;
            match field(&value, "type")? {
                "confirmed" if field(&value["receipt"], "transactionId")? == transaction => Ok(merge(
                    json!({"found": true, "profile": profile.name}),
                    receipt_fields(&value)?,
                )),
                "confirmed" => Err("the receipt lookup answered for another transaction".into()),
                other => Err(format!("no accepted transaction {transaction} ({other})")),
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
    let receipt = json!({
        "transactionId": outcome["transactionId"], "eventId": outcome["eventId"],
        "acceptedCount": outcome["acceptedCount"], "worldRoot": outcome["worldRoot"],
    });
    Ok(json!({
        "retried": true, "profile": profile.name, "confirmation": outcome["confirmation"],
        "turn_hash": outcome["transactionId"], "receipt": receipt,
        "chain_index": number(field(&outcome, "acceptedCount")?), "finality": "accepted",
    }))
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

pub(crate) fn run(argv: Vec<OsString>) -> Result<()> {
    let flags = parse(argv)?;
    let value = {
        let _progress = StdoutToStderr::hold()?;
        match flags.verb.as_str() {
            "join" => join(&flags),
            "send" => send(&flags),
            "transfer" => transfer(&flags),
            "receipt" => receipt(&flags),
            "retry" => retry(&flags),
            other => Err(format!("unknown verb '{other}' (try --help)")),
        }
    }?;
    println!(
        "{}",
        serde_json::to_string(&value).map_err(|error| format!("cannot render result: {error}"))?
    );
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
