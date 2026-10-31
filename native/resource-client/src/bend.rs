//! `mini bend` — author an Objective Bend (`.obend`) program and run it in the kernel.
//!
//! A bend turn IS an activity turn (`activity.rs`, Host ops 7 author / 210 plan / 211 assemble /
//! 212 submit / 213 lookup / 214 view): this verb only builds the turn bodies, the workspace key
//! signs through `activity::submit`, and the retained-ingress / exact-retry machinery is that
//! file's, unchanged. Everything lives under `WS/bend/`:
//!
//! ```text
//! WS/bend/NAME/spec.json            the package-input spec handed to the Host's front end
//! WS/bend/NAME/source/MODULE.obend  the source the spec names (a copy of the member's @FILE)
//! WS/bend/NAME/out/                 the Host's artifact.bin, package.bin, publication.json
//! WS/bend/NAME/attempts/…           one activity attempt directory per submitted turn
//! WS/bend/objects/REF.json          which bend an object runs and its birth transaction
//! ```
//!
//! * `mini bend --action publish --dir WS --name NAME --source FILE [--entry DEF] [--account REF]`
//!   runs the workspace's Host `objective-publication SPEC activity OUT` (the Host's own Lean front
//!   end captures and lowers the source; a refusal is printed as the Host's, nothing submitted),
//!   then submits the `publish` turn paid from the member's own account and spend capability.
//! * `mini bend --action run --dir WS --name NAME --object REF [--seed JSON] [--input JSON]
//!   [--deposit N] [--state-type JSON] [--account REF]` creates the object pinning the published
//!   package (when REF has no record yet), then births its activity under a full envelope.
//! * `mini bend --action show --dir WS --object REF` reads the object back (a public view, op 214).
//!
//! The Host publishes ONE envelope figure (`limits.extractTicks`) and the front end's quote of the
//! package (`pins[].frontEnd`); both are read from the view. The five other fixed envelope figures
//! and the tariff are the Objective invocation policy's every genesis pins
//! (`activity_world.policy_of`, `scripts/author-objective-policy.sh`); the Host does not publish them,
//! so they are mirrored below and tied to `activity_world.py` by `policy_mirror_matches_the_world`.
use crate::activity::{self, Ws};
use crate::agent_reserve::field;
use crate::*;
use serde_json::{json, Value};

/// The policy's maximum envelope, member by member (`activity_world.MAXIMUM`), in its order.
const ENVELOPE_KEYS: [&str; 22] = [
    "typeFuel", "sourceTicks", "heap", "stack", "outputNodes", "outputBytes", "extractTicks", "inputBytes",
    "scalarBits", "memoryTouches", "proofWork", "feeDebit", "turnBytes", "witnessBytes", "storageBytes",
    "sideEffectCount", "networkBytes", "leaseByteBlocks", "incidences", "replayBytes", "coreBytes", "domainWork",
];
/// The fixed members a full envelope declares at the policy maximum (`activity_world.cap`).
const FIXED: [(&str, u64); 5] =
    [("heap", 200000), ("stack", 200000), ("typeFuel", 16384), ("outputNodes", 20000), ("outputBytes", 200000)];
/// Tariff edition 4 (`activity_world.TARIFF`): base, source tick, replay byte, core byte.
const BASE: u128 = 1;
const TICK_RATE: u128 = 1;
const REPLAY_RATE: u128 = 6;
const CORE_RATE: u128 = 2;
/// The source ticks a bend's birth declares (`activity_world.BEND_TICKS`) and the multiple of its price the
/// default deposit reserves (`activity_world.BEND_PURSE_PRICES`, whose comment carries the measurement). Every leg
/// declares the same envelope, so every resume costs the purse one price; every yield must leave the await's pair
/// (two prices) and the record's storage deposit in it. The default carries `ANSWERS` delivered replies through to
/// the activity's end: the pair, one price per answer, and one price that covers the storage deposit (2,568 for the
/// Tally). A program that is answered more often needs `--deposit N`; the unspent purse returns when it ends.
const TICKS: u128 = 300;
const ANSWERS: u128 = 1;
const DEPOSIT_PRICES: u128 = ANSWERS + 3;
/// The declared state type `{total: Nat}` (the checker's type JSON) `Tally` and its siblings keep.
const TOTAL_STATE: &str = r#"{"tag":"field","name":"total","member":{"tag":"natural"},"tail":{"tag":"emptyRow"}}"#;

fn name_ok(name: &str) -> Result<()> {
    if name.is_empty() || name.len() > 64 || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
        return Err(format!("bend: `{name}` is not a bend name (1..64 ASCII letters, digits or hyphens)"));
    }
    Ok(())
}

fn text(args: &mut Args, name: &str) -> Result<String> {
    args.required(name)?.into_string().map_err(|_| format!("--{name} must be UTF-8"))
}

fn opt(args: &mut Args, name: &str) -> Result<Option<String>> {
    args.optional(name).map(|v| v.into_string().map_err(|_| format!("--{name} must be UTF-8"))).transpose()
}

fn json_flag(args: &mut Args, name: &str) -> Result<Option<Value>> {
    opt(args, name)?
        .map(|t| serde_json::from_str(&t).map_err(|e| format!("bend: --{name} is not JSON: {e}")))
        .transpose()
}

// ------------------------------------------------------------------ pure turn bodies

/// The package-input spec the Host's front end captures (`activity_world.publication`): one module,
/// named for its file, no imports; the entry is a definition of that module.
fn package_input(module: &str, source: &Path, entry: &str) -> Value {
    json!({"schema": "dregg.objective-bend.package-input.v1", "edition": "objective-bend-1",
           "modules": [{"name": module, "sourcePath": source, "imports": []}],
           "entryModule": "0", "entryDefinition": entry})
}

/// The price of a declared envelope (`Tariff.workOf`) of `ticks` source ticks and the front end's quote.
fn price(ticks: u128, replay: u128, core: u128) -> u128 {
    BASE + TICK_RATE * ticks + REPLAY_RATE * replay + CORE_RATE * core
}

/// A full envelope (`activity_world.cap`): the policy's fixed members, the extraction budget the Host
/// publishes, the front end's quote of the package, and `ticks` source ticks.
fn envelope(extract: u128, replay: u128, core: u128, ticks: u128) -> Value {
    let mut c: serde_json::Map<String, Value> = ENVELOPE_KEYS.iter().map(|k| ((*k).to_owned(), json!("0"))).collect();
    for (k, v) in FIXED {
        c.insert(k.into(), json!(v.to_string()));
    }
    c.insert("extractTicks".into(), json!(extract.to_string()));
    c.insert("replayBytes".into(), json!(replay.to_string()));
    c.insert("coreBytes".into(), json!(core.to_string()));
    c.insert("sourceTicks".into(), json!(ticks.to_string()));
    Value::Object(c)
}

fn publish_turn(artifact: &str, package: &str, payer: &str, payer_cap: &str) -> Value {
    json!({"kind": "publish", "artifact": artifact, "package": package, "payer": payer, "payerCapability": payer_cap})
}

fn create_turn(object: &str, object_cap: &str, pin: &str, state_type: &Value, seed: Option<&Value>, payer: &str, payer_cap: &str) -> Value {
    let mut turn = json!({"kind": "create", "object": object, "objectCapability": object_cap, "pin": pin,
        "stateType": state_type, "law": {"type": "all", "predicates": []}, "upgrade": {"frozen": {}},
        "payer": payer, "payerCapability": payer_cap});
    if let Some(seed) = seed {
        turn["seed"] = seed.clone();
    }
    turn
}

#[allow(clippy::too_many_arguments)]
fn birth_turn(object: &str, object_cap: &str, account: &str, account_cap: &str, pin: &str, input: &Value, envelope: &Value, deposit: u128) -> Value {
    json!({"kind": "birth", "object": object, "objectCapability": object_cap, "account": account,
        "accountCapability": account_cap, "pin": pin, "input": input,
        "envelope": envelope, "resume": envelope, "timeout": envelope, "deposit": deposit.to_string()})
}

/// What `Tally` starts from: `{init: set 0, decider: SUBJECT}` (the member answers their own awaits) on an
/// object with no declared state yet, and `{init: keep}` on one that has it: the kernel admits a `set` only
/// from the birth that creates the state (`blindWrite`), so a later run on the same object joins its total.
/// Any other program names its input with `--input`.
fn default_input(subject: &str, state_exists: bool) -> Value {
    let init = if state_exists { json!({"tag": "variant", "label": "keep", "payload": {"tag": "record", "fields": []}}) }
        else { json!({"tag": "variant", "label": "set", "payload": {"tag": "natural", "value": "0"}}) };
    json!({"tag": "record", "fields": [
        {"name": "init", "value": init},
        {"name": "decider", "value": {"tag": "natural", "value": subject}}]})
}

/// A data value, as the member reads it: `3`, `{total=3}`, `set(0)`; anything else compact JSON.
fn data_text(v: &Value) -> String {
    match v.get("tag").and_then(Value::as_str) {
        Some("natural") => v.get("value").and_then(Value::as_str).unwrap_or("?").to_owned(),
        Some("record") => format!("{{{}}}", v.get("fields").and_then(Value::as_array).map(|fs| fs.iter()
            .map(|f| format!("{}={}", f.get("name").and_then(Value::as_str).unwrap_or("?"), data_text(f.get("value").unwrap_or(&Value::Null))))
            .collect::<Vec<_>>().join(", ")).unwrap_or_default()),
        Some("variant") => format!("{}({})", v.get("label").and_then(Value::as_str).unwrap_or("?"),
            data_text(v.get("payload").unwrap_or(&Value::Null))),
        _ => v.to_string(),
    }
}

/// How the Host decided a submitted turn.
#[derive(Debug, PartialEq)]
enum Decided {
    /// Admitted: the height the turn was judged at (`judged_height`), world root, receipt (transaction, event),
    /// how it confirmed.
    Admitted { height: String, root: String, receipt: String, how: String },
    Refused(String),
    Undecided(String),
}

/// The logical height a turn was judged at, from its receipt's accepted count: the Host's clock is
/// `genesisHeight + |accepted|` (`NativeHost.logicalHeight`), a turn is judged at the height before it is
/// appended, so the receipt of the k-th accepted turn reads `genesisHeight + k - 1`. It is the clock an await's
/// `yieldedAt` and `deadline` and the view's `height` are on (the view's height is the one the NEXT turn is judged
/// at), so a receipt, `bend await` and `bend show` print one scale.
fn judged_height(genesis: u128, accepted: &str) -> String {
    accepted.parse::<u128>().ok().and_then(|k| genesis.checked_add(k.checked_sub(1)?)).map(|h| h.to_string())
        .unwrap_or_else(|| "?".into())
}

fn decided(outcome: &Value, genesis: u128) -> Decided {
    let s = |k: &str| outcome.get(k).and_then(Value::as_str).unwrap_or("?").to_owned();
    if let Some(line) = crate::charged_line(outcome) {
        return Decided::Refused(line);
    }
    match outcome.get("type").and_then(Value::as_str) {
        Some("confirmed") => Decided::Admitted {
            height: judged_height(genesis, &s("acceptedCount")),
            root: s("worldRoot"),
            receipt: format!("tx {} event {}", s("transactionId"), s("eventId")),
            how: s("confirmation"),
        },
        Some("refused") => Decided::Refused(
            crate::refusal_line(outcome).unwrap_or_else(|| "refused: unnamed".into()).trim_start_matches("refused: ").to_owned()),
        other => Decided::Undecided(format!("Host outcome {}", other.unwrap_or("untyped"))),
    }
}

/// Record a Host's refusal (the shell and `mini` render it with its exit code) and finish the verb.
fn ending(error: String) -> Result<()> {
    if let Some(m) = error.strip_prefix("refused: ").or_else(|| error.strip_prefix("never forwarded: ")) {
        note_command_ending(CommandEnding::Refused(m.to_owned()));
        Ok(())
    } else {
        Err(error)
    }
}

/// The refusal for a payer that cannot cover the run: nothing is submitted.
fn unfunded_refusal(name: &str, object_ref: &str, held: u128, cost: u128) -> String {
    format!("refused: unfunded: run {name} on {object_ref} costs {cost} (its purse deposit plus the birth envelope's price) and your account holds {held}; nothing was submitted (--deposit N sets a smaller purse)")
}

/// The Host-free refusal for an object name that is not here: nothing is submitted.
fn no_object_refusal(name: &str) -> String {
    format!("refused: no object named {name}: make one with `create {name} content open`")
}

fn absent_object(root: &Path, name: &str) -> Option<String> {
    let file = root.join("refs").join(format!("{}.json", workspace::ref_file(name)));
    (!name.contains('/') && !file.exists()).then(|| no_object_refusal(name))
}

/// The two shell lines that recover a turn whose answer was not read.
fn recovery(name: &str) -> String {
    format!("`bend lookup {name}` asks the Host for the decided outcome of the retained ingress (absence never submits); \
             `bend retry {name}` submits the same retained bytes again (never a new nonce)")
}

/// `ending`, with an undecided turn (a reply not read, or an earlier attempt of the same turn still
/// undecided) naming `bend lookup` and `bend retry` rather than the activity client's own verbs.
fn ending_for(name: &str, error: String) -> Result<()> {
    if error.starts_with("uncertain host") || error.starts_with("undecided: ") {
        let what = error.strip_prefix("undecided: ").unwrap_or(&error);
        let what = if what.starts_with("this turn's exact ingress") { "the last attempt of this turn may have been admitted" } else { what };
        note_command_ending(CommandEnding::Undecided(format!("{what}; {}", recovery(name))));
        Ok(())
    } else {
        ending(error)
    }
}

// ------------------------------------------------------------------ the workspace

struct Bend {
    ws: Ws,
    pin: Value,
    /// The deployment's `genesisHeight` (its pinned config): receipts print heights on the Host's logical clock.
    genesis: u128,
}

impl Bend {
    fn open(root: PathBuf) -> Result<Self> {
        let bytes = fs::read(root.join("workspace.json")).map_err(|e| format!("bend: cannot read workspace.json: {e}"))?;
        let pin: Value = serde_json::from_slice(&bytes).map_err(|e| format!("bend: invalid workspace.json: {e}"))?;
        let ws = activity::ws(root)?;
        let config: Value = serde_json::from_slice(&fs::read(&ws.config).map_err(|e| format!("bend: cannot read {}: {e}", ws.config.display()))?)
            .map_err(|e| format!("bend: {}: {e}", ws.config.display()))?;
        let genesis = match &config["genesisHeight"] {
            Value::Number(n) => n.as_u64().map(u128::from),
            Value::String(t) => t.parse().ok(),
            _ => None,
        }.ok_or_else(|| format!("bend: {} names no genesisHeight", ws.config.display()))?;
        Ok(Self { ws, pin, genesis })
    }

    fn dir(&self, name: &str) -> PathBuf {
        self.ws.root.join("bend").join(name)
    }

    /// The member's own account and the capability that spends from it (`--account REF`, else the
    /// workspace's one account reference, as `credit` finds it).
    fn payer(&self, explicit: Option<&str>) -> Result<(String, String)> {
        let name = crate::credit::my_account(&self.ws.root, &self.pin, explicit)?;
        let reference = workspace::reference(&self.ws.root, &name)?;
        let capability = reference.get("operationCapability").or_else(|| reference.get("observeCapability"))
            .and_then(Value::as_str).ok_or_else(|| format!("bend: account reference {name} names no capability"))?;
        Ok((field(&reference, "target")?.to_owned(), capability.to_owned()))
    }

    /// The refusal for an object name this workspace has no reference to (`None` when it has one, or
    /// the name is a shared `room/name`, which resolves through the room): the member makes the cell
    /// first with the shell verb that makes a content cell they own; `bend` never makes one.
    fn no_object(&self, name: &str) -> Option<String> {
        absent_object(&self.ws.root, name)
    }

    /// The content resource REF: (object cell, its operation capability).
    fn object(&self, name: &str) -> Result<(String, String)> {
        let reference = workspace::reference(&self.ws.root, name)?;
        let capability = reference.get("operationCapability").and_then(Value::as_str)
            .ok_or_else(|| format!("bend: {name} names no operation capability (a resource you may write)"))?;
        Ok((field(&reference, "target")?.to_owned(), capability.to_owned()))
    }

    /// One turn under a fresh attempt directory, described by `meta` (retained beside it as
    /// `ATTEMPT.meta.json`, so `bend lookup` and `bend retry` know what the attempt was). With
    /// `lose`, the Host's reply to the submission is deliberately not read (the shell's lost-reply
    /// switch, `transport`): the attempt stays retained and undecided.
    fn submit(&self, name: &str, step: &str, turn: &Value, meta: &Value, lose: bool) -> Result<(Decided, Value)> {
        self.submit_again(name, step, turn, meta, lose, false)
    }

    /// `submit`, with `again`: the member's decision to sign once more a turn whose identical twin this workspace
    /// already had decided (`activity::turn_nonce`; `bend run --again`).
    fn submit_again(&self, name: &str, step: &str, turn: &Value, meta: &Value, lose: bool, again: bool) -> Result<(Decided, Value)> {
        let attempts = self.dir(name).join("attempts");
        crate::fsio::ensure_private_dir_all(&attempts)?;
        let out = attempts.join(format!("{step}-{}", &crate::fsio::random_nonce()?[..8]));
        let mut meta = meta.clone();
        meta["step"] = json!(step);
        crate::fsio::retain_json(&attempts.join(format!("{}.meta.json", out.file_name().and_then(|n| n.to_str()).unwrap_or("attempt"))), &meta)?;
        if lose {
            std::env::set_var(mini_sdk::operator::LOSE_REPLY_ENV, mini_sdk::host_operations::ACTIVITY_SUBMIT.to_string());
        }
        let outcome = activity::submit(&self.ws, turn, &out, false, None, again);
        std::env::remove_var(mini_sdk::operator::LOSE_REPLY_ENV);
        let outcome = outcome?;
        Ok((decided(&outcome, self.genesis), outcome))
    }

    /// The newest attempt of NAME that reached an ingress: (its directory, its meta).
    fn latest(&self, name: &str) -> Result<(PathBuf, Value)> {
        let attempts = self.dir(name).join("attempts");
        let mut found: Vec<(std::time::SystemTime, PathBuf, Value)> = Vec::new();
        for entry in fs::read_dir(&attempts).map_err(|_| format!("bend: {name} has no attempts here"))? {
            let entry = entry.map_err(|e| e.to_string())?;
            let file = entry.file_name().to_string_lossy().into_owned();
            let Some(stem) = file.strip_suffix(".meta.json") else { continue };
            let dir = attempts.join(stem);
            if !dir.join("ingress.bin").is_file() {
                continue;
            }
            let meta: Value = serde_json::from_slice(&fs::read(entry.path()).map_err(|e| e.to_string())?).map_err(|e| format!("bend: {file}: {e}"))?;
            found.push((entry.metadata().and_then(|m| m.modified()).map_err(|e| e.to_string())?, dir, meta));
        }
        found.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
        found.pop().map(|(_, dir, meta)| (dir, meta)).ok_or_else(|| format!("bend: no attempt of {name} reached the Host (nothing to look up)"))
    }
}

fn published(bend: &Bend, name: &str) -> Result<Value> {
    let path = bend.dir(name).join("out").join("publication.json");
    let bytes = fs::read(&path).map_err(|_| format!("bend: {name} is not published here: `bend publish {name} @FILE`"))?;
    serde_json::from_slice(&bytes).map_err(|e| format!("bend: {}: {e}", path.display()))
}

// ------------------------------------------------------------------ publish

fn publish(bend: &Bend, mut args: Args) -> Result<()> {
    let name = text(&mut args, "name")?;
    let source = path(args.required("source")?);
    let entry = opt(&mut args, "entry")?.unwrap_or_else(|| name.clone());
    let account = opt(&mut args, "account")?;
    let lose = lose_flag(&mut args)?;
    args.finish()?;
    name_ok(&name)?;
    let module = source.file_stem().and_then(|s| s.to_str()).filter(|s| !s.is_empty()).ok_or("bend: --source names no file")?.to_owned();
    let bytes = fs::read(&source).map_err(|e| format!("bend: cannot read {}: {e}", source.display()))?;
    let dir = bend.dir(&name);
    crate::fsio::ensure_private_dir_all(&dir.join("source"))?;
    let kept = dir.join("source").join(format!("{module}.obend"));
    let spec = package_input(&module, &kept, &entry);
    let spec_bytes = serde_json::to_vec(&spec).map_err(|e| e.to_string())?;
    let out = dir.join("out");
    if out.join("publication.json").is_file() {
        // The same bend again (a retry after a lost reply): the same spec reuses the front end's
        // output; another source under this name is another bend.
        if fs::read(dir.join("spec.json")).ok().as_deref() != Some(&spec_bytes) || fs::read(&kept).ok().as_deref() != Some(&bytes) {
            return Err(format!("bend: {name} is already published here with other source; publish the new source under another name"));
        }
    } else {
        if kept.exists() {
            fs::remove_file(&kept).map_err(|e| format!("bend: {e}"))?;
        }
        crate::fsio::create_private(&kept, &bytes)?;
        let spec_path = dir.join("spec.json");
        if spec_path.exists() {
            fs::remove_file(&spec_path).map_err(|e| format!("bend: {e}"))?;
        }
        crate::fsio::create_private(&spec_path, &spec_bytes)?;
        let output = std::process::Command::new(&bend.ws.host)
            .arg(&bend.ws.config)
            .args(["objective-publication"])
            .arg(&spec_path)
            .arg("activity")
            .arg(&out)
            .output()
            .map_err(|e| format!("bend: cannot run the Host: {e}"))?;
        if !output.status.success() {
            // The Host's front end refused the source: its diagnostic, by name; nothing was submitted.
            let said = String::from_utf8_lossy(&output.stderr);
            let said = said.trim().trim_start_matches("uncaught exception:").trim();
            note_command_ending(CommandEnding::Refused(format!(
                "front-end: the Host's Objective Bend front end refused {}: {}; nothing was submitted",
                source.display(), said.split_whitespace().collect::<Vec<_>>().join(" "))));
            return Ok(());
        }
    }
    let publication: Value = serde_json::from_slice(&fs::read(out.join("publication.json")).map_err(|e| format!("bend: {e}"))?)
        .map_err(|e| format!("bend: publication.json: {e}"))?;
    let artifact_id = field(&publication, "artifactId")?.to_owned();
    let package_id = field(&publication, "packageId")?.to_owned();
    let hex = |file: &str| fs::read(out.join(file)).map(|b| mini_sdk::hex::encode(&b)).map_err(|e| format!("bend: {file}: {e}"));
    let (payer, payer_cap) = bend.payer(account.as_deref())?;
    let turn = publish_turn(&hex("artifact.bin")?, &hex("package.bin")?, &payer, &payer_cap);
    let meta = json!({"kind": "publish", "bend": name, "artifactId": artifact_id, "packageId": package_id});
    match bend.submit(&name, "publish", &turn, &meta, lose).map(|(d, _)| d) {
        Err(e) => ending_for(&name, e),
        Ok(decided) => report(bend, &name, &meta, None, "bend publish", decided),
    }
}

/// `--lose-reply-once`: the shell's lost-reply switch, armed for the turn's submission only.
fn lose_flag(args: &mut Args) -> Result<bool> {
    Ok(opt(args, "lose-reply-once")?.as_deref() == Some("true"))
}

/// What the shell adds to a Host refusal of an attempt described by `meta`, when the Host's words are true but
/// do not say what happened (an exact repeat of an admitted turn is `transaction identity conflict`).
fn refusal_hint(meta: &Value, r: &str) -> String {
    let m = |k: &str| meta.get(k).and_then(Value::as_str).unwrap_or("?").to_owned();
    match m("kind").as_str() {
        // A second publish of the same source names the same artifact and package, so the Host
        // sees a replay of an admitted transaction identity.
        "publish" if r.contains("transaction identity conflict") => format!(
            " (this package is already published: artifact {} package {}; `bend run` it)", m("artifactId"), m("packageId")),
        "resolve" if r.contains("responseType") => " (the reply's DATA does not have the shape this slot's ask declared; \
            answer with exactly the response type the asking program names, or {\"refused\": REASON})".to_owned(),
        // The same answer to the same slot (a retry after a restart or a lost reply, typed again) is the
        // same transaction identity under a fresh ingress: the slot was already decided by it.
        "resolve" | "deliver" if r.contains("transaction identity conflict") => format!(" ({})", already_done(meta)),
        _ => String::new(),
    }
}

/// What an exact repeat of an admitted answer or delivery is: the slot already answered, the await
/// already delivered (the same answer again changes nothing; another answer is refused by the slot).
fn already_done(meta: &Value) -> String {
    let m = |k: &str| meta.get(k).and_then(Value::as_str).unwrap_or("?").to_owned();
    if m("kind") == "deliver" {
        format!("await {} is already delivered; nothing changed: `bend await` shows where the activity is now", m("await"))
    } else {
        format!("slot {} is already answered with this answer; nothing changed: `bend deliver` resumes the activity", m("slot"))
    }
}

/// A run identical to one this workspace already had decided (same bend, object, input and deposit) is not
/// signed again by accident; running it once more is the member's decision, and the line that makes it is
/// `bend run NAME OBJECT --again` (the activity client's own words name its `--again true`, not a bend verb).
fn run_again(name: &str, object_ref: &str, error: String) -> String {
    match error.strip_prefix("activity: this turn was already submitted (") {
        Some(rest) => {
            let kind = rest.split(';').next().unwrap_or("decided");
            let kind = if kind == "confirmed" { "admitted" } else { kind };
            format!("refused: run {name} on {object_ref}: this exact run was already {kind}; nothing was submitted. \
                A second run with the same input is a new activity: `bend run {name} {object_ref} --again`")
        }
        None => error,
    }
}

/// The activity client refuses to sign an exact repeat of a turn this workspace already had decided
/// (`activity::turn_nonce`). For an answer or a delivery that repeat is never a second decision, so it
/// is refused by name (nothing is submitted) rather than offered `--again`.
fn repeated(meta: &Value, error: String) -> String {
    if error.starts_with("activity: this turn was already submitted (confirmed;") {
        format!("refused: {}", already_done(meta))
    } else {
        error
    }
}

/// Print the Host's decision on an attempt described by `meta`, or record its refusal / undecided ending.
/// `lead` names the verb (`bend publish`, `bend lookup`, `bend retry`).
fn report(bend: &Bend, name: &str, meta: &Value, transaction: Option<String>, lead: &str, d: Decided) -> Result<()> {
    let m = |k: &str| meta.get(k).and_then(Value::as_str).unwrap_or("?").to_owned();
    match d {
        Decided::Refused(r) => {
            let hint = refusal_hint(meta, &r);
            ending(format!("refused: {r}{hint}"))
        }
        Decided::Undecided(r) => ending_for(name, format!("undecided: {r}")),
        Decided::Admitted { height, root, receipt, how } => match m("kind").as_str() {
            "publish" => {
                println!("admitted: {lead} {name} ({how}): artifact {} package {}, height {height}, world root {root}, receipt {receipt}", m("artifactId"), m("packageId"));
                Ok(())
            }
            "run" => {
                let tx = transaction.ok_or("bend: the attempt names no transaction")?;
                finish_run(bend, name, meta, &tx, &format!("{lead} {name} ({how}) on {}", m("objectRef")), &height, &root, &receipt, None, None)
            }
            _ => {
                println!("admitted: {lead} {name} ({how}): {} turn, height {height}, world root {root}, receipt {receipt}", m("kind"));
                Ok(())
            }
        },
    }
}

/// The birth transaction an attempt's plan names (Host inspection of its retained `plan.bin`).
fn transaction_of(bend: &Bend, dir: &Path) -> Result<String> {
    let plan = fs::read(dir.join("plan.bin")).map_err(|e| format!("bend: {}: {e}", dir.join("plan.bin").display()))?;
    let inspected = activity::inspect(&bend.ws, "objective-activity-plan", &plan)?;
    inspected.pointer("/command/transaction").map(|t| t.as_str().map(str::to_owned).unwrap_or_else(|| t.to_string()))
        .ok_or_else(|| "bend: the plan names no transaction".to_owned())
}

/// `bend lookup NAME`: the receipt-only lookup (op 213) of NAME's last attempt's retained ingress.
/// The decided Host answer an attempt retained (`outcome.json` of type confirmed or refused).
fn retained_decision(dir: &Path) -> Option<Value> {
    let outcome: Value = serde_json::from_slice(&fs::read(dir.join("outcome.json")).ok()?).ok()?;
    matches!(outcome.get("type").and_then(Value::as_str), Some("confirmed" | "refused")).then_some(outcome)
}

fn lookup_cmd(bend: &Bend, mut args: Args, retry: bool) -> Result<()> {
    let name = text(&mut args, "name")?;
    args.finish()?;
    name_ok(&name)?;
    let (dir, meta) = bend.latest(&name)?;
    let ingress = dir.join("ingress.bin");
    // The attempt's own decided answer (the Host's confirmation or refusal of exactly this
    // ingress, retained when it was read) is the decided record. A receipt lookup cannot
    // recover a refusal (a refused ingress leaves no receipt), so a lookup answers from it.
    let retained = (!retry).then(|| retained_decision(&dir)).flatten();
    let outcome = match retained {
        Some(decision) => Ok(decision),
        None if retry => activity::resubmit(&bend.ws, &ingress),
        None => activity::lookup(&bend.ws, &ingress),
    };
    let outcome = match outcome {
        Ok(o) => o,
        Err(e) => return ending_for(&name, e),
    };
    let d = decided(&outcome, bend.genesis);
    let transaction = if matches!(d, Decided::Admitted { .. }) && meta.get("kind").and_then(Value::as_str) == Some("run") { Some(transaction_of(bend, &dir)?) } else { None };
    report(bend, &name, &meta, transaction, if retry { "bend retry" } else { "bend lookup" }, d)
}

// ------------------------------------------------------------------ run

fn balance(view: &Value, account: &str) -> Option<u128> {
    view.get("balances")?.as_array()?.iter().find(|b| b.get("account").and_then(Value::as_str) == Some(account))?
        .get("balance")?.as_str()?.parse().ok()
}

fn cell_of<'a>(view: &'a Value, cell: &str) -> Option<&'a Value> {
    view.get("cells")?.as_array()?.iter().find(|c| c.get("cell").and_then(Value::as_str) == Some(cell))
}

fn decimal_of(v: &Value, ptr: &str) -> Option<u128> {
    v.pointer(ptr)?.as_str()?.parse().ok()
}

fn run_bend(bend: &Bend, mut args: Args) -> Result<()> {
    let name = text(&mut args, "name")?;
    let object_ref = text(&mut args, "object")?;
    let seed = json_flag(&mut args, "seed")?;
    let input = json_flag(&mut args, "input")?;
    let state_type = json_flag(&mut args, "state-type")?;
    let deposit = opt(&mut args, "deposit")?;
    let account = opt(&mut args, "account")?;
    let lose = lose_flag(&mut args)?;
    let again = opt(&mut args, "again")?.as_deref() == Some("true");
    args.finish()?;
    name_ok(&name)?;
    if let Some(refusal) = bend.no_object(&object_ref) {
        return ending(refusal);
    }
    let deposit: Option<u128> = deposit
        .map(|d| if mini_sdk::decimal::is_canonical_max(&d, 30) { d.parse().map_err(|_| "bend: --deposit is too large".to_owned()) } else { Err("bend: --deposit must be a canonical decimal".to_owned()) })
        .transpose()?;
    let publication = published(bend, &name)?;
    let pin = field(&publication, "artifactId")?.to_owned();
    let (payer, payer_cap) = bend.payer(account.as_deref())?;
    let (object, object_cap) = bend.object(&object_ref)?;
    let view = activity::view(&bend.ws, &json!({"objects": [&object], "pins": [&pin], "accounts": [&payer]}))?;
    let front = view.pointer("/pins/0/frontEnd").filter(|f| f.is_object()).ok_or_else(|| format!(
        "bend: the chain holds no package for {name} (artifact {pin}): its publish turn was not admitted; run `bend publish {name} @FILE` again"))?;
    let (replay, core) = (decimal_of(front, "/replayBytes").ok_or("bend: front-end quote lacks replayBytes")?,
        decimal_of(front, "/coreBytes").ok_or("bend: front-end quote lacks coreBytes")?);
    let extract = decimal_of(&view, "/limits/extractTicks").ok_or("bend: the Host published no extraction budget")?;
    let before = balance(&view, &payer);
    let object_cell = view.pointer("/objects/0/objectCell").and_then(Value::as_str).ok_or("bend: view names no object cell")?;
    let has_record = cell_of(&view, object_cell).and_then(|c| c.get("kind")).and_then(Value::as_str) == Some("object-record");
    // The run costs its deposit (the activity's purse) plus the birth envelope's price. A payer that
    // holds less is told so before anything is signed, with the figures (the Host would refuse it
    // `unfunded` after the create turn already landed).
    let cost = deposit.unwrap_or(DEPOSIT_PRICES * price(TICKS, replay, core)) + price(TICKS, replay, core);
    if let Some(held) = before.filter(|held| *held < cost) {
        return ending(unfunded_refusal(&name, &object_ref, held, cost));
    }
    let mut created = None;
    if !has_record {
        let state_type = state_type.unwrap_or_else(|| serde_json::from_str(TOTAL_STATE).expect("a constant"));
        let turn = create_turn(&object, &object_cap, &pin, &state_type, seed.as_ref(), &payer, &payer_cap);
        let meta = json!({"kind": "create", "bend": name, "objectRef": object_ref});
        match bend.submit(&name, "create", &turn, &meta, false) {
            Err(e) => return ending_for(&name, e),
            Ok((Decided::Admitted { height, .. }, _)) => created = Some(height),
            Ok((Decided::Refused(m), _)) => return ending(format!("refused: create {object_ref}: {m}")),
            Ok((Decided::Undecided(m), _)) => return ending_for(&name, format!("undecided: create {object_ref}: {m}")),
        }
    } else if seed.is_some() {
        return Err(format!("bend: {object_ref} already has a record; --seed is the creation's"));
    }
    let envelope = envelope(extract, replay, core, TICKS);
    let deposit = deposit.unwrap_or(DEPOSIT_PRICES * price(TICKS, replay, core));
    let state_exists = view.pointer("/objects/0/stateCell").and_then(Value::as_str).and_then(|c| cell_of(&view, c))
        .is_some_and(|c| c.get("value").is_some_and(|v| !v.is_null()));
    let input = input.unwrap_or_else(|| default_input(&bend.ws.subject, state_exists));
    let turn = birth_turn(&object, &object_cap, &payer, &payer_cap, &pin, &input, &envelope, deposit);
    let meta = json!({"kind": "run", "bend": name, "objectRef": object_ref, "object": object, "pin": pin, "payer": payer, "deposit": deposit.to_string()});
    let (how, outcome) = match bend.submit_again(&name, "birth", &turn, &meta, lose, again) {
        Err(e) => return ending_for(&name, run_again(&name, &object_ref, e)),
        Ok((Decided::Refused(m), _)) => return ending(format!("refused: run {name} on {object_ref}: {m}")),
        Ok((Decided::Undecided(m), _)) => return ending_for(&name, format!("undecided: run {name} on {object_ref}: {m}")),
        Ok((admitted, outcome)) => (admitted, outcome),
    };
    let Decided::Admitted { height, root, receipt, .. } = how else { unreachable!("matched above") };
    let transaction = outcome.get("transaction").map(|t| t.as_str().map(str::to_owned).unwrap_or_else(|| t.to_string())).unwrap_or_default();
    finish_run(bend, &name, &meta, &transaction, &format!("bend run {name} on {object_ref}"), &height, &root, &receipt, before, created)
}

/// The admitted run's line: the Host's decision, the object's declared state and the activity's purse
/// read back through the view; the object's registry entry (`bend show` reads it).
#[allow(clippy::too_many_arguments)]
fn finish_run(bend: &Bend, name: &str, meta: &Value, transaction: &str, lead: &str, height: &str, root: &str, receipt: &str,
              before: Option<u128>, created: Option<String>) -> Result<()> {
    let m = |k: &str| meta.get(k).and_then(Value::as_str).unwrap_or("?").to_owned();
    let (object, payer, pin, object_ref, deposit) = (m("object"), m("payer"), m("pin"), m("objectRef"), m("deposit"));
    let now = activity::view(&bend.ws, &json!({"objects": [&object], "births": [{"object": &object, "transaction": transaction}], "accounts": [&payer]}))?;
    let record_cell = now.pointer("/births/0/record").and_then(Value::as_str).unwrap_or_default().to_owned();
    let purse = activity::view(&bend.ws, &json!({"accounts": [&record_cell]}))?;
    let state = now.pointer("/objects/0/stateCell").and_then(Value::as_str).and_then(|c| cell_of(&now, c))
        .and_then(|c| c.get("value")).map(data_text).unwrap_or_else(|| "(none)".into());
    let after = balance(&now, &payer);
    let mut line = format!("admitted: {lead}: height {height}, world root {root}, receipt {receipt}; state {state}; purse {}; deposit {deposit}",
        balance(&purse, &record_cell).map(|b| b.to_string()).unwrap_or_else(|| "?".into()));
    if let (Some(b), Some(a)) = (before, after) {
        line.push_str(&format!("; account {b} -> {a} (charge {})", b.saturating_sub(a)));
    }
    if let Some(h) = created {
        line.push_str(&format!("; object created at height {h}"));
    }
    let registry = bend.ws.root.join("bend").join("objects");
    crate::fsio::ensure_private_dir_all(&registry)?;
    // The object's newest birth is the row (a later run on the same object replaces an ended one's).
    let path = registry.join(format!("{}.json", workspace::ref_file(&object_ref)));
    let old: Option<Value> = fs::read(&path).ok().and_then(|b| serde_json::from_slice(&b).ok());
    let row = next_row(old.as_ref(), json!({"bend": name, "pin": pin, "object": object, "transaction": transaction, "record": record_cell}));
    let _ = crate::fsio::replace_private(&path, &row_bytes(&row));
    println!("{line}");
    Ok(())
}

// ------------------------------------------------------------------ show

fn show(bend: &Bend, mut args: Args) -> Result<()> {
    let object_ref = text(&mut args, "object")?;
    args.finish()?;
    if let Some(refusal) = bend.no_object(&object_ref) {
        return ending(refusal);
    }
    let (object, _) = bend.object(&object_ref)?;
    let known: Option<Value> = fs::read(bend.ws.root.join("bend").join("objects").join(format!("{}.json", workspace::ref_file(&object_ref))))
        .ok().and_then(|b| serde_json::from_slice(&b).ok());
    let mut request = json!({"objects": [&object]});
    if let Some(k) = &known {
        request["births"] = json!([{"object": &object, "transaction": k.get("transaction")}]);
    }
    let view = activity::view(&bend.ws, &request)?;
    let cell = |ptr: &str| view.pointer(ptr).and_then(Value::as_str).and_then(|c| cell_of(&view, c));
    let Some(record) = cell("/objects/0/objectCell").filter(|c| c.get("kind").and_then(Value::as_str) == Some("object-record")) else {
        println!("{object_ref}: object cell {object}, no activity record (never created by a bend)");
        return Ok(());
    };
    let state = cell("/objects/0/stateCell");
    println!("{object_ref}: object cell {object}, pin {}, state {} (version {}), height {}",
        record.get("pin").and_then(Value::as_str).unwrap_or("?"),
        state.and_then(|c| c.get("value")).map(data_text).unwrap_or_else(|| "(none)".into()),
        state.and_then(|c| c.get("version")).map(|v| v.to_string().trim_matches('"').to_owned()).unwrap_or_else(|| "?".into()),
        view.get("height").and_then(Value::as_str).unwrap_or("?"));
    if let Some(k) = known {
        let record_cell = k.get("record").and_then(Value::as_str).unwrap_or_default();
        let purse = activity::view(&bend.ws, &json!({"accounts": [record_cell]}))?;
        let phase = cell_of(&view, record_cell).and_then(|c| c.pointer("/record/phase")).map(|p| p.to_string()).unwrap_or_else(|| "?".into());
        println!("  bend {}: activity record {record_cell}, purse {}, phase {phase}",
            k.get("bend").and_then(Value::as_str).unwrap_or("?"),
            balance(&purse, record_cell).map(|b| b.to_string()).unwrap_or_else(|| "?".into()));
    }
    Ok(())
}

// ------------------------------------------------------------------ await / answer

fn decimal_arg(value: &str, what: &str) -> Result<()> {
    if mini_sdk::decimal::is_canonical_max(value, 80) { Ok(()) } else { Err(format!("bend: {what} must be a canonical decimal")) }
}

/// `bend await OBJECT TRANSACTION`: the activity that birth made, as one JSON line (the read a
/// resident's `mini_pending_awaits` is built on). Absent record: phase `none`. Its `height` is the view's: the
/// height the next turn is judged at, the clock of `deadline` and of every receipt's height (`judged_height`).
fn await_cmd(bend: &Bend, mut args: Args) -> Result<()> {
    let object = text(&mut args, "object")?;
    let transaction = text(&mut args, "transaction")?;
    args.finish()?;
    decimal_arg(&object, "OBJECT")?;
    decimal_arg(&transaction, "TRANSACTION")?;
    let view = activity::view(&bend.ws, &json!({"objects": [&object], "births": [{"object": &object, "transaction": &transaction}]}))?;
    println!("{}", await_of_view(&view, &object, &transaction));
    Ok(())
}

fn await_of_view(view: &Value, object: &str, transaction: &str) -> Value {
    let record_cell = view.pointer("/births/0/record").and_then(Value::as_str).unwrap_or_default();
    let phase = cell_of(view, record_cell).and_then(|c| c.pointer("/record/phase"));
    let state = view.pointer("/objects/0/stateCell").and_then(Value::as_str).and_then(|c| cell_of(view, c)).and_then(|c| c.get("value"));
    let mut out = json!({"type": "mini-bend-await-v1", "object": object, "transaction": transaction, "record": record_cell,
        "height": view.get("height"), "phase": phase.and_then(|p| p.get("kind")).cloned().unwrap_or(json!("none")),
        "state": state.cloned().unwrap_or(Value::Null), "stateText": state.map(data_text)});
    if let Some(source) = phase.and_then(|p| p.pointer("/await/source")).filter(|s| s.get("kind") == Some(&json!("reply"))) {
        out["slot"] = source.get("slot").cloned().unwrap_or(Value::Null);
        out["decider"] = source.get("decider").cloned().unwrap_or(Value::Null);
        out["deadline"] = phase.and_then(|p| p.pointer("/await/deadline")).cloned().unwrap_or(Value::Null);
    }
    out
}

/// `bend deliver OBJECT TRANSACTION [--account REF]`: resume the activity with the settled outcome
/// of the await it is on (the slot's decided answer, or `timedOut` past the deadline): one deliver
/// turn, paid from my account. Anyone may deliver; the await id is spent once (a second delivery of
/// the same await is refused). The attempt name is fixed per await, for `bend lookup`/`bend retry`.
fn deliver_cmd(bend: &Bend, mut args: Args) -> Result<()> {
    let object = text(&mut args, "object")?;
    let transaction = text(&mut args, "transaction")?;
    let account = opt(&mut args, "account")?;
    args.finish()?;
    decimal_arg(&object, "OBJECT")?;
    decimal_arg(&transaction, "TRANSACTION")?;
    let view = activity::view(&bend.ws, &json!({"objects": [&object], "births": [{"object": &object, "transaction": &transaction}]}))?;
    // Nothing to deliver (not awaiting; the await not yet decided nor past its deadline) is the Host's
    // view refusing, by name: a refusal ending, not a client error.
    let found = match deliverable(&view) { Ok(found) => found, Err(e) => return ending(e) };
    match deliver_turn(bend, &object, &transaction, found, account.as_deref())? {
        Delivery::Refused(e) => ending(e),
        Delivery::Submitted(name, meta, Err(e)) => ending_for(&name, repeated(&meta, e)),
        Delivery::Submitted(name, meta, Ok(d)) => report(bend, &name, &meta, None, "bend deliver", d),
    }
}

/// A delivery's turn: refused before anything was signed (the quote), or submitted under its fixed
/// attempt name with its meta and the Host's decision (or the client's error).
enum Delivery {
    Refused(String),
    Submitted(String, Value, Result<Decided>),
}

/// One deliver turn for the awaiting `(record, await)` of OBJECT's birth TRANSACTION, paid from my account.
fn deliver_turn(bend: &Bend, object: &str, transaction: &str, (record, await_id): (String, String), account: Option<&str>) -> Result<Delivery> {
    let (payer, payer_cap) = bend.payer(account)?;
    let mut turn = json!({"kind": "deliver", "record": record, "await": await_id, "account": payer, "accountCapability": payer_cap});
    // The resumed segment runs over the stored checkpoint: when it needs more heap than the
    // escrowed envelope carries, the deliverer adds the difference (`heapUncovered`; priced,
    // paid by me). The Host's read-only quote is the kernel's own `ResumeTail.needed`.
    let quoted = activity::view(&bend.ws, &json!({"quotes": [{"record": &record, "await": &await_id}]}))?;
    let extra = match extra_heap(&quoted, &record, &await_id) { Ok(extra) => extra, Err(e) => return Ok(Delivery::Refused(e)) };
    if let Some(heap) = extra {
        turn["extra"] = extra_envelope(heap);
    }
    let name = deliver_name(&await_id);
    let meta = json!({"kind": "deliver", "object": object, "transaction": transaction, "await": await_id});
    let decided = bend.submit(&name, "deliver", &turn, &meta, false).map(|(d, _)| d);
    Ok(Delivery::Submitted(name, meta, decided))
}

/// The registry rows: (reference, bend, object, transaction), from `bend/objects/*.json` (an
/// admitted `bend run` writes one per object).
pub(crate) fn registry(root: &Path) -> Vec<(String, String, String, String)> {
    let mut rows: Vec<_> = fs::read_dir(root.join("bend").join("objects"))
        .into_iter()
        .flatten()
        .flatten()
        .take(256)
        .filter_map(|e| {
            let name = e.file_name().to_string_lossy().strip_suffix(".json")?.to_owned();
            let v: Value = serde_json::from_slice(&fs::read(e.path()).ok()?).ok()?;
            let s = |k: &str| v[k].as_str().map(str::to_owned);
            Some((name, s("bend").unwrap_or_default(), s("object")?, s("transaction")?))
        })
        .collect();
    rows.sort();
    rows
}

/// The await of a view that is past its deadline: `(record, await)` when the activity awaits and the
/// height the next turn is judged at is beyond the deadline, so a delivery settles it now (`timedOut`, or
/// the decider's answer if the slot was decided in time). `None` while it may still be answered, or when
/// nothing awaits.
fn overdue(view: &Value) -> Option<(String, String)> {
    let record = view.pointer("/births/0/record").and_then(Value::as_str)?;
    let phase = cell_of(view, record)?.pointer("/record/phase")?;
    if phase.get("kind").and_then(Value::as_str) != Some("awaiting") {
        return None;
    }
    let deadline: u128 = phase.pointer("/await/deadline")?.as_str()?.parse().ok()?;
    let height: u128 = view.get("height")?.as_str()?.parse().ok()?;
    (height > deadline).then(|| Some((record.to_owned(), phase.pointer("/await/id")?.as_str()?.to_owned()))).flatten()
}

fn row_bytes(row: &Value) -> Vec<u8> {
    let mut bytes = serde_json::to_vec_pretty(row).expect("JSON values serialise");
    bytes.push(b'\n');
    bytes
}

/// The view's height when the birth's activity is over (its record retired, or ended or faulted), so a
/// settle never reads it again; `None` while it awaits.
fn ended(view: &Value) -> Option<String> {
    let record = view.pointer("/births/0/record").and_then(Value::as_str)?;
    let kind = cell_of(view, record).and_then(|c| c.pointer("/record/phase/kind")).and_then(Value::as_str);
    (kind != Some("awaiting")).then(|| view.get("height").and_then(Value::as_str).unwrap_or("?").to_owned())
}

/// `bend settle [--account REF]`: deliver every activity this workspace ran (`bend/objects/`) whose await
/// is past its deadline, so a run reaches its end and its purse returns without anyone typing
/// `bend deliver`; one line per activity. The door's tick runs it for every enrolled member
/// (`mini-door-process`), so a tally nobody delivers still completes at its deadline.
fn settle_cmd(bend: &Bend, mut args: Args) -> Result<()> {
    let account = opt(&mut args, "account")?;
    args.finish()?;
    let mut settled = 0;
    let rows = bend.ws.root.join("bend").join("objects");
    for (name, _, object, _) in registry(&bend.ws.root) {
        if decimal_arg(&object, "OBJECT").is_err() {
            continue;
        }
        let file = rows.join(format!("{}.json", workspace::ref_file(&name)));
        let Ok(mut row) = fs::read(&file).map_err(|e| e.to_string()).and_then(|b| serde_json::from_slice::<Value>(&b).map_err(|e| e.to_string())) else { continue };
        let before = row.clone();
        // An activity seen ended is never read again: a settle costs one view per LIVE activity, not per run ever made.
        for transaction in live_births(&row) {
            if decimal_arg(&transaction, "TRANSACTION").is_err() {
                continue;
            }
            let view = match activity::view(&bend.ws, &json!({"objects": [&object], "births": [{"object": &object, "transaction": &transaction}]})) {
                Ok(view) => view,
                Err(e) => { eprintln!("{name}: not read: {e}"); continue; }
            };
            if let Some(height) = ended(&view) {
                mark_ended(&mut row, &transaction, &height);
                continue;
            }
            let Some(found) = overdue(&view) else { continue };
            match deliver_turn(bend, &object, &transaction, found, account.as_deref()) {
                Ok(Delivery::Submitted(_, _, Ok(Decided::Admitted { height, receipt, .. }))) => {
                    settled += 1;
                    println!("settled {name}: delivered past its deadline at height {height}, receipt {receipt}");
                }
                Ok(Delivery::Submitted(_, meta, Ok(Decided::Refused(r)))) => eprintln!("{name}: delivery refused: {r}{}", refusal_hint(&meta, &r)),
                Ok(Delivery::Submitted(_, _, Ok(Decided::Undecided(r)))) => eprintln!("{name}: delivery undecided: {r}; `bend settle` again retries it"),
                Ok(Delivery::Submitted(_, meta, Err(e))) => eprintln!("{name}: {}", repeated(&meta, e)),
                Ok(Delivery::Refused(e)) | Err(e) => eprintln!("{name}: {e}"),
            }
        }
        if row != before {
            let _ = crate::fsio::replace_private(&file, &row_bytes(&row));
        }
    }
    println!("bend settle: {settled} delivered");
    Ok(())
}

/// The births of an object's registry row a settle still reads: the newest (`transaction`, unless
/// `ended`) and every earlier run on the same object not yet seen ended (`earlier`).
fn live_births(row: &Value) -> Vec<String> {
    let mut out: Vec<String> = row.get("earlier").and_then(Value::as_array).into_iter().flatten()
        .filter_map(|e| e.as_str().map(str::to_owned)).collect();
    if row.get("ended").is_none() {
        if let Some(t) = row.get("transaction").and_then(Value::as_str) {
            out.push(t.to_owned());
        }
    }
    out
}

fn mark_ended(row: &mut Value, transaction: &str, height: &str) {
    if row.get("transaction").and_then(Value::as_str) == Some(transaction) {
        row["ended"] = json!(height);
    } else if let Some(earlier) = row.get_mut("earlier").and_then(Value::as_array_mut) {
        earlier.retain(|e| e.as_str() != Some(transaction));
    }
}

/// An object's registry row after a new birth on it: the newest birth names the row, and an earlier one
/// not seen ended stays in `earlier`, so `bend settle` still ends it at its deadline.
fn next_row(old: Option<&Value>, row: Value) -> Value {
    let mut row = row;
    let Some(old) = old else { return row };
    let mut earlier: Vec<Value> = old.get("earlier").and_then(Value::as_array).cloned().unwrap_or_default();
    let (was, now) = (old.get("transaction"), row.get("transaction"));
    if was.is_some() && was != now && old.get("ended").is_none() {
        earlier.extend(was.cloned());
    }
    earlier.retain(|e| Some(e) != now);
    if !earlier.is_empty() {
        row["earlier"] = json!(earlier);
    }
    row
}

/// The record cell and the await id of an activity that is awaiting, from its public view.
fn deliverable(view: &Value) -> Result<(String, String)> {
    let record = view.pointer("/births/0/record").and_then(Value::as_str).ok_or("bend: the view names no activity record")?;
    let phase = cell_of(view, record).and_then(|c| c.pointer("/record/phase")).ok_or("bend: the activity record is absent")?;
    if phase.get("kind").and_then(Value::as_str) != Some("awaiting") {
        return Err(format!("refused: the activity is not awaiting (phase {}): nothing to deliver",
            phase.get("kind").and_then(Value::as_str).unwrap_or("none")));
    }
    let await_id = phase.pointer("/await/id").and_then(Value::as_str).ok_or("bend: the await names no id")?;
    Ok((record.to_owned(), await_id.to_owned()))
}

/// The heap a delivery must add to its escrowed envelope, from the view's quote of `(record, await)`:
/// `needed - escrow`, or none when the escrow already covers the resumed segment.
fn extra_heap(view: &Value, record: &str, await_id: &str) -> Result<Option<u128>> {
    let quote = view.get("quotes").and_then(Value::as_array).into_iter().flatten()
        .find(|q| q["record"] == record && q["await"] == await_id)
        .ok_or("bend: the Host quoted no heap for this await")?;
    if let Some(reason) = quote.get("refused") {
        return Err(format!("refused: the pending await cannot be delivered: {reason}"));
    }
    let number = |k: &str| quote[k].as_str().and_then(|v| v.parse::<u128>().ok())
        .ok_or_else(|| format!("bend: the heap quote's {k} is not a decimal"));
    let (needed, escrow) = (number("needed")?, number("escrow")?);
    Ok((needed > escrow).then(|| needed - escrow))
}

/// An added envelope carrying only heap: every other member zero.
fn extra_envelope(heap: u128) -> Value {
    let mut c = serde_json::Map::new();
    for k in ENVELOPE_KEYS { c.insert(k.into(), json!("0")); }
    c.insert("heap".into(), json!(heap.to_string()));
    Value::Object(c)
}

fn deliver_name(await_id: &str) -> String {
    use sha2::{Digest, Sha256};
    format!("deliver-{}", &format!("{:x}", Sha256::digest(await_id.as_bytes()))[..16])
}

/// The attempt name of the answer to SLOT: fixed, so `bend lookup`/`bend retry` find it again.
fn answer_name(slot: &str) -> String {
    use sha2::{Digest, Sha256};
    format!("answer-{}", &format!("{:x}", Sha256::digest(slot.as_bytes()))[..16])
}

/// `bend answer SLOT @FILE`: one resolve turn deciding SLOT, signed by this workspace's key. The
/// kernel admits only the slot's decider (notDecider) and only once (a decided slot refuses).
fn answer_cmd(bend: &Bend, mut args: Args) -> Result<()> {
    let slot = text(&mut args, "slot")?;
    let file = path(args.required("answer")?);
    args.finish()?;
    decimal_arg(&slot, "SLOT")?;
    let bytes = fs::read(&file).map_err(|e| format!("bend: {}: {e}", file.display()))?;
    if bytes.len() > 4096 { return Err("bend: an answer is at most 4096 bytes".into()); }
    let answer: Value = serde_json::from_slice(&bytes).map_err(|e| format!("bend: the answer is not JSON: {e}"))?;
    let shaped = answer.as_object().is_some_and(|o| o.len() == 1
        && (o.contains_key("reply") || o.get("refused").is_some_and(Value::is_string)));
    if !shaped { return Err("bend: the answer is {\"reply\": DATA} or {\"refused\": REASON}".into()); }
    let name = answer_name(&slot);
    let turn = json!({"kind": "resolve", "slot": &slot, "answer": &answer});
    let meta = json!({"kind": "resolve", "slot": &slot});
    match bend.submit(&name, "resolve", &turn, &meta, false) {
        Err(e) => ending_for(&name, repeated(&meta, e)),
        Ok((d, _)) => report(bend, &name, &meta, None, "bend answer", d),
    }
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(&mut args, "action")?;
    let bend = Bend::open(path(args.required("dir")?))?;
    match action.as_str() {
        "publish" => publish(&bend, args),
        "run" => run_bend(&bend, args),
        "show" => show(&bend, args),
        "await" => await_cmd(&bend, args),
        "answer" => answer_cmd(&bend, args),
        "deliver" => deliver_cmd(&bend, args),
        "settle" => settle_cmd(&bend, args),
        "lookup" => lookup_cmd(&bend, args, false),
        "retry" => lookup_cmd(&bend, args, true),
        _ => Err("bend --action must be publish, run, show, await, answer, deliver, settle, lookup or retry".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deliver_adds_exactly_the_heap_the_quote_lacks() {
        let quote = |needed: &str, escrow: &str| json!({"quotes": [{"record": "41", "await": "55", "needed": needed, "escrow": escrow}]});
        assert_eq!(extra_heap(&quote("200018", "200000"), "41", "55").unwrap(), Some(18));
        assert_eq!(extra_heap(&quote("200000", "200000"), "41", "55").unwrap(), None);
        assert_eq!(extra_heap(&quote("10", "200000"), "41", "55").unwrap(), None);
        assert!(extra_heap(&quote("1", "1"), "41", "56").is_err(), "a quote for another await is not this one's");
        let refused = json!({"quotes": [{"record": "41", "await": "55", "refused": "awaitMismatch"}]});
        assert!(extra_heap(&refused, "41", "55").unwrap_err().starts_with("refused:"));
        let e = extra_envelope(18);
        assert_eq!(e.as_object().unwrap().len(), ENVELOPE_KEYS.len());
        assert_eq!((e["heap"].as_str(), e["stack"].as_str()), (Some("18"), Some("0")));
    }

    #[test]
    fn an_earlier_run_on_the_same_object_is_still_settled() {
        let first = json!({"bend": "tally", "object": "7", "transaction": "100"});
        let second = next_row(Some(&first), json!({"bend": "tally", "object": "7", "transaction": "200"}));
        assert_eq!(live_births(&second), ["100", "200"], "the first run is still read");
        let mut third = next_row(Some(&second), json!({"bend": "tally", "object": "7", "transaction": "300"}));
        assert_eq!(live_births(&third), ["100", "200", "300"]);
        assert_eq!(next_row(Some(&third), json!({"transaction": "300"}))["earlier"], json!(["100", "200"]), "a lookup of the same birth adds nothing");
        mark_ended(&mut third, "100", "40");
        mark_ended(&mut third, "300", "41");
        assert_eq!(live_births(&third), ["200"]);
        let mut ended_first = first.clone();
        mark_ended(&mut ended_first, "100", "9");
        assert!(next_row(Some(&ended_first), json!({"transaction": "200"})).get("earlier").is_none(), "an ended run is not carried");
    }

    #[test]
    fn only_an_await_past_its_deadline_is_settled() {
        let view = |kind: &str, height: &str| json!({"height": height, "births":[{"object":"7","transaction":"9","record":"41"}],
            "cells":[{"cell":"41","record":{"phase":{"kind":kind,"await":{"id":"55","deadline":"90","yieldedAt":"86",
                "source":{"kind":"reply","slot":"66","decider":"8"}}}}}]});
        assert_eq!(overdue(&view("awaiting", "91")), Some(("41".to_owned(), "55".to_owned())), "the next turn is judged past the deadline");
        assert_eq!(overdue(&view("awaiting", "90")), None, "at the deadline the decider may still answer");
        assert_eq!(overdue(&view("awaiting", "87")), None);
        assert_eq!(overdue(&view("done", "200")), None, "an ended activity is not delivered again");
        assert_eq!(overdue(&json!({"height":"5","births":[{"record":"41"}],"cells":[]})), None, "a retired record: nothing awaits");
        assert_eq!(ended(&view("awaiting", "91")), None);
        assert_eq!(ended(&view("done", "200")).as_deref(), Some("200"));
        assert_eq!(ended(&json!({"height":"5","births":[{"record":"41"}],"cells":[]})).as_deref(), Some("5"), "a retired record is over");
    }

    #[test]
    fn deliver_names_the_awaiting_record_and_its_await() {
        let view = |kind: &str| json!({"births":[{"object":"7","transaction":"9","record":"41"}],
            "cells":[{"cell":"41","record":{"phase":{"kind":kind,"await":{"id":"55","deadline":"90","yieldedAt":"20",
                "source":{"kind":"reply","slot":"66","decider":"8"}}}}}]});
        assert_eq!(deliverable(&view("awaiting")).unwrap(), ("41".to_owned(), "55".to_owned()));
        assert!(deliverable(&view("done")).unwrap_err().starts_with("refused: the activity is not awaiting"));
        assert!(deliverable(&json!({"births":[]})).is_err());
        assert_eq!(deliver_name("55"), deliver_name("55"));
        assert_ne!(deliver_name("55"), deliver_name("56"));
    }

    #[test]
    fn a_lookup_answers_from_the_attempts_retained_decision() {
        let dir = std::env::temp_dir().join(format!("bend-retained-{}-{}", std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir_all(&dir).unwrap();
        assert!(retained_decision(&dir).is_none(), "nothing retained: ask the Host");
        let refused = json!({"type":"refused","refusal":"operation-rejected: pastDeadline"});
        fs::write(dir.join("outcome.json"), refused.to_string()).unwrap();
        assert_eq!(retained_decision(&dir), Some(refused.clone()));
        assert!(matches!(decided(&refused, 10), Decided::Refused(_)));
        // An undecided answer is not a decision: the Host is asked.
        fs::write(dir.join("outcome.json"), json!({"type":"undecided"}).to_string()).unwrap();
        assert!(retained_decision(&dir).is_none());
        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn the_package_input_is_the_front_ends_spec() {
        let spec = package_input("Tally", Path::new("/ws/bend/tally/source/Tally.obend"), "tally");
        assert_eq!(spec, json!({"schema": "dregg.objective-bend.package-input.v1", "edition": "objective-bend-1",
            "modules": [{"name": "Tally", "sourcePath": "/ws/bend/tally/source/Tally.obend", "imports": []}],
            "entryModule": "0", "entryDefinition": "tally"}));
    }

    #[test]
    fn a_full_envelope_declares_the_quote_the_budget_and_the_policy_figures() {
        let e = envelope(3_200_000, 1500, 900, 3000);
        assert_eq!(e.as_object().unwrap().len(), ENVELOPE_KEYS.len());
        assert_eq!((e["sourceTicks"].as_str(), e["extractTicks"].as_str(), e["replayBytes"].as_str(), e["coreBytes"].as_str()),
            (Some("3000"), Some("3200000"), Some("1500"), Some("900")));
        assert_eq!((e["heap"].as_str(), e["typeFuel"].as_str(), e["feeDebit"].as_str()), (Some("200000"), Some("16384"), Some("0")));
        assert_eq!(price(3000, 1500, 900), 1 + 3000 + 6 * 1500 + 2 * 900);
    }

    #[test]
    fn the_turn_bodies_are_the_hosts_turns() {
        let env = envelope(1, 2, 3, 3000);
        let birth = birth_turn("90", "91", "130", "1030", "777", &default_input("40", false), &env, 1234);
        assert_eq!((birth["kind"].as_str(), birth["deposit"].as_str(), birth["pin"].as_str()), (Some("birth"), Some("1234"), Some("777")));
        assert_eq!(birth["resume"], birth["envelope"]);
        assert_eq!(birth["timeout"], birth["envelope"]);
        assert_eq!(birth["input"]["fields"][1], json!({"name": "decider", "value": {"tag": "natural", "value": "40"}}));
        let state: Value = serde_json::from_str(TOTAL_STATE).unwrap();
        let create = create_turn("90", "91", "777", &state, None, "130", "1030");
        assert!(create.get("seed").is_none());
        assert_eq!(create["upgrade"], json!({"frozen": {}}));
        let seeded = create_turn("90", "91", "777", &state, Some(&json!({"tag": "natural", "value": "5"})), "130", "1030");
        assert_eq!(seeded["seed"]["value"], "5");
        let publish = publish_turn("aa", "bb", "130", "1030");
        assert_eq!(publish, json!({"kind": "publish", "artifact": "aa", "package": "bb", "payer": "130", "payerCapability": "1030"}));
    }

    #[test]
    fn data_reads_as_the_member_writes_it() {
        let state = json!({"tag": "record", "fields": [{"name": "total", "value": {"tag": "natural", "value": "3"}}]});
        assert_eq!(data_text(&state), "{total=3}");
        assert_eq!(data_text(&default_input("40", false)), "{init=set(0), decider=40}");
        assert_eq!(data_text(&default_input("40", true)), "{init=keep({}), decider=40}", "a later run joins the object's total");
    }

    #[test]
    fn an_exact_repeat_is_named_for_what_happened() {
        let conflict = "conflict: transaction identity conflict (phase replay)";
        let h = refusal_hint(&json!({"kind": "resolve", "slot": "5551"}), conflict);
        assert!(h.contains("slot 5551 is already answered") && h.contains("`bend deliver`"), "{h}");
        let h = refusal_hint(&json!({"kind": "deliver", "await": "55"}), conflict);
        assert!(h.contains("await 55 is already delivered"), "{h}");
        let h = refusal_hint(&json!({"kind": "publish", "artifactId": "1", "packageId": "2"}), conflict);
        assert!(h.contains("already published: artifact 1 package 2"), "{h}");
        assert!(refusal_hint(&json!({"kind": "resolve", "slot": "5551"}), "notDecider").is_empty(), "other refusals keep the Host's words alone");
        assert!(refusal_hint(&json!({"kind": "run"}), conflict).is_empty());
        let guard = "activity: this turn was already submitted (confirmed; /ws/bend/answer-1/attempts/resolve-2); a second one is your decision: --again true";
        let r = repeated(&json!({"kind": "resolve", "slot": "5551"}), guard.into());
        assert!(r.starts_with("refused: slot 5551 is already answered") && !r.contains("--again"), "{r}");
        let guard_run = "activity: this turn was already submitted (confirmed; /ws/bend/tally/attempts/birth-1); a second one is your decision: --again true";
        let r = run_again("tally", "t1", guard_run.into());
        assert!(r.starts_with("refused: run tally on t1: this exact run was already admitted") && r.ends_with("`bend run tally t1 --again`"), "{r}");
        assert!(!r.contains("--again true"), "the line named is a bend verb: {r}");
        let line = format!("bend run tally t1 --again");
        let s = crate::shell::words(&line).unwrap();
        assert!(crate::shell_grammar::parse(&crate::shell_grammar::BEND, &s).is_ok(), "the suggested line parses");
        assert_eq!(run_again("tally", "t1", "bend: x".into()), "bend: x");
        let refused_before = "activity: this turn was already submitted (refused; /x); a second one is your decision: --again true";
        assert_eq!(repeated(&json!({"kind": "resolve", "slot": "1"}), refused_before.into()), refused_before, "a refused answer is not an answer");
    }

    #[test]
    fn the_hosts_outcomes_are_decided_by_name() {
        let ok = json!({"type": "confirmed", "confirmation": "installed", "transactionId": "7", "eventId": "9", "acceptedCount": "12", "worldRoot": "55"});
        // the 12th accepted turn of a world born at height 10 was judged at height 21 (the view then reads 22)
        assert_eq!(decided(&ok, 10), Decided::Admitted { height: "21".into(), root: "55".into(), receipt: "tx 7 event 9".into(), how: "installed".into() });
        assert_eq!(judged_height(0, "1"), "0");
        assert_eq!(judged_height(10, "0"), "?", "no turn is the 0th");
        assert_eq!(judged_height(10, "x"), "?");
        let no = json!({"type": "refused", "reason": "notObjectHolder", "phase": "", "detail": ""});
        assert!(matches!(decided(&no, 10), Decided::Refused(m) if m.starts_with("notObjectHolder")));
        assert!(matches!(decided(&json!({"type": "uncertain"}), 10), Decided::Undecided(_)));
    }

    #[test]
    fn a_hosts_ending_is_not_a_client_error() {
        let _ = take_command_ending();
        assert!(ending("refused: op210: notAccountOwner".into()).is_ok());
        assert_eq!(take_command_ending().unwrap().render().0, 3);
        assert!(ending("bend: no workspace".into()).is_err());
        assert!(ending_for("tally", "bend: no workspace".into()).is_err());
    }

    #[test]
    fn an_undecided_turn_names_the_two_shell_lines_that_recover_it() {
        for error in ["uncertain host response: reply deliberately not read", "undecided: this turn's exact ingress is retained at /x/attempts/a and may have been admitted; `mini activity --action lookup`"] {
            let _ = take_command_ending();
            assert!(ending_for("tally", error.into()).is_ok());
            let (code, text) = take_command_ending().unwrap().render();
            assert_eq!(code, 4, "{text}");
            assert!(text.contains("`bend lookup tally`") && text.contains("`bend retry tally`"), "{text}");
            assert!(!text.contains("mini activity"), "{text}");
        }
    }

    #[test]
    fn an_await_reads_the_reply_slot_decider_and_deadline() {
        let view = json!({"height":"40","births":[{"record":"77"}],"objects":[{"stateCell":"78"}],"cells":[
            {"cell":"77","record":{"phase":{"kind":"awaiting","await":{"id":"1","deadline":"90","source":{"kind":"reply","slot":"5551","slotCell":"9","decider":"42"}}}}},
            {"cell":"78","value":{"tag":"record","fields":[{"name":"total","value":{"tag":"natural","value":"3"}}]}}]});
        let a = await_of_view(&view, "12", "34");
        assert_eq!((a["phase"].as_str(), a["slot"].as_str(), a["decider"].as_str(), a["deadline"].as_str()),
            (Some("awaiting"), Some("5551"), Some("42"), Some("90")));
        let none = await_of_view(&json!({"births":[{"record":"77"}],"cells":[]}), "12", "34");
        assert_eq!(none["phase"], "none");
        assert!(none.get("slot").is_none());
        assert_eq!(answer_name("5551"), answer_name("5551"));
        assert!(answer_name("5551").len() <= 64 && name_ok(&answer_name("5551")).is_ok());
    }

    #[test]
    fn an_absent_object_is_refused_by_name_with_the_verb_that_makes_it() {
        let text = no_object_refusal("fresh");
        assert!(text.starts_with("refused: no object named fresh: make one with `create fresh content open`"), "{text}");
        let _ = take_command_ending();
        assert!(ending(text).is_ok());
        assert_eq!(take_command_ending().unwrap().render().0, 3);
    }

    #[test]
    fn only_a_reference_this_workspace_holds_is_an_object() {
        let root = std::env::temp_dir().join(format!("mini-bend-absent-{}", std::process::id()));
        fs::create_dir_all(root.join("refs")).unwrap();
        assert!(absent_object(&root, "fresh").is_some());
        fs::write(root.join("refs").join(format!("{}.json", workspace::ref_file("fresh"))), b"{}").unwrap();
        assert!(absent_object(&root, "fresh").is_none());
        assert!(absent_object(&root, "room/shared").is_none(), "a shared name resolves through its room");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn an_unfunded_run_says_what_it_costs_and_what_the_account_holds() {
        let text = unfunded_refusal("tally", "lobby-tally", 874, 2162240);
        assert!(text.starts_with("refused: unfunded: run tally on lobby-tally costs 2162240") && text.contains("holds 874"), "{text}");
        assert_eq!(price(3000, 1500, 900), 1 + 3000 + 6 * 1500 + 2 * 900);
    }

    #[test]
    fn bend_names_are_reference_safe() {
        assert!(name_ok("tally-2").is_ok());
        assert!(name_ok("").is_err() && name_ok("a/b").is_err() && name_ok("a b").is_err());
    }

    /// The mirrored policy figures are `activity_world.py`'s, the world every genesis pins.
    #[test]
    fn policy_mirror_matches_the_world() {
        let world = include_str!("../activity_world.py");
        for (k, v) in FIXED {
            assert!(world.contains(&format!("'{k}': {v}")), "{k}: {v} is not in activity_world.MAXIMUM");
        }
        assert!(world.contains(&format!("'replayBytes': '{REPLAY_RATE}'")) && world.contains(&format!("'coreBytes': '{CORE_RATE}'")));
        assert!(world.contains(&format!("'base': '{BASE}', 'typeFuel': '0', 'sourceTicks': '{TICK_RATE}'")));
        assert!(world.contains(&format!("BEND_TICKS = {TICKS}")) && world.contains(&format!("BEND_PURSE_PRICES = {DEPOSIT_PRICES}")));
        assert!(world.contains(&format!("BEND_ANSWERS = {ANSWERS}")));
        for k in ENVELOPE_KEYS {
            assert!(world.contains(&format!("'{k}':")), "{k} is not an envelope member of activity_world.MAXIMUM");
        }
    }
}
