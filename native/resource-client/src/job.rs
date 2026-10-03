//! `mini job` — a Nock job between two friends, adjudicated by one `ran` turn
//! (COMPUTE, the J-JOB floor).
//!
//! A job is one declared cell born in a room under the job law
//! (`deploy/shell/templates/job/law.job`, `Kernel/Job.lean`), bound here at
//! CALLER = this workspace's subject, PROGRAM, WINDOW. Its money is the Book's,
//! moved by the job-money receiver (ops 160-163, `Kernel/JobMoneyReceiver.lean`):
//!
//! * `post`   — the caller births the job in ROOM, writes the order (unfunded:
//!   escrow, bond, provider 0) and funds the escrow from its account (money turn).
//! * `claim`  — a room member takes the job and bonds at least the price (money turn).
//! * `answer` — the provider posts an output (by default the one its node computes:
//!   op 134, the kernel's own dry run on the job's sample), with `finalAt = now + WINDOW`.
//! * `check`  — anyone in the window runs the truth turn: a write of the truth field
//!   carrying the run claim, which the kernel re-executes and compares byte for byte
//!   (`checkRun_sound`); then the decide turn (match: upheld 3, mismatch: slashed 4).
//!   Past `answerBy` with no answer it decides the stall (slashed); past `finalAt`
//!   with no truth it decides the timeout (upheld).
//! * `settle` — the close money turn: the provider is paid price + bond (upheld),
//!   the bond is split per the tariff (slashed), or the escrow returns (void). The
//!   ingress is retained; settling again resubmits the same bytes and the Host
//!   answers the original receipt.
//! * `show` / `list` — the job's fields by name; the jobs this workspace knows in a room.
//!
//! Every write is an ordinary workspace proposal; every refusal is the Host's,
//! by name (the law's clause, or the money decision's reason).
use crate::agent_reserve::{field, private_bytes};
use crate::*;
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::time::Instant;

/// The job law's JSON (`scripts/gen-joblaw.py` keeps it equal to `Kernel/Job.lean` §2).
const LAW: &str = include_str!("../../../deploy/shell/templates/job/law.job.json");
/// The same law, one clause per line, as the Host renders a refused clause.
const LAW_SHELL: &str = include_str!("../../../deploy/shell/templates/job/law.job.shell");

const STATES: [&str; 7] = ["open", "claimed", "answered", "upheld", "slashed", "void", "closed"];
const NAMES: [&str; 16] = [
    "state", "program", "input", "caller", "callerAcct", "price", "claimBy", "answerBy", "escrow",
    "provider", "providerAcct", "bond", "output", "steps", "finalAt", "truth",
];
const STATE: u32 = 0;
const OUTPUT: u32 = 12;
const STEPS: u32 = 13;
const FINAL_AT: u32 = 14;
const TRUTH: u32 = 15;
const FUND: u8 = 1;
const CLAIM: u8 = 2;
const SETTLE: u8 = 3;
/// The challenge window when `post` is not given one (clock seconds).
const DEFAULT_WINDOW: i128 = 60;

struct Ws {
    root: PathBuf,
    pin: Value,
    host: PathBuf,
    socket: PathBuf,
    config: PathBuf,
    key: PathBuf,
    subject: String,
}

fn ws(root: PathBuf) -> Result<Ws> {
    let bytes = fs::read(root.join("workspace.json"))
        .map_err(|error| format!("job: cannot read workspace.json: {error}"))?;
    let pin: Value = serde_json::from_slice(&bytes).map_err(|error| format!("job: invalid workspace.json: {error}"))?;
    Ok(Ws {
        host: PathBuf::from(field(&pin, "host")?),
        socket: PathBuf::from(field(&pin, "socket")?),
        config: PathBuf::from(field(&pin, "config")?),
        key: PathBuf::from(field(&pin, "key")?),
        subject: field(&pin, "subject")?.to_string(),
        root,
        pin,
    })
}

fn invoke(ws: &Ws, operation: u8, payload: &[u8]) -> Result<Vec<u8>> {
    let frame = session_invoke(&ws.host, &ws.socket, &ws.config, operation, payload)?;
    match frame.split_first() {
        Some((actual, body)) if *actual == operation && !body.is_empty() => Ok(body.to_vec()),
        Some((255 | 254, body)) => Err(format!(
            "refused: op{operation}: {}",
            String::from_utf8_lossy(&body[body.len().saturating_sub(400)..]).split_whitespace().collect::<Vec<_>>().join(" ")
        )),
        _ => Err(format!("job: op{operation} returned an invalid frame")),
    }
}

fn with_kind(kind: &str, body: &[u8]) -> Vec<u8> {
    let mut payload = (kind.len() as u16).to_le_bytes().to_vec();
    payload.extend_from_slice(kind.as_bytes());
    payload.extend_from_slice(body);
    payload
}

fn author(ws: &Ws, kind: &str, value: &Value) -> Result<Vec<u8>> {
    invoke(ws, 7, &with_kind(kind, value.to_string().as_bytes()))
}

fn inspect(ws: &Ws, kind: &str, bytes: &[u8]) -> Result<Value> {
    serde_json::from_slice(&invoke(ws, 8, &with_kind(kind, bytes))?)
        .map_err(|error| format!("job: invalid Host inspection of {kind}: {error}"))
}

fn pair(first: &[u8], second: &[u8]) -> Vec<u8> {
    let mut bytes = (first.len() as u32).to_le_bytes().to_vec();
    bytes.extend_from_slice(first);
    bytes.extend_from_slice(second);
    bytes
}

fn unhex(text: &str) -> Result<Vec<u8>> { crate::decode_hex(text).map_err(|e| format!("job: {e}")) }

fn nonce() -> Result<String> {
    let mut bytes = [0u8; 16];
    File::open("/dev/urandom")
        .and_then(|mut file| file.read_exact(&mut bytes))
        .map_err(|error| format!("job: cannot obtain a nonce: {error}"))?;
    Ok(u128::from_be_bytes(bytes).to_string())
}

fn int(value: &Value, what: &str) -> Result<i128> {
    value
        .as_str()
        .and_then(|text| text.parse::<i128>().ok())
        .ok_or_else(|| format!("job: {what} is not a decimal"))
}

fn decimal(text: &str, what: &str) -> Result<String> {
    if text.is_empty()
        || text.len() > 80
        || !text.bytes().all(|b| b.is_ascii_digit())
        || (text.len() > 1 && text.starts_with('0'))
    {
        return Err(format!("job: {what} must be a canonical decimal"));
    }
    Ok(text.to_owned())
}

fn arg(args: &mut Args, name: &str) -> Result<String> {
    let value = args.required(name)?
        .into_string()
        .map_err(|_| format!("--{name} must be UTF-8"))?;
    if name == "name" { name_ok(&value)?; }
    Ok(value)
}

fn opt(args: &mut Args, name: &str) -> Result<Option<String>> {
    args.optional(name)
        .map(|value| value.into_string().map_err(|_| format!("--{name} must be UTF-8")))
        .transpose()
}

fn name_ok(name: &str) -> Result<()> {
    if name.is_empty()
        || name.len() > 64
        || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
    {
        return Err(format!("job: `{name}` is not a reference name"));
    }
    Ok(())
}

/// The deployment clock (op 129).
fn now(ws: &Ws) -> Result<i128> {
    let view = inspect(ws, "clock-view", &invoke(ws, 129, &[])?)?;
    int(view.get("now").ok_or("job: clock view lacks now")?, "clock now")
}

/// One client-contract call, in process (the shell's own path).
fn client(command: &str, flags: &[(&str, OsString)]) -> Result<()> {
    let args = Args {
        command: OsString::from(command),
        values: flags.iter().map(|(name, value)| (OsString::from(format!("--{name}")), value.clone())).collect(),
    };
    let _ = take_host_decision();
    let result = crate::run(args);
    let _ = io::stdout().flush();
    // A Host refusal is reported as the Host decoded it (the law's clause, by name).
    result.map_err(|error| {
        let decided = match take_host_decision() {
            Some(HostDecision::RefusedFrame { decoded: Some(outcome), .. }) | Some(HostDecision::Outcome(outcome)) => {
                refusal_line(&outcome)
            }
            _ => None,
        };
        decided.unwrap_or(error)
    })
}

fn jobs_dir(ws: &Ws) -> Result<PathBuf> {
    let dir = ws.root.join("jobs");
    fs::create_dir(&dir).or_else(|e| if e.kind() == std::io::ErrorKind::AlreadyExists { Ok(()) } else { Err(e) }).map_err(|e| e.to_string())?;
    if !fs::symlink_metadata(&dir).map_err(|e| e.to_string())?.is_dir() { return Err("job directory must be a real directory".into()); }
    fs::create_dir(dir.join("req")).or_else(|e| if e.kind() == std::io::ErrorKind::AlreadyExists { Ok(()) } else { Err(e) }).map_err(|e| e.to_string())?;
    if !fs::symlink_metadata(dir.join("req")).map_err(|e| e.to_string())?.is_dir() { return Err("job request directory must be a real directory".into()); }
    Ok(dir)
}

fn record_path(ws: &Ws, name: &str) -> Result<PathBuf> {
    name_ok(name)?;
    Ok(jobs_dir(ws)?.join(format!("{name}.json")))
}

/// The job's local record; a job this workspace holds only a reference to
/// (created or imported outside `post`/`claim`) is known by that reference.
fn record(ws: &Ws, name: &str) -> Result<Value> {
    let path = record_path(ws, name)?;
    match fs::symlink_metadata(&path) {
        Ok(_) => {
            let bytes = crate::shell::session_fs::read(&ws.root, &path, 1 << 20)?;
            serde_json::from_slice(&bytes).map_err(|error| format!("job: {}: {error}", path.display()))
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            let reference = workspace::reference(&ws.root, name)
                .map_err(|_| format!("job: no job {name} in this workspace (post, or claim it)"))?;
            Ok(json!({"type":"minidregg-job-v1","name":name,"job":field(&reference, "target")?}))
        }
        Err(error) => Err(error.to_string()),
    }
}

/// WINDOW: the record's, else the job law's own (clause 34's offset).
fn window_of(ws: &Ws, name: &str, rec: &Value) -> Result<i128> {
    if let Some(window) = rec.get("window").and_then(Value::as_str) {
        return int(&json!(window), "window");
    }
    let reference = workspace::reference(&ws.root, name)?;
    let policy = workspace::signed_view(&ws.root, &ws.pin, &reference, "policy")?.0;
    find_window(&policy)
        .ok_or_else(|| "job: the job law names no window".to_string())
        .and_then(|w| int(&json!(w), "window"))
}

fn save(ws: &Ws, name: &str, value: &Value) -> Result<()> {
    let path = record_path(ws, name)?;
    crate::shell::session_fs::replace(&ws.root, &path, &serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?)
}

/// The job cell's fields, by a signed read under this workspace's reference.
fn fields(ws: &Ws, name: &str) -> Result<BTreeMap<u32, String>> {
    let reference = workspace::reference(&ws.root, name)?;
    let (view, _, _) = workspace::signed_view(&ws.root, &ws.pin, &reference, "resource")?;
    let entries = view
        .pointer("/cell/entries")
        .or_else(|| view.pointer("/page/entries"))
        .and_then(Value::as_array)
        .ok_or("job: the resource view has no entries")?;
    let mut out = BTreeMap::new();
    for entry in entries {
        if let (Some(f), Some(v)) = (
            entry.pointer("/key/field").and_then(Value::as_str),
            entry.get("value").and_then(Value::as_str),
        ) {
            if let Ok(f) = f.parse::<u32>() {
                out.insert(f, v.to_owned());
            }
        }
    }
    Ok(out)
}

fn get(fields: &BTreeMap<u32, String>, f: u32) -> Result<i128> {
    fields
        .get(&f)
        .and_then(|v| v.parse::<i128>().ok())
        .ok_or_else(|| format!("job: field {} ({}) is absent", f, NAMES[f as usize]))
}

fn named(fields: &BTreeMap<u32, String>) -> Value {
    let mut out = serde_json::Map::new();
    for (f, v) in fields {
        let key = NAMES.get(*f as usize).map(|s| s.to_string()).unwrap_or(format!("field{f}"));
        out.insert(key, json!(v));
    }
    if let Some(state) = fields.get(&STATE).and_then(|s| s.parse::<usize>().ok()).and_then(|s| STATES.get(s)) {
        out.insert("stateName".into(), json!(state));
    }
    Value::Object(out)
}

/// The clause a law refusal names, as `law.job.shell` spells it (the Host's rendering).
fn clause_text(index: usize) -> Option<String> {
    LAW_SHELL.lines().filter(|l| !l.starts_with("--")).nth(index).map(|l| l.trim_end_matches(';').to_owned())
}

/// Propose and submit one scalar invoke on `name`; the outcome the Host retained.
fn write(ws: &Ws, id: &str, name: &str, actions: Vec<Value>, run_claim: Option<Value>) -> Result<Value> {
    let mut request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"scalar","actions":actions}}]});
    if let Some(claim) = run_claim {
        request["run"] = claim;
    }
    let path = jobs_dir(ws)?.join("req").join(format!("{id}.json"));
    crate::shell::session_fs::replace(&ws.root, &path, request.to_string().as_bytes())?;
    client(
        "workspace",
        &[("action", "propose".into()), ("dir", ws.root.clone().into()), ("request", path.into()), ("proposal-id", id.into())],
    )?;
    let attempt = ws.root.join("attempts").join(id);
    let submitted = client(
        "workspace",
        &[
            ("action", "submit".into()),
            ("dir", ws.root.clone().into()),
            ("intent", ws.root.join("proposals").join(id).join("intent.json").into()),
            ("attempt", attempt.clone().into()),
        ],
    );
    let outcome = fs::read(attempt.join("outcome.json"))
        .ok()
        .and_then(|bytes| serde_json::from_slice::<Value>(&bytes).ok());
    match (submitted, outcome) {
        (Ok(()), Some(outcome)) if outcome.get("type").and_then(Value::as_str) == Some("confirmed") => Ok(outcome),
        (_, Some(outcome)) => Err(refusal_line(&outcome).unwrap_or_else(|| format!("job: {id}: {outcome}"))),
        (Err(error), None) => Err(error),
        (Ok(()), None) => Err(format!("job: {id}: no outcome retained")),
    }
}

fn create(field: u32, value: impl ToString) -> Value {
    json!({"type":"create","key":{"type":"object","field":field.to_string()},"value":value.to_string()})
}

fn update(field: u32, expected: impl ToString, value: impl ToString) -> Value {
    json!({"type":"write","key":{"type":"object","field":field.to_string()},
        "expected":expected.to_string(),"value":value.to_string()})
}

/// One job-money turn (op 160 plan, sign, 161 assembly, 162 submit). The plan
/// names a refusal (`jobRefused [k]` is the law's clause k); the submission is
/// blind. Everything is retained under `dir`.
#[allow(clippy::too_many_arguments)]
fn money(
    ws: &Ws,
    dir: &Path,
    job: &str,
    action: u8,
    account: &str,
    amount: &str,
    capability: &str,
    job_capability: &str,
) -> Result<Value> {
    fs::create_dir_all(dir).map_err(|error| format!("job: {}: {error}", dir.display()))?;
    let view = inspect(ws, "pay-view", &invoke(ws, 107, &[])?)?;
    let authority = view.get("authorityRoot").and_then(Value::as_str).ok_or("job: pay view lacks authorityRoot")?;
    let command = json!({"subject":ws.subject,"capability":capability,"jobCapability":job_capability,
        "job":job,"action":action.to_string(),
        "account":account,"amount":amount,"nonce":nonce()?,"expectedAuthorityRoot":authority});
    crate::shell::session_fs::replace(&ws.root, &dir.join("command.json"), command.to_string().as_bytes())?;
    let command_bytes = author(ws, "job-money", &command)?;
    let plan = match invoke(ws, 160, &command_bytes) {
        Ok(plan) => plan,
        Err(refused) => {
            let named = refused
                .find("jobRefused [")
                .and_then(|at| refused[at + 12..].split(']').next())
                .and_then(|k| k.trim().parse::<usize>().ok())
                .and_then(clause_text)
                .map(|clause| format!(" (the job law: {clause})"))
                .unwrap_or_default();
            return Err(format!("{refused}{named}"));
        }
    };
    crate::shell::session_fs::replace(&ws.root, &dir.join("plan.bin"), &plan)?;
    let header = inspect(ws, "pay-plan", &plan)?;
    let canonical = header.pointer("/header/canonical").and_then(Value::as_str).ok_or("job: plan lacks a header")?;
    let seed: [u8; 32] = private_bytes(&ws.key, 32)?
        .try_into()
        .map_err(|_| "job: workspace key must contain exactly 32 raw bytes")?;
    let signature = SigningKey::from_bytes(&seed).sign(&unhex(canonical)?).to_bytes();
    let ingress = invoke(ws, 161, &pair(&plan, &signature))?;
    crate::shell::session_fs::replace(&ws.root, &dir.join("ingress.bin"), &ingress)?;
    submit_ingress(ws, dir, &ingress)
}

fn submit_ingress(ws: &Ws, dir: &Path, ingress: &[u8]) -> Result<Value> {
    let outcome = inspect(ws, "outcome", &invoke(ws, 162, ingress)?)?;
    let stem = format!("outcome-{}.json", nonce()?);
    crate::shell::session_fs::replace(&ws.root, &dir.join(stem), outcome.to_string().as_bytes())?;
    if outcome.get("type").and_then(Value::as_str) == Some("confirmed") {
        Ok(outcome)
    } else {
        Err(refusal_line(&outcome).unwrap_or_else(|| format!("job: money turn not confirmed: {outcome}")))
    }
}

/// A reference's capability for writes (falls back to its observe capability).
fn operation_capability(reference: &Value) -> Result<String> {
    reference
        .get("operationCapability")
        .or_else(|| reference.get("observeCapability"))
        .and_then(Value::as_str)
        .map(str::to_owned)
        .ok_or_else(|| "job: the reference names no capability".into())
}

/// The kernel's dry run (op 134) of the job's program on the job's sample: the
/// claim a truth turn carries, and the writes it names.
fn dry_run(ws: &Ws, job: &str, fields: &BTreeMap<u32, String>) -> Result<(Value, Value)> {
    let program = fields.get(&1).ok_or("job: no program field")?;
    let show: Value = serde_json::from_slice(&invoke(ws, 132, program.as_bytes())?)
        .map_err(|error| format!("job: program show: {error}"))?;
    let sample = show.pointer("/abi/sample").and_then(Value::as_array).ok_or("job: program ABI lacks sample")?;
    let mut values = Vec::new();
    for slot in sample {
        let name = slot.get("slot").and_then(Value::as_str).ok_or("job: ABI sample slot")?;
        let parts: Vec<&str> = name.split('/').collect();
        let value = match parts.as_slice() {
            ["resource", "field", n, "before" | "after"] => fields
                .get(&n.parse::<u32>().map_err(|_| "job: ABI field")?)
                .cloned()
                .ok_or_else(|| format!("job: the program reads {name}, which the job does not hold"))?,
            _ => return Err(format!("job: the program reads {name}; a job program reads job fields")),
        };
        values.push(json!([slot.get("target").cloned().unwrap_or(json!("0")), name, value]));
    }
    let request = json!({"programId":program,"caller":ws.subject,"room":"0","targets":[job],"values":values});
    let dry: Value = serde_json::from_slice(&invoke(ws, 134, request.to_string().as_bytes())?)
        .map_err(|error| format!("job: dry run: {error}"))?;
    if dry.get("verdict").and_then(Value::as_str) != Some("ok") {
        return Err(format!("job: the program did not finish on the job's sample: {dry}"));
    }
    let claim = json!({"programId":program,"sample":dry.get("sample").cloned().unwrap_or(json!("")),
        "output":dry.get("output").cloned().unwrap_or(json!("")),"steps":dry.get("steps").cloned().unwrap_or(json!("0"))});
    Ok((claim, dry))
}

/// The value the program writes into the truth field (its one output write).
fn truth_of(dry: &Value) -> Result<String> {
    let writes = dry.get("writes").and_then(Value::as_array).ok_or("job: dry run lacks writes")?;
    writes
        .iter()
        .find(|w| w.get(1).and_then(Value::as_str) == Some(&TRUTH.to_string()))
        .and_then(|w| w.get(2).and_then(Value::as_str))
        .map(str::to_owned)
        .ok_or_else(|| "job: the program names no write of the truth field (15); it is not a job program".into())
}

fn timed<T>(label: &str, f: impl FnOnce() -> Result<T>) -> Result<(T, f64)> {
    let start = Instant::now();
    let value = f().map_err(|error| format!("{label}: {error}"))?;
    Ok((value, start.elapsed().as_secs_f64()))
}

// ---------------------------------------------------------------- actions

fn post(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = match opt(&mut args, "name")? {
        Some(name) => name,
        None => format!("job-{}", &nonce()?[..8]),
    };
    let room = arg(&mut args, "room")?;
    let program = decimal(&arg(&mut args, "program")?, "--program")?;
    let input = decimal(&arg(&mut args, "input")?, "--input")?;
    let price = decimal(&arg(&mut args, "price")?, "--price")?;
    let deadline: i128 = decimal(&arg(&mut args, "deadline")?, "--deadline")?.parse().map_err(|_| "--deadline")?;
    let window: i128 = match opt(&mut args, "window")? {
        Some(w) => decimal(&w, "--window")?.parse().map_err(|_| "--window")?,
        None => DEFAULT_WINDOW,
    };
    let account_ref = arg(&mut args, "account")?;
    args.finish()?;
    name_ok(&name)?;
    name_ok(&room)?;
    if price == "0" {
        return Err("job: a job's price is positive (the law's clause 8)".into());
    }
    if deadline < 2 {
        return Err("job: --deadline is the answer deadline in clock seconds (at least 2)".into());
    }
    let account = workspace::reference(&ws.root, &account_ref)?;
    let account_id = field(&account, "target")?.to_owned();
    let account_cap = operation_capability(&account)?;
    let clock = now(ws)?;
    let claim_by = clock + deadline / 2;
    let answer_by = clock + deadline;
    // The law, bound: CALLER, PROGRAM, WINDOW (`fields.json` placeholders).
    let law = LAW
        .replace("{CALLER}", &ws.subject)
        .replace("{PROGRAM}", &program)
        .replace("{NEG_WINDOW}", &format!("-{window}"))
        .replace("{WINDOW}", &window.to_string());
    let law_path = jobs_dir(ws)?.join(format!("{name}.law.json"));
    crate::shell::session_fs::replace(&ws.root, &law_path, law.as_bytes())?;
    let ((), birth) = timed("post (birth)", || {
        client(
            "workspace",
            &[
                ("action", "create".into()),
                ("dir", ws.root.clone().into()),
                ("name", name.clone().into()),
                ("storage", "declared".into()),
                ("predicate", law_path.clone().into()),
                ("in", room.clone().into()),
                // K-FIELD-CLOSURE: a job cell declares exactly its sixteen fields.
                ("fields", "0-15".into()),
            ],
        )
    })?;
    let reference = workspace::reference(&ws.root, &name)?;
    let target = field(&reference, "target")?.to_owned();
    let mut rec = json!({"type":"minidregg-job-v1","name":name,"job":target,"room":room,"role":"caller",
        "program":program,"input":input,"price":price,"window":window.to_string(),
        "claimBy":claim_by.to_string(),"answerBy":answer_by.to_string(),"callerAcct":account_id});
    save(ws, &name, &rec)?;
    // The order: the cell is born holding no field (it declares 0-15), so every order field is created.
    let order = vec![
        create(0, 0),
        create(1, &program),
        create(2, &input),
        create(3, &ws.subject),
        create(4, &account_id),
        create(5, &price),
        create(6, claim_by),
        create(7, answer_by),
        create(8, 0),
        create(9, 0),
        create(10, 0),
        create(11, 0),
    ];
    let (_, ordered) = timed("post (order)", || write(ws, &format!("{name}-order"), &name, order, None))?;
    let dir = jobs_dir(ws)?.join(format!("{name}.fund"));
    let (_, funded) = timed("post (fund)", || money(ws, &dir, &target, FUND, &account_id, &price, &account_cap, "0"))?;
    rec["latency"] = json!({"birth":birth,"order":ordered,"fund":funded});
    save(ws, &name, &rec)?;
    Ok(json!({"type":"job-posted","job":target,"name":name,"room":room,"program":program,"input":input,
        "price":price,"claimBy":claim_by.to_string(),"answerBy":answer_by.to_string(),"window":window.to_string(),
        "escrow":price,"latency":{"birth":birth,"order":ordered,"fund":funded,"total":birth + ordered + funded}}))
}

fn claim(ws: &Ws, mut args: Args) -> Result<Value> {
    let job = decimal(&arg(&mut args, "job")?, "--job")?;
    let name = opt(&mut args, "name")?.unwrap_or_else(|| format!("job-{job}"));
    let room = opt(&mut args, "room")?;
    let bond = decimal(&arg(&mut args, "bond")?, "--bond")?;
    let account_ref = arg(&mut args, "account")?;
    args.finish()?;
    name_ok(&name)?;
    // The claimer's capability on the job: the job reference it already holds (a
    // delegation), or else its room grant -- a member's `under ROOM` covers the jobs
    // born in the room.
    let held = workspace::reference(&ws.root, &name).ok();
    let cap = match (&held, &room) {
        (Some(reference), _) => operation_capability(reference)?,
        (None, Some(room)) => {
            name_ok(room)?;
            operation_capability(&workspace::reference(&ws.root, room)?)?
        }
        (None, None) => return Err("job: claim needs --room ROOM (the room the job was posted in)".into()),
    };
    if held.is_none() {
        client(
            "workspace",
            &[
                ("action", "import".into()),
                ("dir", ws.root.clone().into()),
                ("name", name.clone().into()),
                ("kind", "object".into()),
                ("target", job.clone().into()),
                ("observe-capability", cap.clone().into()),
                ("operation-capability", cap.clone().into()),
            ],
        )?;
    }
    let account = workspace::reference(&ws.root, &account_ref)?;
    let account_id = field(&account, "target")?.to_owned();
    let account_cap = operation_capability(&account)?;
    let dir = jobs_dir(ws)?.join(format!("{name}.claim-{}", nonce()?));
    let (_, latency) = timed("claim", || money(ws, &dir, &job, CLAIM, &account_id, &bond, &account_cap, &cap))?;
    // The job as the provider now holds it (a signed read under its grant).
    let f = fields(ws, &name)?;
    let policy = {
        let reference = workspace::reference(&ws.root, &name)?;
        workspace::signed_view(&ws.root, &ws.pin, &reference, "policy").map(|v| v.0).ok()
    };
    // WINDOW is the law's constant: clause 34's offset (`finalAt <= clock now + WINDOW`).
    let window = policy
        .as_ref()
        .and_then(find_window)
        .unwrap_or_else(|| DEFAULT_WINDOW.to_string());
    let rec = json!({"type":"minidregg-job-v1","name":name,"job":job,"room":room,"role":"provider",
        "program":f.get(&1),"input":f.get(&2),"price":f.get(&5),"claimBy":f.get(&6),"answerBy":f.get(&7),
        "window":window,"providerAcct":account_id,"bond":bond});
    save(ws, &name, &rec)?;
    Ok(json!({"type":"job-claimed","job":job,"name":name,"bond":bond,"program":f.get(&1),"input":f.get(&2),
        "price":f.get(&5),"answerBy":f.get(&7),"window":window,"latency":{"claim":latency}}))
}

/// The WINDOW constant out of a job law (clause 34's `leSlotsOff` offset).
fn find_window(policy: &Value) -> Option<String> {
    fn walk(v: &Value) -> Option<String> {
        if v.get("type").and_then(Value::as_str) == Some("leSlotsOff")
            && v.get("left").and_then(Value::as_str) == Some("resource/field/14/after")
            && v.get("right").and_then(Value::as_str) == Some("clock/now")
        {
            return v.get("offset").and_then(Value::as_str).map(str::to_owned);
        }
        match v {
            Value::Object(map) => map.values().find_map(walk),
            Value::Array(items) => items.iter().find_map(walk),
            _ => None,
        }
    }
    walk(policy)
}

/// The caller funds an ordered job (the money turn `post` ends with), for a job
/// ordered outside `post`.
fn fund(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = arg(&mut args, "name")?;
    let account_ref = arg(&mut args, "account")?;
    // The deposit is the price; `--amount` names another (the money decision refuses it).
    let amount = opt(&mut args, "amount")?.map(|a| decimal(&a, "--amount")).transpose()?;
    args.finish()?;
    let rec = record(ws, &name)?;
    let job = field(&rec, "job")?.to_owned();
    // The price is read from the job unless the deposit is named.
    let price = match amount {
        Some(amount) => amount,
        None => fields(ws, &name)?.get(&5).cloned().ok_or("job: the job has no price")?,
    };
    let account = workspace::reference(&ws.root, &account_ref)?;
    let dir = jobs_dir(ws)?.join(format!("{name}.fund-{}", nonce()?));
    let (_, latency) = timed("fund", || {
        money(ws, &dir, &job, FUND, field(&account, "target")?, &price, &operation_capability(&account)?, "0")
    })?;
    Ok(json!({"type":"job-funded","job":job,"name":name,"escrow":price,"latency":{"fund":latency}}))
}

/// The truth turn alone: the job's program re-executed by the kernel on the job's
/// sample, its output written to the truth field under the run claim. In state 2
/// anyone in the window; in state 1 the provider (the synchronous path).
fn truth(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = arg(&mut args, "name")?;
    args.finish()?;
    let rec = record(ws, &name)?;
    let job = field(&rec, "job")?.to_owned();
    let f = fields(ws, &name)?;
    let ((claim, dry), ran) = timed("truth (run)", || dry_run(ws, &job, &f))?;
    let value = truth_of(&dry)?;
    let (_, latency) = timed("truth", || {
        write(ws, &format!("{name}-truth-{}", nonce()?), &name, vec![create(TRUTH, &value)], Some(claim.clone()))
    })?;
    Ok(json!({"type":"job-truth","job":job,"truth":value,"kernelSteps":claim.get("steps"),
        "latency":{"run":ran,"truth":latency}}))
}

fn answer(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = arg(&mut args, "name")?;
    let output = opt(&mut args, "output")?;
    let steps = opt(&mut args, "steps")?;
    args.finish()?;
    let rec = record(ws, &name)?;
    let job = field(&rec, "job")?.to_owned();
    let window = window_of(ws, &name, &rec)?;
    let f = fields(ws, &name)?;
    if get(&f, STATE)? != 1 {
        return Err(format!("job: {name} is {}, not claimed", STATES[get(&f, STATE)? as usize]));
    }
    // The provider's node runs the program on the job's sample unless an output is given.
    let (computed, ran) = match &output {
        Some(output) => ((decimal(output, "--output")?, steps.clone().unwrap_or("0".into())), 0.0),
        None => {
            let ((claim, dry), secs) = timed("answer (run)", || dry_run(ws, &job, &f))?;
            ((truth_of(&dry)?, claim.get("steps").and_then(Value::as_str).unwrap_or("0").to_owned()), secs)
        }
    };
    let final_at = now(ws)? + window;
    let actions = vec![
        update(STATE, 1, 2),
        create(OUTPUT, &computed.0),
        create(STEPS, &computed.1),
        create(FINAL_AT, final_at),
    ];
    let (_, latency) = timed("answer", || write(ws, &format!("{name}-answer-{}", nonce()?), &name, actions, None))?;
    Ok(json!({"type":"job-answered","job":job,"name":name,"output":computed.0,"steps":computed.1,
        "finalAt":final_at.to_string(),"latency":{"run":ran,"answer":latency}}))
}

fn check(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = arg(&mut args, "name")?;
    args.finish()?;
    let rec = record(ws, &name)?;
    let job = field(&rec, "job")?.to_owned();
    let f = fields(ws, &name)?;
    let state = get(&f, STATE)?;
    let clock = now(ws)?;
    let id = |what: &str| -> Result<String> { Ok(format!("{name}-{what}-{}", nonce()?)) };
    match state {
        // The stall: claimed, no truth, answerBy past.
        1 if f.get(&TRUTH).is_none() && clock > get(&f, 7)? => {
            let (_, decide) = timed("check (stall)", || write(ws, &id("stall")?, &name, vec![update(STATE, 1, 4)], None))?;
            Ok(json!({"type":"job-checked","job":job,"verdict":"slashed","why":"stall: no answer by answerBy",
                "answerBy":f.get(&7),"now":clock.to_string(),"latency":{"decide":decide}}))
        }
        // The synchronous path: the provider's own run is on the cell.
        1 if f.get(&TRUTH).is_some() => {
            let (_, decide) = timed("check (decide)", || write(ws, &id("decide")?, &name, vec![update(STATE, 1, 3)], None))?;
            Ok(json!({"type":"job-checked","job":job,"verdict":"upheld","why":"the provider's own run",
                "truth":f.get(&TRUTH),"latency":{"decide":decide}}))
        }
        2 if f.get(&TRUTH).is_none() && clock > get(&f, FINAL_AT)? => {
            let (_, decide) = timed("check (timeout)", || write(ws, &id("timeout")?, &name, vec![update(STATE, 2, 3)], None))?;
            Ok(json!({"type":"job-checked","job":job,"verdict":"upheld","why":"timeout: no truth by finalAt",
                "latency":{"decide":decide}}))
        }
        2 => {
            // The truth turn: the kernel re-executes the job's program on its own sample and
            // admits the write only if it is the program's product; the law needs `ran PROGRAM`.
            let ((claim, dry), ran) = timed("check (run)", || dry_run(ws, &job, &f))?;
            let truth_started = Instant::now();
            let truth = match f.get(&TRUTH) {
                Some(t) => t.clone(),
                None => {
                    let truth = truth_of(&dry)?;
                    // The sample carries the admission height: an admission in between makes
                    // the claim sampleStale, and the kernel's dry run is simply asked again.
                    let first = write(ws, &id("truth")?, &name, vec![create(TRUTH, &truth)], Some(claim.clone()));
                    match first {
                        Ok(_) => {}
                        Err(e) if e.contains("sampleStale") => {
                            let (again, _) = dry_run(ws, &job, &f)?;
                            write(ws, &id("truth")?, &name, vec![create(TRUTH, &truth)], Some(again))
                                .map_err(|e| format!("check (truth): {e}"))?;
                        }
                        Err(e) => return Err(format!("check (truth): {e}")),
                    }
                    truth
                }
            };
            let truth_secs = ran;
            let truth_write = truth_started.elapsed().as_secs_f64();
            let output = f.get(&OUTPUT).cloned().ok_or("job: answered without output")?;
            let verdict = if truth == output { 3 } else { 4 };
            let (_, decide) = timed("check (decide)", || write(ws, &id("decide")?, &name, vec![update(STATE, 2, verdict)], None))?;
            Ok(json!({"type":"job-checked","job":job,"truth":truth,"output":output,
                "verdict":STATES[verdict as usize],"kernelSteps":claim.get("steps"),
                "latency":{"run":truth_secs,"truth":truth_write,"decide":decide}}))
        }
        _ => Err(format!(
            "job: {name} is {}; check decides an answered job (or a claimed one past answerBy)",
            STATES.get(state as usize).unwrap_or(&"?")
        )),
    }
}

fn settle(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = arg(&mut args, "name")?;
    args.finish()?;
    let rec = record(ws, &name)?;
    let job = field(&rec, "job")?.to_owned();
    // Settling again is the same turn: the retained ingress of the confirmed settle,
    // resubmitted, answers the original receipt (replay), never a second payout. A
    // refused attempt is kept for the record and a fresh one is made.
    let jobs = jobs_dir(ws)?;
    let mut tried: Vec<PathBuf> = fs::read_dir(&jobs)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with(&format!("{name}.settle-"))))
        .collect();
    tried.sort();
    for previous in &tried {
        let confirmed = fs::read_dir(previous).map_err(|e| e.to_string())?.filter_map(|e| e.ok()).any(|e| {
            fs::read(e.path())
                .ok()
                .and_then(|b| serde_json::from_slice::<Value>(&b).ok())
                .is_some_and(|v| v.get("type").and_then(Value::as_str) == Some("confirmed"))
        });
        if confirmed {
            let ingress = fs::read(previous.join("ingress.bin")).map_err(|e| e.to_string())?;
            let (outcome, latency) = timed("settle (resubmit)", || submit_ingress(ws, previous, &ingress))?;
            return Ok(json!({"type":"job-settled","job":job,"resubmitted":true,"outcome":outcome,"latency":{"settle":latency}}));
        }
    }
    let dir = jobs.join(format!("{name}.settle-{}", nonce()?));
    let reference = workspace::reference(&ws.root, &name)?;
    let cap = operation_capability(&reference)?;
    // Reads around the turn are for the report; the turn itself needs only the capability.
    let before = fields(ws, &name).unwrap_or_default();
    let (outcome, latency) = timed("settle", || money(ws, &dir, &job, SETTLE, "0", "0", &cap, "0"))?;
    let after = fields(ws, &name).unwrap_or_default();
    Ok(json!({"type":"job-settled","job":job,"from":before.get(&STATE).and_then(|s| s.parse::<usize>().ok()).and_then(|s| STATES.get(s)),
        "fields":named(&after),"outcome":outcome,"latency":{"settle":latency}}))
}

fn show(ws: &Ws, mut args: Args) -> Result<Value> {
    let name = arg(&mut args, "name")?;
    args.finish()?;
    let rec = record(ws, &name).unwrap_or(json!({}));
    let f = fields(ws, &name)?;
    Ok(json!({"type":"job","name":name,"job":rec.get("job"),"room":rec.get("room"),"role":rec.get("role"),
        "fields":named(&f)}))
}

fn list(ws: &Ws, mut args: Args) -> Result<Value> {
    let room = arg(&mut args, "room")?;
    args.finish()?;
    let mut jobs = Vec::new();
    let dir = jobs_dir(ws)?;
    let mut names: Vec<String> = fs::read_dir(&dir)
        .map_err(|e| e.to_string())?
        .filter_map(|e| e.ok()?.file_name().into_string().ok())
        .filter(|n| n.ends_with(".json") && !n.ends_with(".law.json"))
        .map(|n| n.trim_end_matches(".json").to_owned())
        .collect();
    names.sort();
    for name in names {
        let Ok(rec) = record(ws, &name) else { continue };
        if rec.get("room").and_then(Value::as_str) != Some(room.as_str()) {
            continue;
        }
        let state = fields(ws, &name)
            .ok()
            .and_then(|f| f.get(&STATE).and_then(|s| s.parse::<usize>().ok()))
            .and_then(|s| STATES.get(s).copied())
            .unwrap_or("unreadable");
        jobs.push(json!({"name":name,"job":rec.get("job"),"role":rec.get("role"),"state":state,
            "price":rec.get("price"),"program":rec.get("program")}));
    }
    Ok(json!({"type":"jobs","room":room,"jobs":jobs}))
}

/// `mini job --action post|claim|answer|check|settle|show|list --dir WORKSPACE ...`.
pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = arg(&mut args, "action")?;
    let ws = ws(path(args.required("dir")?))?;
    let value = match action.as_str() {
        "post" => post(&ws, args)?,
        "claim" => claim(&ws, args)?,
        "fund" => fund(&ws, args)?,
        "truth" => truth(&ws, args)?,
        "answer" => answer(&ws, args)?,
        "check" => check(&ws, args)?,
        "settle" => settle(&ws, args)?,
        "show" => show(&ws, args)?,
        "list" => list(&ws, args)?,
        _ => return Err("job --action must be post, fund, claim, answer, truth, check, settle, show or list".into()),
    };
    println!("{}", serde_json::to_string(&value).map_err(|e| e.to_string())?);
    Ok(())
}

#[cfg(test)]
mod path_tests {
    use super::*;
    #[test]
    fn job_record_updates_are_atomic_and_symlinks_never_read_or_written() {
        use std::os::unix::fs::symlink;
        let root = std::env::temp_dir().join(format!("mini-job-record-{}", std::process::id()));
        fs::create_dir(&root).unwrap();
        let ws = Ws { root:root.clone(), pin:json!({}), host:"/unused".into(), socket:"/unused".into(), config:"/unused".into(), key:"/unused".into(), subject:"0".into() };
        let first = json!({"type":"minidregg-job-v1","job":"42","window":"10"});
        save(&ws, "valid", &first).unwrap();
        assert_eq!(record(&ws, "valid").unwrap(), first);
        let second = json!({"type":"minidregg-job-v1","job":"42","window":"11"});
        save(&ws, "valid", &second).unwrap();
        assert_eq!(record(&ws, "valid").unwrap(), second);
        let external = root.join("foreign.json");
        fs::write(&external, b"retained foreign bytes").unwrap();
        symlink(&external, root.join("jobs/escape.json")).unwrap();
        assert!(record(&ws, "escape").is_err());
        assert!(save(&ws, "escape", &second).is_err());
        assert_eq!(fs::read(&external).unwrap(), b"retained foreign bytes");
        symlink(&root, root.join("linked-jobs")).unwrap();
        assert!(crate::shell::session_fs::replace(&root, &root.join("linked-jobs/foreign.json"), b"bad").is_err());
        assert_eq!(fs::read(&external).unwrap(), b"retained foreign bytes");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn job_names_refuse_escape_before_any_directory_is_created() {
        let root = std::env::temp_dir().join(format!("mini-job-path-{}", std::process::id()));
        let ws = Ws { root:root.clone(), pin:json!({}), host:"/unused".into(), socket:"/unused".into(), config:"/unused".into(), key:"/unused".into(), subject:"0".into() };
        for name in ["../outside", "/outside", "a/b", ".", "", "a\\b"] {
            assert!(record_path(&ws, name).is_err());
            let mut args = Args { command:"job".into(), values:vec![("--name".into(), name.into())] };
            assert!(arg(&mut args, "name").is_err());
        }
        assert!(!root.exists());
        for name in ["job-one", "job_2", "J3"] { assert!(name_ok(name).is_ok()); }
    }
}
