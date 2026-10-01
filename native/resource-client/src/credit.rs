//! P-CREDIT (PLACE §2.10): a week in a room, bought with a posting.
//!
//! A room's tariff is data on the room cell `R` itself: declared fields
//! (`TARIFF_FIELDS`), written only by a holder of `mutate` on `R` (the
//! founder; members and the concierge hold observe/place/append/delegate).
//! Paying is one fleet turn: `credit` moves from my account to the room's till
//! `A_R` and the turn publishes `renew` on my account's topic. The till's
//! incoming ledger (Host op 180) is the room's view of who paid when. The
//! room's concierge (`grain-runtime concierge`) reads that ledger and issues
//! each payer a member capability `under R` whose window ends at
//! `entry.height + period`; the Host refuses any request above it
//! (`Admissible.validUntil`, refusal `outside-validity`). Nothing here decides
//! admission: every number shown is a signed read, every act a submitted turn.
use crate::workspace::{self, ImportInput};
use crate::{absolute, path, print_json, Args, Result};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};

/// The room cell's tariff fields: name → declared field key of `R`.
/// `week`: credit a week costs (0 = free: the concierge issues on request);
/// `birth` and `hermes/turn`: the room's prices for items 7/8 (stored, not yet
/// charged by anything here); `till`: the room account `A_R` payments go to;
/// `period`: a week's length in heights; `runner`: the concierge's own account
/// `A_P` (`topup` funds it); `concierge`: the concierge's subject.
pub(crate) const TARIFF_FIELDS: &[(&str, &str)] = &[
    ("week", "1"),
    ("birth", "2"),
    ("hermes/turn", "3"),
    ("till", "4"),
    ("period", "5"),
    ("runner", "6"),
    ("concierge", "7"),
];

/// Fields a founder sets by `tariff ROOM set FIELD N`; the rest are written
/// by `room concierge` (install) and name accounts and subjects.
const SETTABLE: &[&str] = &["week", "birth", "hermes/turn", "period"];

pub(crate) const RENEW_TOPIC: &str = "renew";

/// What a member's week grants under the room: read, bear cells into it, and
/// append (speak on its streams). Never `mutate`, so a member cannot write the
/// room cell's tariff; never `delegate`.
pub(crate) const MEMBER_VERBS: &[&str] = &["observe", "place", "append"];

/// The concierge's grant under the room: the member verbs plus `delegate`.
const CONCIERGE_VERBS: &[&str] = &["observe", "place", "append", "delegate"];

const DEFAULT_PERIOD: &str = "2016";
const MAX_COST: &str = "50000";

fn text(value: OsString, label: &str) -> Result<String> {
    value.into_string().map_err(|_| format!("{label} must be UTF-8"))
}

fn opt(args: &mut Args, key: &str) -> Result<Option<String>> {
    args.optional(key).map(|value| text(value, key)).transpose()
}

fn decimal(value: &str, label: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 40
        || value.starts_with('0') && value != "0"
        || !value.bytes().all(|byte| byte.is_ascii_digit())
    {
        return Err(format!("{label} must be a canonical decimal"));
    }
    Ok(())
}

fn number(value: &str, label: &str) -> Result<u128> {
    decimal(value, label)?;
    value.parse().map_err(|_| format!("{label} out of range"))
}

fn field_key(name: &str) -> Result<&'static str> {
    TARIFF_FIELDS
        .iter()
        .find(|(field, _)| *field == name)
        .map(|(_, key)| *key)
        .ok_or_else(|| {
            format!(
                "tariff field is one of {}",
                TARIFF_FIELDS.iter().map(|(f, _)| *f).collect::<Vec<_>>().join(", ")
            )
        })
}

fn write_json(path: &Path, value: &Value) -> Result<()> {
    let mut bytes = serde_json::to_vec_pretty(value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    if path.exists() {
        if fs::read(path).map_err(|error| error.to_string())? == bytes {
            return Ok(());
        }
        return Err(format!("{} exists with other contents", path.display()));
    }
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    workspace::private_file(path, &bytes)
}

fn ref_exists(root: &Path, name: &str) -> bool {
    root.join("refs").join(format!("{}.json", workspace::ref_file(name))).exists()
}

// ---------------------------------------------------------------- the room's tariff

/// The room as one signed read of `R` through the reference `via`.
pub(crate) struct Room {
    pub target: String,
    pub height: u128,
    pub root: String,
    /// Tariff field name → value, only the fields `R` holds.
    pub fields: BTreeMap<&'static str, String>,
}

impl Room {
    fn get(&self, name: &str) -> Option<&str> {
        self.fields.get(name).map(String::as_str)
    }

    fn need(&self, name: &str) -> Result<&str> {
        self.get(name).ok_or_else(|| {
            format!("room {} has no tariff field {name} (`tariff ROOM` shows it; the founder sets it)", self.target)
        })
    }

    fn json(&self) -> Value {
        let tariff: serde_json::Map<String, Value> =
            self.fields.iter().map(|(k, v)| (k.to_string(), json!(v))).collect();
        json!({"type":"minidregg-room-tariff-v1","room":self.target,"height":self.height.to_string(),
            "root":self.root,"tariff":tariff,"authority":"signed-read"})
    }
}

/// The reference a member reads the room through: `NAME-guest` when the
/// member's window replaced `NAME` (a guest's grant outlives the window).
fn read_ref(root: &Path, name: &str) -> String {
    let guest = format!("{name}-guest");
    if ref_exists(root, &guest) {
        guest
    } else {
        name.to_owned()
    }
}

pub(crate) fn room(root: &Path, ws: &Value, name: &str) -> Result<Room> {
    let reference = workspace::reference(root, &read_ref(root, name))?;
    if workspace::member(&reference, "kind")? != "object" {
        return Err(format!("reference {name} is not a room"));
    }
    let (view, challenge, _) = workspace::signed_view(root, ws, &reference, "resource")?;
    let height = number(workspace::member(&challenge, "height")?, "signed height")?;
    let cell = view.get("cell").ok_or("signed room view lacks its cell")?;
    let mut fields = BTreeMap::new();
    for entry in cell.get("entries").and_then(Value::as_array).into_iter().flatten() {
        let (Some(key), Some(value)) = (
            entry.get("key").and_then(|key| key.get("field")).and_then(Value::as_str),
            entry.get("value").and_then(Value::as_str),
        ) else {
            continue;
        };
        if let Some((field, _)) = TARIFF_FIELDS.iter().find(|(_, k)| *k == key) {
            fields.insert(*field, value.to_owned());
        }
    }
    Ok(Room {
        target: workspace::member(&reference, "target")?.to_owned(),
        height,
        root: cell.get("root").and_then(Value::as_str).unwrap_or("").to_owned(),
        fields,
    })
}

/// One proposal file and its id under this workspace; `stem` names it.
fn proposal_request(root: &Path, id: &str, request: &Value) -> Result<PathBuf> {
    workspace::validate_name(id)?;
    let path = root.join("sources").join(format!("credit-{id}.request.json"));
    write_json(&path, request)?;
    Ok(path)
}

/// Propose (once) and submit (once; afterwards an exact lookup) proposal `id`.
fn propose_and_submit(root: &Path, ws: &Value, id: &str, request: &Value) -> Result<PathBuf> {
    let request_path = proposal_request(root, id, request)?;
    let proposal = root.join("proposals").join(id);
    if !proposal.join("proposal.json").exists() {
        workspace::propose(root, ws, &request_path, id, None)?;
    }
    let attempt = root.join("attempts").join(id);
    if attempt.join("call.bin").exists() {
        workspace::recover(root, &attempt)?;
    } else {
        if attempt.exists() {
            // A previous run stopped before it signed: nothing was sent.
            fs::rename(&attempt, root.join("attempts").join(format!("{id}-unsent-{}", workspace::random_nonce()?)))
                .map_err(|error| error.to_string())?;
        }
        workspace::submit_intent(root, ws, &proposal.join("intent.json"), "intent", false, Some(&attempt))?;
    }
    if workspace::accepted_outcome(&attempt)?.is_none() {
        return Err(format!("proposal {id} was not admitted; its attempt is {}", attempt.display()));
    }
    Ok(attempt)
}

/// Write tariff fields of `R` in one scalar turn: `create` for a field `R`
/// lacks, `write` (expecting the signed value just read) for one it holds.
fn set_fields(root: &Path, ws: &Value, name: &str, room: &Room, values: &[(&str, String)]) -> Result<PathBuf> {
    let mut actions = Vec::new();
    for (field, value) in values {
        let key = field_key(field)?;
        decimal(value, field)?;
        actions.push(match room.get(field) {
            None => json!({"type":"create","key":{"type":"object","field":key},"value":value}),
            Some(current) => json!({"type":"write","key":{"type":"object","field":key},"value":value,"expected":current}),
        });
    }
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
        "targets":[{"name":name,"payload":{"type":"scalar","actions":actions}}]});
    let id = format!("tariff-{}-{}", room.height, workspace::random_nonce()?);
    propose_and_submit(root, ws, &id, &request)
}

// ---------------------------------------------------------------- my account

/// This workspace's paying account reference: `explicit`, else its one
/// account reference, else the account its provisioning names (the birth
/// context's fee payer and the account grant it holds), imported once as
/// `account`.
pub(crate) fn my_account(root: &Path, ws: &Value, explicit: Option<&str>) -> Result<String> {
    if let Some(name) = explicit {
        return Ok(name.to_owned());
    }
    let mut accounts = Vec::new();
    for entry in fs::read_dir(root.join("refs")).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let file = entry.file_name().to_string_lossy().into_owned();
        let Some(stem) = file.strip_suffix(".json") else { continue };
        let name = workspace::ref_name_of_file(stem);
        if let Ok(reference) = workspace::reference(root, &name) {
            if workspace::member(&reference, "kind")? == "account"
                && !name.ends_with("-till")
                && !name.ends_with("-runner")
            {
                accounts.push(name);
            }
        }
    }
    accounts.sort();
    match accounts.len() {
        1 => return Ok(accounts.remove(0)),
        0 => {}
        _ if accounts.iter().any(|name| name == "account") => return Ok("account".into()),
        _ => return Err(format!("several account references ({}); name one with --account", accounts.join(", "))),
    }
    let context = workspace::bounded_json(&workspace::member_path(ws, "birthContext")?)
        .map_err(|error| format!("no account reference and no provisioning to name one: {error}"))?;
    let payer = workspace::member(&context, "feePayer")?;
    let grant = context
        .get("grants")
        .and_then(Value::as_array)
        .and_then(|grants| {
            grants.iter().find(|grant| {
                grant.get("kind").and_then(Value::as_str) == Some("account")
                    && grant.get("target").and_then(Value::as_str) == Some(payer)
            })
        })
        .ok_or("the provisioning names no grant over its fee payer")?;
    let capability = workspace::member(grant, "capability")?;
    workspace::import(
        root,
        ImportInput {
            name: "account",
            kind: "account",
            target: payer,
            observe: capability,
            operation: Some(capability),
            control: None,
            provenance: None,
            room: None,
        },
    )?;
    Ok("account".into())
}

// ---------------------------------------------------------------- windows

/// Where the adopted window of room reference `name` is noted: the
/// capability `NAME` presents and the `notAfter` its signed capability view
/// stated when it was adopted (a read the Host made while the window was open;
/// after it ends the capability no longer reads, by design).
fn window_note(root: &Path, name: &str) -> PathBuf {
    root.join("credit").join("windows").join(format!("{}.json", workspace::ref_file(name)))
}

/// My current window under the room, as noted at adoption. `None`: `NAME`
/// is still a guest reference.
fn window(root: &Path, name: &str) -> Result<Option<(String, String)>> {
    let note = window_note(root, name);
    if !note.exists() {
        return Ok(None);
    }
    let value = workspace::bounded_json(&note)?;
    Ok(Some((
        workspace::member(&value, "capability")?.to_owned(),
        workspace::member(&value, "notAfter")?.to_owned(),
    )))
}

/// The signed capability view of `capability` (presented as the grant it
/// reads): its `notAfter` and whether it may `place` (a member's window; a
/// guest's observe/append invite is not one).
fn window_of(root: &Path, ws: &Value, via: &str, capability: &str) -> Result<(String, bool)> {
    let mut reference = workspace::reference(root, via)?;
    reference["observeCapability"] = json!(capability);
    let (view, _, _) = workspace::signed_view(root, ws, &reference, "capability")?;
    let head = view.get("head").ok_or("capability view lacks head")?;
    let places = head
        .get("verbs")
        .and_then(Value::as_array)
        .is_some_and(|verbs| verbs.iter().any(|verb| verb.as_str() == Some("place")));
    Ok((workspace::member(head, "notAfter")?.to_owned(), places))
}

/// Adopt the newest member window for room `name` from `inbox`: every
/// delegated room reference addressed to me whose target is the room; the one
/// whose signed capability view ends latest replaces `NAME` (the guest
/// reference moves to `NAME-guest` the first time). Returns the adopted
/// (capability, notAfter), if any is newer than what `NAME` presents.
fn adopt_window(root: &Path, ws: &Value, name: &str, room: &Room, inbox: &Path) -> Result<Option<(String, String)>> {
    let me = workspace::member(ws, "subject")?;
    let mut candidates = Vec::new();
    let Ok(entries) = fs::read_dir(inbox) else { return Ok(None) };
    for entry in entries {
        let entry = entry.map_err(|error| error.to_string())?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Ok(value) = workspace::bounded_json(&path) else { continue };
        if value.get("type").and_then(Value::as_str) == Some("minidregg-delegated-reference-v1")
            && value.get("room") == Some(&json!(true))
            && value.get("recipient").and_then(Value::as_str) == Some(me)
            && value.get("target").and_then(Value::as_str) == Some(room.target.as_str())
        {
            if let Some(capability) = value.get("capability").and_then(Value::as_str) {
                candidates.push((capability.to_owned(), path));
            }
        }
    }
    let current = window(root, name)?;
    let via = read_ref(root, name);
    let mut best: Option<(String, String, PathBuf)> = None;
    for (capability, path) in candidates {
        if current.as_ref().is_some_and(|(held, _)| *held == capability) {
            continue;
        }
        let presented = workspace::reference(root, &via)?;
        if presented.get("operationCapability").and_then(Value::as_str) == Some(capability.as_str()) {
            continue;
        }
        // A window that has ended no longer reads (the Host refuses its view
        // outside-validity): it is not adoptable, whatever the inbox holds.
        let Ok((after, places)) = window_of(root, ws, &via, &capability) else {
            continue;
        };
        if !places {
            continue;
        }
        let newer = |other: &str| number(&after, "notAfter").ok() > number(other, "notAfter").ok();
        if current.as_ref().is_some_and(|(_, held)| !newer(held)) {
            continue;
        }
        if best.as_ref().is_some_and(|(_, held, _)| !newer(held)) {
            continue;
        }
        best = Some((capability, after, path));
    }
    let Some((capability, after, source)) = best else { return Ok(None) };
    let refs = root.join("refs");
    let file = |n: &str| refs.join(format!("{}.json", workspace::ref_file(n)));
    let guest = format!("{name}-guest");
    if !file(&guest).exists() {
        // The guest reference keeps its own name inside; rewrite it under the new one.
        let mut value = workspace::bounded_json(&file(name))?;
        value["name"] = json!(guest);
        let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
        bytes.push(b'\n');
        workspace::private_file(&file(&guest), &bytes)?;
    }
    let replaced = root.join("credit").join("replaced");
    fs::create_dir_all(&replaced).map_err(|error| error.to_string())?;
    let replaced = replaced.join(format!("{}-{}.json", workspace::ref_file(name), workspace::random_nonce()?));
    fs::rename(file(name), &replaced).map_err(|error| error.to_string())?;
    let value = workspace::bounded_json(&source)?;
    workspace::import(
        root,
        ImportInput {
            name,
            kind: "object",
            target: &room.target,
            observe: &capability,
            operation: Some(&capability),
            control: None,
            provenance: Some(&source),
            room: (value.get("room") == Some(&json!(true))).then_some("member"),
        },
    )?;
    let note = window_note(root, name);
    if note.exists() {
        fs::remove_file(&note).map_err(|error| error.to_string())?;
    }
    write_json(&note, &json!({"type":"minidregg-room-window-note-v1","room":room.target,
        "capability":capability,"notAfter":after,"adoptedAtHeight":room.height.to_string(),
        "source":source}))?;
    Ok(Some((capability, after)))
}

// ---------------------------------------------------------------- renew (the delegation)

/// Delegate a member window under the room to `subject`, ending at `not_after`,
/// as proposal `id` (idempotent: a rerun with the same id looks the attempt
/// up, never sends twice). Publishes the recipient reference and, with
/// `outbox`, leaves a copy in `outbox/SUBJECT/`.
pub(crate) fn renew(
    root: &Path,
    ws: &Value,
    name: &str,
    subject: &str,
    not_after: &str,
    id: &str,
    verbs: &[&str],
    outbox: Option<&Path>,
) -> Result<Value> {
    decimal(subject, "member subject")?;
    decimal(not_after, "notAfter")?;
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
        "name":name,"recipient":subject,"verbs":verbs,"maxCost":MAX_COST,"room":true,
        "notAfter":not_after});
    let attempt = propose_and_submit(root, ws, id, &request)?;
    workspace::publish_delegation(root, id, &attempt)?;
    let reference = root.join("proposals").join(id).join("recipient-reference.json");
    let value = workspace::bounded_json(&reference)?;
    let delivered = match outbox {
        Some(outbox) => {
            let path = outbox.join(subject).join(format!("{id}.json"));
            write_json(&path, &value)?;
            Some(path)
        }
        None => None,
    };
    let window = json!({"type":"minidregg-room-window-v1","room":workspace::member(&workspace::reference(root, name)?, "target")?,
        "subject":subject,"notAfter":not_after,"capability":value["capability"],
        "verbs":verbs,"proposal":id,"attempt":attempt,"receipt":value["receipt"],
        "reference":reference,"delivered":delivered,"authority":"admitted-delegation"});
    // Retained beside the proposal: a runner reads the decision's outcome from
    // here, not from this process's stdout.
    write_json(&root.join("proposals").join(id).join("window.json"), &window)?;
    Ok(window)
}

// ---------------------------------------------------------------- install (room concierge)

/// The founder installs a concierge for room `name`: births the till `A_R`
/// (an account the founder owns) and the runner account `A_P` (owned by the
/// concierge, funded `fund`), writes the tariff's account fields (and `week`
/// = 0, `period`, when `R` lacks them), grants the concierge `under R`
/// (member verbs + delegate) and observe on the till, and writes the program
/// the controller runs. Every step is resumable from what it retained.
fn install(
    root: &Path,
    ws: &Value,
    name: &str,
    concierge: &str,
    period: &str,
    fund: &str,
    outbox: &Path,
    program: &Path,
) -> Result<()> {
    decimal(concierge, "concierge subject")?;
    number(period, "period")?;
    decimal(fund, "runner funding")?;
    let me = workspace::member(ws, "subject")?.to_owned();
    let permit = root.join("sources").join("credit-permit-all.json");
    write_json(&permit, &json!({"type":"all","predicates":[]}))?;
    let till_name = format!("{name}-till");
    if !ref_exists(root, &till_name) {
        workspace::create(root, ws, &till_name, "declared", &permit, None, "account", None, None, None)?;
    }
    let till = workspace::reference(root, &till_name)?;
    let till_target = workspace::member(&till, "target")?.to_owned();
    let runner_name = format!("{name}-runner");
    let handoff = workspace::create_funded_account(
        root,
        ws,
        &runner_name,
        &json!({"type":"all","predicates":[]}),
        concierge,
        fund,
    )?;
    let runner_target = workspace::member(&handoff, "target")?.to_owned();
    write_json(&outbox.join(concierge).join(format!("{runner_name}.json")), &handoff)?;
    let current = room(root, ws, name)?;
    let mut values = vec![
        ("till", till_target.clone()),
        ("runner", runner_target.clone()),
        ("concierge", concierge.to_owned()),
    ];
    if current.get("week").is_none() {
        values.push(("week", "0".into()));
    }
    if current.get("period").is_none() {
        values.push(("period", period.to_owned()));
    }
    let values: Vec<_> = values
        .into_iter()
        .filter(|(field, value)| current.get(field) != Some(value.as_str()))
        .collect();
    if !values.is_empty() {
        set_fields(root, ws, name, &current, &values)?;
    }
    // The concierge's grant under the room, and its read of the till.
    let grant = format!("{name}-concierge");
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
        "name":name,"recipient":concierge,"verbs":CONCIERGE_VERBS,"maxCost":MAX_COST,"room":true});
    let attempt = propose_and_submit(root, ws, &grant, &request)?;
    workspace::publish_delegation(root, &grant, &attempt)?;
    write_json(
        &outbox.join(concierge).join(format!("{name}.json")),
        &workspace::bounded_json(&root.join("proposals").join(&grant).join("recipient-reference.json"))?,
    )?;
    let reads = format!("{name}-till-concierge");
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
        "name":till_name,"recipient":concierge,"verbs":["observe"],"maxCost":MAX_COST});
    let attempt = propose_and_submit(root, ws, &reads, &request)?;
    workspace::publish_delegation(root, &reads, &attempt)?;
    write_json(
        &outbox.join(concierge).join(format!("{till_name}.json")),
        &workspace::bounded_json(&root.join("proposals").join(&reads).join("recipient-reference.json"))?,
    )?;
    let value = json!({"type":"minidregg-concierge-program-v1","roomName":name,
        "room":current.target,"founder":me,"concierge":concierge,"till":till_target,
        "runner":runner_target,"topic":RENEW_TOPIC,"memberVerbs":MEMBER_VERBS,
        "refs":{"room":name,"till":till_name,"runner":runner_name},
        "program":"for each renew entry on the till's incoming ledger whose asset is the pinned credit asset: amount >= tariff.week issues `member` under the room to the payer's signer with notAfter = max(entry.height, the payer's current notAfter) + tariff.period; a smaller amount is journaled underpaid and issues nothing; when tariff.week = 0 every filed request from a standing room member issues height + period"});
    write_json(program, &value)?;
    print_json(&value)
}

/// Import every reference file in `inbox` this workspace does not hold yet,
/// under the file's stem: delegated references addressed to me, and account
/// handoffs naming me as owner.
fn adopt(root: &Path, ws: &Value, inbox: &Path) -> Result<()> {
    let me = workspace::member(ws, "subject")?;
    let mut adopted = Vec::new();
    for entry in fs::read_dir(inbox).map_err(|error| format!("{}: {error}", inbox.display()))? {
        let path = entry.map_err(|error| error.to_string())?.path();
        let Some(stem) = path.file_stem().and_then(|s| s.to_str()).map(str::to_owned) else { continue };
        if path.extension().and_then(|e| e.to_str()) != Some("json") || ref_exists(root, &stem) {
            continue;
        }
        let value = workspace::bounded_json(&path)?;
        match value.get("type").and_then(Value::as_str) {
            Some("minidregg-delegated-reference-v1") => {
                if workspace::member(&value, "recipient")? != me {
                    continue;
                }
                let capability = workspace::member(&value, "capability")?;
                workspace::import(
                    root,
                    ImportInput {
                        name: &stem,
                        kind: workspace::member(&value, "kind")?,
                        target: workspace::member(&value, "target")?,
                        observe: capability,
                        operation: Some(capability),
                        control: None,
                        provenance: Some(&path),
                        room: (value.get("room") == Some(&json!(true))).then_some("member"),
                    },
                )?;
            }
            Some("minidregg-fleet-account-handoff-v1") => {
                if workspace::member(&value, "owner")? != me {
                    continue;
                }
                workspace::import(
                    root,
                    ImportInput {
                        name: &stem,
                        kind: "account",
                        target: workspace::member(&value, "target")?,
                        observe: workspace::member(&value, "observeCapability")?,
                        operation: Some(workspace::member(&value, "operationCapability")?),
                        control: value.get("controlCapability").and_then(Value::as_str),
                        provenance: Some(&path),
                        room: None,
                    },
                )?;
            }
            _ => continue,
        }
        adopted.push(stem);
    }
    print_json(&json!({"type":"minidregg-credit-adopt-v1","adopted":adopted}))
}

// ---------------------------------------------------------------- verbs

fn show_tariff(room: &Room, name: &str) {
    println!("tariff of {name} (room {}) at height {}", room.target, room.height);
    for (field, _) in TARIFF_FIELDS {
        match room.get(field) {
            Some(value) => println!("  {field:<12} {value}"),
            None => println!("  {field:<12} -"),
        }
    }
}

pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = text(args.required("action")?, "credit action")?;
    let root = absolute(&path(args.required("dir")?))?;
    let ws = workspace::load(&root)?;
    match action.as_str() {
        "balance" => {
            let account = opt(&mut args, "account")?;
            args.finish()?;
            let name = my_account(&root, &ws, account.as_deref())?;
            let (balance, asset, height, target) = crate::fleet::account_balance(&root, &name)?;
            println!("credit {balance}  (asset {asset}, account {target}, signed read at height {height})");
            Ok(())
        }
        "room" => {
            let name = text(args.required("room")?, "room")?;
            args.finish()?;
            print_json(&room(&root, &ws, &name)?.json())
        }
        "tariff" => {
            let name = text(args.required("room")?, "room")?;
            let set = opt(&mut args, "set")?;
            let value = opt(&mut args, "value")?;
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            match (set, value) {
                (None, None) => {
                    show_tariff(&current, &name);
                    Ok(())
                }
                (Some(field), Some(value)) => {
                    if !SETTABLE.contains(&field.as_str()) {
                        return Err(format!(
                            "a founder sets {} (the accounts and the concierge are set by `room concierge`)",
                            SETTABLE.join(", ")
                        ));
                    }
                    set_fields(&root, &ws, &name, &current, &[(field.as_str(), value.clone())])?;
                    println!("tariff {name}: {field} = {value}");
                    Ok(())
                }
                _ => Err("tariff set needs --set FIELD and --value N".into()),
            }
        }
        "pay" => {
            let name = text(args.required("room")?, "room")?;
            let amount = opt(&mut args, "amount")?;
            let account = opt(&mut args, "account")?;
            let outbox = opt(&mut args, "outbox")?.map(PathBuf::from);
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            let week = current.need("week")?.to_owned();
            let till = current.need("till")?.to_owned();
            let amount = amount.unwrap_or_else(|| week.clone());
            decimal(&amount, "amount")?;
            if amount == "0" {
                // A free room: nothing to pay; the request is filed for the
                // concierge, which checks membership by a signed `who` read.
                let me = workspace::member(&ws, "subject")?;
                let outbox = outbox.ok_or("a free room's request is filed in an outbox (--outbox)")?;
                let concierge = current.need("concierge")?;
                let path = outbox
                    .join(concierge)
                    .join(format!("request-{}-{me}-{}.json", current.target, current.height));
                write_json(&path, &json!({"type":"minidregg-room-request-v1","room":current.target,
                    "subject":me,"height":current.height.to_string()}))?;
                println!("{name} is free (week 0): request filed for the concierge ({})", path.display());
                return Ok(());
            }
            let account = my_account(&root, &ws, account.as_deref())?;
            let payload = format!("room {}", current.target);
            let result = crate::fleet::pay_turn(
                &root,
                &account,
                &till,
                &amount,
                None,
                Some((RENEW_TOPIC, payload.as_bytes())),
            )?;
            println!(
                "paid {amount} to {name}'s till (account {till}) with {RENEW_TOPIC} #{} (fee {}, transaction {}); the concierge issues your window",
                result["publication"]["sequence"].as_str().unwrap_or("?"),
                result["fee"].as_str().unwrap_or("?"),
                result["receipt"]["transactionId"].as_str().unwrap_or("?")
            );
            Ok(())
        }
        "topup" => {
            let name = text(args.required("room")?, "room")?;
            let amount = text(args.required("amount")?, "amount")?;
            let account = opt(&mut args, "account")?;
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            let runner = current.need("runner")?.to_owned();
            let account = my_account(&root, &ws, account.as_deref())?;
            let result = crate::fleet::pay_turn(&root, &account, &runner, &amount, None, None)?;
            println!(
                "topped up {name}'s runner account {runner} by {amount} (fee {}, transaction {})",
                result["fee"].as_str().unwrap_or("?"),
                result["receipt"]["transactionId"].as_str().unwrap_or("?")
            );
            Ok(())
        }
        "renew" => {
            let name = text(args.required("room")?, "room")?;
            let subject = text(args.required("subject")?, "subject")?;
            let until = opt(&mut args, "not-after")?;
            let for_heights = opt(&mut args, "for")?;
            let id = opt(&mut args, "proposal-id")?;
            let outbox = opt(&mut args, "outbox")?.map(PathBuf::from);
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            let not_after = match (until, for_heights) {
                (Some(until), None) => until,
                (None, Some(heights)) => (current.height + number(&heights, "--for")?).to_string(),
                (None, None) => (current.height + number(current.need("period")?, "period")?).to_string(),
                _ => return Err("renew takes --not-after H or --for N, not both".into()),
            };
            let id = id.unwrap_or_else(|| format!("renew-{subject}-{not_after}"));
            print_json(&renew(&root, &ws, &name, &subject, &not_after, &id, MEMBER_VERBS, outbox.as_deref())?)
        }
        "status" => {
            let name = text(args.required("room")?, "room")?;
            let inbox = opt(&mut args, "inbox")?.map(PathBuf::from);
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            let adopted = match &inbox {
                Some(inbox) => adopt_window(&root, &ws, &name, &current, inbox)?,
                None => None,
            };
            println!("room {name} ({}) at height {}", current.target, current.height);
            if let Some((capability, after)) = &adopted {
                println!("  adopted a member window from the inbox: capability {capability}, notAfter {after}");
            }
            match window(&root, &name)? {
                None => println!("  my window: none (guest; `pay {name} week` buys one)"),
                Some((capability, after)) => {
                    let after_n = number(&after, "notAfter")?;
                    if after_n >= current.height {
                        println!(
                            "  my window: member until height {after} ({} heights left; capability {capability})",
                            after_n - current.height
                        );
                    } else {
                        println!(
                            "  my window: ENDED at height {after} ({} heights ago; capability {capability}); `pay {name} week` renews",
                            current.height - after_n
                        );
                    }
                }
            }
            match current.get("week") {
                Some(week) => println!(
                    "  tariff: week {week} credit for {} heights",
                    current.get("period").unwrap_or("?")
                ),
                None => println!("  tariff: none set"),
            }
            if let Some(till) = current.get("till") {
                match crate::fleet::account_balance(&root, &format!("{name}-till")) {
                    Ok((balance, asset, _, _)) => println!("  till: account {till}, balance {balance} (asset {asset})"),
                    Err(_) => println!("  till: account {till} (its balance is the room's to read)"),
                }
            }
            if let Some(runner) = current.get("runner") {
                println!("  runner account: {runner}; concierge {}", current.get("concierge").unwrap_or("-"));
            }
            Ok(())
        }
        "ledger" => {
            let account = text(args.required("account")?, "account reference")?;
            let since = opt(&mut args, "since")?.unwrap_or_else(|| "0".into());
            let topic = opt(&mut args, "topic")?.unwrap_or_else(|| RENEW_TOPIC.into());
            args.finish()?;
            print_json(&crate::fleet::incoming(&root, &account, &topic, &since, "64")?)
        }
        "install" => {
            let name = text(args.required("room")?, "room")?;
            let concierge = text(args.required("concierge")?, "concierge")?;
            let period = opt(&mut args, "period")?.unwrap_or_else(|| DEFAULT_PERIOD.into());
            let fund = opt(&mut args, "fund")?.unwrap_or_else(|| "1".into());
            let outbox = PathBuf::from(text(args.required("outbox")?, "outbox")?);
            let program = PathBuf::from(text(args.required("program")?, "program")?);
            args.finish()?;
            install(&root, &ws, &name, &concierge, &period, &fund, &outbox, &program)
        }
        "adopt" => {
            let inbox = PathBuf::from(text(args.required("inbox")?, "inbox")?);
            args.finish()?;
            adopt(&root, &ws, &inbox)
        }
        _ => Err("credit action must be balance, room, tariff, pay, topup, renew, status, ledger, install or adopt".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tariff_fields_are_distinct_keys() {
        let mut keys: Vec<_> = TARIFF_FIELDS.iter().map(|(_, key)| *key).collect();
        keys.sort();
        keys.dedup();
        assert_eq!(keys.len(), TARIFF_FIELDS.len());
        assert_eq!(field_key("week").unwrap(), "1");
        assert!(field_key("weekly").is_err());
    }

    #[test]
    fn members_never_mutate_or_delegate() {
        assert!(!MEMBER_VERBS.contains(&"mutate"));
        assert!(!MEMBER_VERBS.contains(&"delegate"));
        assert!(MEMBER_VERBS.contains(&"observe"));
        assert!(CONCIERGE_VERBS.iter().all(|v| MEMBER_VERBS.contains(v) || *v == "delegate"));
    }

    #[test]
    fn a_founder_sets_prices_not_accounts() {
        for field in ["till", "runner", "concierge"] {
            assert!(!SETTABLE.contains(&field));
        }
        for field in SETTABLE {
            assert!(field_key(field).is_ok());
        }
    }

    #[test]
    fn decimals_are_canonical() {
        assert!(decimal("0", "x").is_ok());
        assert!(decimal("100", "x").is_ok());
        assert!(decimal("010", "x").is_err());
        assert!(decimal("", "x").is_err());
        assert!(decimal("-1", "x").is_err());
    }
}
