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

pub(crate) use crate::room_schema::{ROOM_FIELDS_START,TARIFF_FIELDS};
/// Fresh rooms declare one central schema, including names, paid-open and assignment.
pub(crate) fn room_declared_fields() -> String { crate::room_schema::declared_fields() }

/// The topic a Hermes turn's payment publishes on Hermes's account.
pub(crate) const HERMES_TOPIC: &str = "hermes";

/// Fields a founder sets by `tariff ROOM set FIELD N`; the rest are written
/// by `room concierge` (install) and name accounts and subjects.
const SETTABLE: &[&str] = &["week", "birth", "hermes/turn", "period", "open"];

/// The topic a concierge's refund publishes on the till.
pub(crate) const REFUND_TOPIC: &str = "refund";

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
    Ok(Room {
        target: workspace::member(&reference, "target")?.to_owned(),
        height,
        root: cell.get("root").and_then(Value::as_str).unwrap_or("").to_owned(),
        fields: tariff_fields(cell),
    })
}

fn tariff_fields(cell: &Value) -> BTreeMap<&'static str, String> {
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
    fields
}

/// The room's tariff as it stood at absolute height `at`: one signed `at`
/// read of `R` (Host K-HISTORY-READ). A payment quotes the height it read the
/// price at; the concierge decides against this read, never the current one.
pub(crate) fn room_at(root: &Path, ws: &Value, name: &str, at: &str) -> Result<Room> {
    decimal(at, "--at")?;
    let reference = workspace::reference(root, &read_ref(root, name))?;
    let view = workspace::signed_view_at(root, ws, &reference, at)?;
    if view.get("state").and_then(Value::as_str) != Some("live") {
        return Err(format!("room {name} was not live at height {at}"));
    }
    let cell = view
        .get("resource")
        .and_then(|resource| resource.get("cell"))
        .ok_or("signed at view lacks the room cell")?;
    Ok(Room {
        target: workspace::member(&reference, "target")?.to_owned(),
        height: number(at, "--at")?,
        root: cell.get("root").and_then(Value::as_str).unwrap_or("").to_owned(),
        fields: tariff_fields(cell),
    })
}

/// The memo a week's payment carries on `renew`: the room, the price it read
/// and the height it read it at, signed with the payment.
pub(crate) fn renew_memo(room: &str, week: &str, height: u128) -> String {
    format!("room {room} week {week} at {height}")
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
pub(crate) fn set_fields(root: &Path, ws: &Value, name: &str, room: &Room, values: &[(&str, String)]) -> Result<PathBuf> {
    let id = format!("tariff-{}-{}", room.height, workspace::random_nonce()?);
    set_fields_exact(root,ws,name,room,values,&id)
}
/// Persist one assignment intent before sending; retries recover its original call.
pub(crate) fn set_fields_exact(root:&Path,ws:&Value,name:&str,room:&Room,values:&[(&str,String)],id:&str)->Result<PathBuf> {
    let retained=root.join("sources").join(format!("credit-{id}.request.json"));
    if retained.exists() {
        let request=workspace::bounded_json(&retained)?;
        let target=&request["targets"][0];
        let actions=target["payload"]["actions"].as_array().ok_or("retained assignment actions absent")?;
        if target["name"]!=name || actions.len()!=values.len() {return Err("retained assignment target differs".into())}
        for (field,value)in values {
            let key=field_key(field)?;
            if actions.iter().filter(|a|a["key"]["field"]==key && a["value"]==*value).count()!=1 {return Err("retained assignment value differs".into())}
        }
        return propose_and_submit(root,ws,id,&request)
    }
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
    propose_and_submit(root, ws, id, &request)
}

/// The permit-all predicate an account birth names (accounts are governed by
/// their capabilities and the Book, not a field law).
pub(crate) fn write_permit(path: &Path) -> Result<()> {
    write_json(path, &json!({"type":"all","predicates":[]}))
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
                && !name.ends_with("-hermes")
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
    // The concierge reads the till's ledger and refunds a payment it will not
    // honour from the till itself (`transfer`).
    let reads = format!("{name}-till-concierge");
    let request = json!({"type":"minidregg-workspace-proposal-v1","action":"delegate",
        "name":till_name,"recipient":concierge,"verbs":["observe","transfer"],"maxCost":MAX_COST});
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
        "program":"for each renew entry on the till's incoming ledger: the entry's memo names the room, the week price and the height H it was read at; the entry must land within 64 heights of H; the tariff is read AT H; when the asset is the pinned credit asset, the quoted price is the tariff's week at H, the amount is at least that week, and the signer is a subject the room admits (a standing grant under the room, or tariff.open = 1 at H), issue `member` under the room with notAfter = max(entry.height, the signer's current notAfter) + tariff.period at H; otherwise refund the amount from the till to the payer on topic refund, journaled with the reason; when tariff.week = 0 every filed request from a standing room member issues height + period"});
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
            let at = opt(&mut args, "at")?;
            args.finish()?;
            match at {
                None => print_json(&room(&root, &ws, &name)?.json()),
                Some(at) => print_json(&room_at(&root, &ws, &name, &at)?.json()),
            }
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
            // The price and the height it was read at travel with the payment:
            // the concierge decides against the tariff at that height.
            let payload = renew_memo(&current.target, &week, current.height);
            let result = crate::fleet::pay_turn(
                &root,
                &account,
                &till,
                &amount,
                None,
                Some((RENEW_TOPIC, payload.as_bytes())),
            )?;
            println!(
                "paid {amount} to {name}'s till (account {till}) with {RENEW_TOPIC} #{} at the price {week} read at height {} (fee {}, transaction {}); the concierge issues your window or refunds it",
                result["publication"]["sequence"].as_str().unwrap_or("?"),
                current.height,
                result["fee"].as_str().unwrap_or("?"),
                result["receipt"]["transactionId"].as_str().unwrap_or("?")
            );
            Ok(())
        }
        "topup" => {
            let name = text(args.required("room")?, "room")?;
            let amount = text(args.required("amount")?, "amount")?;
            let account = opt(&mut args, "account")?;
            let to = opt(&mut args, "to")?;
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            // Hermes's budget when the room has a Hermes, else the
            // concierge's runner account; `--to` says which.
            let hermes = current.get("hermes/account").filter(|a| *a != "0").map(str::to_owned);
            let (whose, destination) = match (to.as_deref(), hermes) {
                (Some("hermes") | None, Some(hermes)) => ("Hermes's budget account", hermes),
                (Some("hermes"), None) => return Err(format!("{name} has no Hermes (its founder summons one)")),
                (Some("concierge") | None, _) => ("runner account", current.need("runner")?.to_owned()),
                (Some(other), _) => return Err(format!("topup --to hermes|concierge, not {other}")),
            };
            let account = my_account(&root, &ws, account.as_deref())?;
            let result = crate::fleet::pay_turn(&root, &account, &destination, &amount, None, None)?;
            println!(
                "topped up {name}'s {whose} {destination} by {amount} (fee {}, transaction {})",
                result["fee"].as_str().unwrap_or("?"),
                result["receipt"]["transactionId"].as_str().unwrap_or("?")
            );
            Ok(())
        }
        // One Hermes turn's payment (PLACE §2.10 "every Hermes turn debits
        // tariff.hermes/turn"): one fleet turn from Hermes's account to the
        // room's till, `hermes/turn` credit plus the fleet fee, publishing
        // MEMO on Hermes's `hermes` topic. An account that cannot cover it is
        // refused at plan (`bookRefused`), which is what stops Hermes.
        "turn" => {
            let name = text(args.required("room")?, "room")?;
            let account = text(args.required("account")?, "account")?;
            let memo = text(args.required("memo")?, "memo")?;
            args.finish()?;
            let current = room(&root, &ws, &name)?;
            let price = current.get("hermes/turn").unwrap_or("0").to_owned();
            if price == "0" {
                print_json(&json!({"type":"minidregg-hermes-turn-v1","room":name,"price":"0","paid":false,
                    "note":"this room does not charge Hermes's turns (tariff hermes/turn is 0)"}))?;
                return Ok(());
            }
            let till = current.need("till")?.to_owned();
            let result = crate::fleet::pay_turn(&root, &account, &till, &price, None, Some((HERMES_TOPIC, memo.as_bytes())))?;
            print_json(&json!({"type":"minidregg-hermes-turn-v1","room":name,"price":price,"paid":true,
                "till":till,"fee":result["fee"],"transaction":result["receipt"]["transactionId"],
                "sequence":result["publication"]["sequence"],"memo":memo}))
        }
        // Hermes returns what is left of a budget account to `--to` (the
        // founder's account `dismiss` named): the balance less the fleet fee,
        // one signed transfer. Nothing is returned when the balance does not
        // cover the fee.
        "return" => {
            let account = text(args.required("account")?, "account")?;
            let to = text(args.required("to")?, "to")?;
            args.finish()?;
            decimal(&to, "return account")?;
            let (balance, asset, height, target) = crate::fleet::account_balance(&root, &account)?;
            let fee = crate::fleet::tariff_base(&root)?;
            let (balance_n, fee_n) = (number(&balance, "balance")?, number(&fee, "fee")?);
            if balance_n <= fee_n {
                return print_json(&json!({"type":"minidregg-hermes-return-v1","account":target,"balance":balance,
                    "asset":asset,"height":height,"returned":"0","note":"the balance does not cover the fee"}));
            }
            let amount = (balance_n - fee_n).to_string();
            let result = crate::fleet::pay_turn(&root, &account, &to, &amount, None, None)?;
            print_json(&json!({"type":"minidregg-hermes-return-v1","account":target,"balance":balance,
                "asset":asset,"height":height,"returned":amount,"fee":result["fee"],"to":to,
                "transaction":result["receipt"]["transactionId"]}))
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
            if let Some(hermes) = current.get("hermes").filter(|h| *h != "0") {
                let account = current.get("hermes/account").unwrap_or("-");
                let price = current.get("hermes/turn").unwrap_or("0");
                match crate::fleet::account_balance(&root, &format!("{name}-hermes")) {
                    Ok((balance, _, _, _)) => println!("  hermes: {hermes}, budget account {account}, balance {balance}, {price} a turn"),
                    Err(_) => println!("  hermes: {hermes}, budget account {account}, {price} a turn"),
                }
            }
            Ok(())
        }
        // The concierge's refund: AMOUNT of ASSET from the till reference
        // ACCOUNT to account TO, publishing MEMO on the till's `refund` topic.
        "refund" => {
            let account = text(args.required("account")?, "account reference")?;
            let to = text(args.required("to")?, "to")?;
            let amount = text(args.required("amount")?, "amount")?;
            let asset = opt(&mut args, "asset")?;
            let memo = text(args.required("memo")?, "memo")?;
            args.finish()?;
            decimal(&to, "refund account")?;
            decimal(&amount, "refund amount")?;
            let result = crate::fleet::pay_turn(&root, &account, &to, &amount, asset.as_deref(),
                Some((REFUND_TOPIC, memo.as_bytes())))?;
            print_json(&json!({"type":"minidregg-refund-v1","from":account,"to":to,"amount":amount,
                "memo":memo,"fee":result["fee"],"transaction":result["receipt"]["transactionId"]}))
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
        _ => Err("credit action must be balance, room, tariff, pay, topup, turn, return, refund, renew, status, ledger, install or adopt".into()),
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
        assert_eq!(field_key("week").unwrap(), "1001");
        // Every room field sits at or above the roster's ceiling.
        for (_, key) in TARIFF_FIELDS {
            assert!(key.parse::<u64>().unwrap() >= ROOM_FIELDS_START);
        }
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
        for field in ["till", "runner", "concierge", "hermes", "hermes/account"] {
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
