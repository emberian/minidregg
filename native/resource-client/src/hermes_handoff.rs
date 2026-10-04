//! Authenticated, immutable summon handoff. Files are hints; native signed
//! observations and the original accepted call qualify delivery, never paths.
use crate::{workspace, Args, Result};
use ed25519_dalek::{Signature, Signer, SigningKey, VerifyingKey};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::os::unix::fs::OpenOptionsExt;
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
};
const DOMAIN: &[u8] = b"mini-hermes-handoff-v1\0";
const LIMIT: usize = 4 * 1024 * 1024;
pub(crate) const ASSIGNMENT_FIELD: &str = crate::room_schema::ASSIGNMENT_FIELD;
fn text<'a>(v: &'a Value, k: &str) -> Result<&'a str> {
    v[k].as_str().ok_or_else(|| format!("handoff {k} absent"))
}
fn fields(v: &Value, names: &[&str]) -> Result<()> {
    let o = v.as_object().ok_or("handoff object required")?;
    if o.len() != names.len() || names.iter().any(|k| !o.contains_key(*k)) {
        return Err("handoff fields differ".into());
    }
    Ok(())
}
fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}
fn unhex(s: &str) -> Result<Vec<u8>> {
    if s.len() % 2 != 0
        || s.len() > LIMIT * 2
        || !s
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err("handoff hex invalid".into());
    }
    crate::decode_hex(s)
}
fn digest(b: &[u8]) -> String {
    hex(&Sha256::digest(b))
}
fn name(s: &str) -> Result<()> {
    if s.is_empty()
        || s.len() > 180
        || s.starts_with('.')
        || !s
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
    {
        return Err("handoff file name invalid".into());
    }
    Ok(())
}
fn read(p: &Path) -> Result<Vec<u8>> {
    let mut f = fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_NONBLOCK)
        .open(p)
        .map_err(|e| e.to_string())?;
    let m = f.metadata().map_err(|e| e.to_string())?;
    if !m.is_file() || m.len() > LIMIT as u64 {
        return Err("handoff requires bounded regular file".into());
    }
    let mut b = Vec::new();
    f.by_ref()
        .take((LIMIT + 1) as u64)
        .read_to_end(&mut b)
        .map_err(|e| e.to_string())?;
    if b.len() > LIMIT {
        return Err("handoff too large".into());
    }
    Ok(b)
}
pub(crate) fn json_file(p: &Path) -> Result<Value> {
    serde_json::from_slice(&read(p)?).map_err(|e| e.to_string())
}
fn world(ws: &Value) -> Result<Value> {
    let c = json_file(&workspace::member_path(ws, "config")?)?;
    let natural = |k: &str| -> Result<String> {
        let v = c.get(k).ok_or_else(|| format!("{k} absent"))?;
        let s = v
            .as_str()
            .map(str::to_owned)
            .unwrap_or_else(|| v.to_string());
        source_decimal(&s, k)?;
        Ok(s)
    };
    Ok(json!({"domain":natural("domain")?,"expectedSeed":natural("expectedSeed")?}))
}
fn source_decimal(value: &str, label: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 80
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|b| b.is_ascii_digit())
    {
        return Err(format!("{label} must be a canonical bounded decimal"));
    }
    Ok(())
}
fn message(bytes: &[u8]) -> Vec<u8> {
    [DOMAIN, bytes].concat()
}
fn decode(bundle: &Value) -> Result<(Value, String)> {
    fields(bundle, &["type", "payloadHex", "publicKey", "signature"])?;
    if bundle["type"] != "mini-hermes-handoff-v1" {
        return Err("unknown handoff version".into());
    }
    let bytes = unhex(text(bundle, "payloadHex")?)?;
    let public: [u8; 32] = unhex(text(bundle, "publicKey")?)?
        .try_into()
        .map_err(|_| "handoff public key width")?;
    let signature = Signature::from_slice(&unhex(text(bundle, "signature")?)?)
        .map_err(|_| "handoff signature width")?;
    VerifyingKey::from_bytes(&public)
        .map_err(|_| "handoff public key invalid")?
        .verify_strict(&message(&bytes), &signature)
        .map_err(|_| "handoff signature refused")?;
    let payload: Value = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    fields(
        &payload,
        &[
            "type",
            "world",
            "recipient",
            "task",
            "founder",
            "room",
            "roomCell",
            "assignment",
            "origin",
            "files",
        ],
    )?;
    if payload["type"] != "mini-hermes-summon-bundle-v1"
        && payload["type"] != "mini-hermes-dismiss-bundle-v1"
    {
        return Err("handoff payload version refused".into());
    }
    for k in ["recipient", "task", "founder", "roomCell", "assignment"] {
        crate::chat::decimal(text(&payload, k)?, k)?;
    }
    if payload["assignment"] == "0" {
        return Err("handoff assignment must be nonzero".into());
    }
    name(text(&payload, "room")?)?;
    let files = payload["files"].as_object().ok_or("handoff files absent")?;
    if files.len() < 3 || files.len() > 128 {
        return Err("handoff file count invalid".into());
    }
    for (n, b) in files {
        name(n)?;
        unhex(b.as_str().ok_or("handoff file encoding absent")?)?;
    }
    validate_files(&payload)?;
    Ok((payload, digest(&bytes)))
}
fn file_name(n: &str) -> String {
    format!("{}.json", workspace::ref_file(n))
}
fn file(p: &Value, n: &str) -> Result<Value> {
    serde_json::from_slice(&unhex(
        p["files"][n]
            .as_str()
            .ok_or_else(|| format!("handoff missing {n}"))?,
    )?)
    .map_err(|e| e.to_string())
}
fn validate_files(p: &Value) -> Result<()> {
    let room = text(p, "room")?;
    let m = file(p, &format!("summon-{room}.json"))?;
    if m["type"] != "mini-hermes-summon-v1"
        || m["room"] != p["room"]
        || m["hermes"] != p["recipient"]
        || m["founder"] != p["founder"]
        || m["assignment"] != p["assignment"]
        || m["roomCell"] != p["roomCell"]
        || m["task"] != p["task"]
    {
        return Err("signed manifest identity differs".into());
    }
    let invite = file(p, &format!("{room}-invite.json"))?;
    if invite["type"] != "minidregg-delegated-reference-v1"
        || invite["recipient"] != p["recipient"]
        || invite["target"] != m["roomCell"]
        || invite["kind"] != "object"
        || invite["room"] != true
    {
        return Err("signed invitation differs".into());
    }
    let account = file(p, &file_name(text(&m["account"], "name")?))?;
    if account["type"] != "minidregg-fleet-account-handoff-v1"
        || account["owner"] != p["recipient"]
        || account["target"] != m["account"]["target"]
    {
        return Err("signed account differs".into());
    }
    let mut names = vec![
        format!("summon-{room}.json"),
        format!("{room}-invite.json"),
        file_name(text(&m["account"], "name")?),
    ];
    for doc in m["docs"].as_array().ok_or("manifest docs absent")? {
        let n = file_name(text(doc, "name")?);
        let d = file(p, &n)?;
        if d["type"] != "minidregg-delegated-reference-v1"
            || d["recipient"] != p["recipient"]
            || d["target"] != doc["target"]
            || d["kind"] != "object"
        {
            return Err("signed document grant differs".into());
        }
        names.push(n);
    }
    names.sort();
    names.dedup();
    if names.len() != p["files"].as_object().unwrap().len() {
        return Err("handoff contains unrelated files".into());
    }
    Ok(())
}
/// Called by the actual summon producer after its exact source transition.
pub(crate) fn seal(
    root: &Path,
    ws: &Value,
    out: &Path,
    manifest: &Value,
    origin: &Path,
    task: &str,
) -> Result<()> {
    let room = text(manifest, "room")?;
    name(room)?;
    let mut names = vec![
        format!("summon-{room}.json"),
        format!("{room}-invite.json"),
        file_name(text(&manifest["account"], "name")?),
    ];
    for d in manifest["docs"].as_array().ok_or("docs absent")? {
        names.push(file_name(text(d, "name")?));
    }
    let mut files = serde_json::Map::new();
    for n in names {
        name(&n)?;
        files.insert(n.clone(), json!(hex(&read(&out.join(&n))?)));
    }
    let receipt =
        workspace::accepted_outcome(origin)?.ok_or("summon source operation is not accepted")?;
    let payload = json!({"type":"mini-hermes-summon-bundle-v1","world":world(ws)?,"recipient":manifest["hermes"],"task":task,"founder":workspace::member(ws,"subject")?,"room":room,"roomCell":manifest["roomCell"],"assignment":manifest["assignment"],"origin":{"callHex":hex(&read(&origin.join("call.bin"))?),"planHex":hex(&read(&origin.join("plan.bin"))?),"signaturesHex":hex(&read(&origin.join("transaction-signatures.bin"))?),"command":json_file(&origin.join("intent.json"))?["purpose"]["draft"]["command"],"receipt":receipt},"files":files});
    let bytes = serde_json::to_vec(&payload).map_err(|e| e.to_string())?;
    let mut seed: [u8; 32] =
        crate::agent_reserve::private_bytes(&workspace::member_path(ws, "key")?, 32)?
            .try_into()
            .map_err(|_| "signing key width")?;
    let key = SigningKey::from_bytes(&seed);
    seed.fill(0);
    let bundle = json!({"type":"mini-hermes-handoff-v1","payloadHex":hex(&bytes),"publicKey":hex(key.verifying_key().as_bytes()),"signature":hex(&key.sign(&message(&bytes)).to_bytes())});
    decode(&bundle)?;
    let target = out.join("handoff.json");
    // A retry does not mint another origin or delivery job. A different key may
    // re-sign the same immutable payload after rotation; its identity is unchanged.
    if target.exists() {
        let (prior, _) = decode(&json_file(&target)?)?;
        if prior != payload {
            return Err("retained summon payload differs; refusing overwrite".into());
        }
    }
    crate::chat::put_json(&target, &bundle)?;
    let _ = root;
    Ok(())
}
fn reference(v: &Value) -> Result<Value> {
    Ok(
        json!({"kind":text(v,"kind")?,"target":text(v,"target")?,"observeCapability":v.get("capability").or_else(||v.get("observeCapability")).ok_or("handoff reference has no observe capability")?}),
    )
}
fn consistent(previous: &mut Option<Value>, challenge: &Value) -> Result<()> {
    let image = json!({"worldRoot":challenge["worldRoot"],"authorityRoot":challenge["authorityRoot"],"height":challenge["height"],"domain":challenge["domain"]});
    for k in ["worldRoot", "authorityRoot", "height", "domain"] {
        if image[k].is_null() {
            return Err("source challenge missing image identity".into());
        }
    }
    if previous
        .as_ref()
        .is_some_and(|p| p["domain"] != image["domain"])
    {
        return Err("source domain changed during handoff verification".into());
    }
    *previous = Some(image);
    Ok(())
}
/// The admitted capability query proves current observe access to this exact
/// account. Its head describes custody and verbs, not admission of a transfer.
fn account_evidence(
    recipient: &Value,
    bound_world: &Value,
    account: &Value,
    view: &Value,
    challenge: &Value,
    challenge_bytes: &[u8],
    signed_bytes: &[u8],
) -> Result<Value> {
    let observe = text(account, "observeCapability")?;
    let operation = text(account, "operationCapability")?;
    let target = text(account, "target")?;
    let head = &view["head"];
    let intent = &challenge["intent"];
    if account["kind"] != "account"
        || view["type"] != "capability"
        || view["kind"] != "account"
        || head["id"] != observe
        || head["holder"]["type"] != "subject"
        || head["holder"]["subject"] != *recipient
        || intent["subject"] != *recipient
        || intent["purpose"]
            != json!({"type":"query","kind":"account","target":target,"view":"capability"})
        || intent["grants"] != json!([{"kind":"account","target":target,"capability":observe}])
        || challenge["domain"] != bound_world["domain"]
    {
        return Err("native account capability differs from handoff recipient/target/grant".into());
    }
    for key in ["height", "worldRoot", "authorityRoot"] {
        source_decimal(text(challenge, key)?, "account observation identity")?;
    }
    let verbs = head["verbs"]
        .as_array()
        .ok_or("account capability verbs absent")?;
    if !verbs.iter().any(|v| v == "observe") {
        return Err("native account capability lacks observe verb".into());
    }
    let operation_verified = operation == observe;
    Ok(
        json!({"type":"mini-hermes-account-custody-v1","target":target,
        "recipient":recipient,"observedCapability":observe,"operationCapability":operation,
        "operationVerified":operation_verified,
        "transferGranted":operation_verified && verbs.iter().any(|v| v == "transfer"),
        "world":bound_world,"head":head,"grant":intent["grants"][0],
        "observation":{"height":challenge["height"],"worldRoot":challenge["worldRoot"],
            "authorityRoot":challenge["authorityRoot"],
            "challengeSha256":digest(challenge_bytes),"signedSha256":digest(signed_bytes)}}),
    )
}
fn verify(
    root: &Path,
    bundle: &Value,
    task: &str,
    room: &str,
    first_delivery: bool,
) -> Result<Value> {
    let (p, id) = decode(bundle)?;
    let ws = workspace::load(root)?;
    if p["task"] != task
        || p["room"] != room
        || p["recipient"] != workspace::member(&ws, "subject")?
        || p["world"] != world(&ws)?
    {
        return Err("handoff recipient/task/room/world differs from registered workspace".into());
    }
    let host = workspace::workspace_host(&ws)?;
    let config = workspace::member_path(&ws, "config")?;
    let socket = crate::SOCKET
        .get()
        .ok_or("recipient workspace socket absent")?;
    let reply = crate::session_invoke(
        &host,
        socket,
        &config,
        144,
        &serde_json::to_vec(&json!({"subject":p["founder"],"publicKey":bundle["publicKey"]}))
            .unwrap(),
    )?;
    let [144, body @ ..] = reply.as_slice() else {
        return Err("native founder key status refused".into());
    };
    let owner: Value = serde_json::from_slice(body).map_err(|e| e.to_string())?;
    if owner["type"] != "subject-key-status-v1"
        || owner["subject"] != p["founder"]
        || (first_delivery && (owner["isCurrent"] != true || owner["currentRevoked"] != false))
    {
        return Err("founder signing key is not current".into());
    }
    let (attempt, _) = workspace::new_attempt(root)?;
    workspace::make_private_dir(&attempt)?;
    let call = attempt.join("origin-call.bin");
    workspace::private_file(&call, &unhex(text(&p["origin"], "callHex")?)?)?;
    let receipt = &p["origin"]["receipt"];
    crate::historical_call_receipt::lookup_verified(
        &host,
        &config,
        socket,
        &call,
        [
            text(receipt, "transactionId")?,
            text(receipt, "eventId")?,
            text(receipt, "acceptedCount")?,
            text(receipt, "worldRoot")?,
        ],
        &attempt.join("origin-lookup"),
    )?;
    let plan = attempt.join("origin-plan.bin");
    let signatures = attempt.join("origin-signatures.bin");
    let assembled = attempt.join("assembled.bin");
    workspace::private_file(&plan, &unhex(text(&p["origin"], "planHex")?)?)?;
    workspace::private_file(&signatures, &unhex(text(&p["origin"], "signaturesHex")?)?)?;
    crate::host_files(
        &host,
        &config,
        &[Path::new("assemble"), &plan, &signatures, &assembled],
    )?;
    if read(&assembled)? != read(&call)? {
        return Err("origin plan/signatures do not reconstruct accepted call".into());
    }
    let presentation = crate::inspect(&host, &config, "plan", &plan, &attempt.join("plan.json"))?;
    let source_config = json_file(&config)?;
    let genesis = source_config["genesisHeight"]
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| source_config["genesisHeight"].to_string())
        .parse::<u128>()
        .map_err(|_| "source genesis height exceeds resident profile")?;
    let count = text(receipt, "acceptedCount")?
        .parse::<u128>()
        .map_err(|_| "source accepted count exceeds resident profile")?;
    let accepted_height = genesis
        .checked_add(count)
        .and_then(|h| h.checked_sub(1))
        .ok_or("source activation height invalid")?
        .to_string();
    let command = &p["origin"]["command"];
    validate_origin_command(&p, command)?;
    let command_json = attempt.join("command.json");
    let command_bin = attempt.join("command.bin");
    workspace::private_file(
        &command_json,
        &serde_json::to_vec(command).map_err(|e| e.to_string())?,
    )?;
    crate::author(
        &host,
        &config,
        "resource".as_ref(),
        &command_json,
        &command_bin,
    )?;
    if presentation["finalizedDraft"]["type"] != "invoke"
        || presentation["finalizedDraft"]["command"] != hex(&read(&command_bin)?)
        || presentation["domain"] != p["world"]["domain"]
    {
        return Err("accepted summon source command differs from bound origin".into());
    }
    if p["type"] == "mini-hermes-dismiss-bundle-v1" {
        return Ok(
            json!({"type":"mini-hermes-dismiss-verified-v1","id":id,"task":task,"room":room,"roomCell":p["roomCell"],"assignment":p["assignment"],"origin":receipt,"world":p["world"]}),
        );
    }
    let manifest = file(&p, &format!("summon-{room}.json"))?;
    let invitation = file(&p, &format!("{room}-invite.json"))?;
    let mut image = None;
    let (view, c, _) = workspace::signed_view(root, &ws, &reference(&invitation)?, "resource")?;
    consistent(&mut image, &c)?;
    let roster = crate::chat::roster_of(&view);
    if roster.founder.as_deref() != p["founder"].as_str()
        || !roster.members.iter().any(|(subject, stream)| {
            Some(subject.as_str()) == p["recipient"].as_str()
                && Some(stream.as_str()) == manifest["stream"].as_str()
        })
    {
        return Err("current native room founder/recipient stream differs".into());
    }
    let field = |n: &str| {
        view.pointer("/cell/entries")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .find(|e| e.pointer("/key/field").and_then(Value::as_str) == Some(n))
            .and_then(|e| e["value"].as_str())
    };
    if field("1008") != p["recipient"].as_str()
        || field("1009") != manifest["account"]["target"].as_str()
        || field(ASSIGNMENT_FIELD) != p["assignment"].as_str()
    {
        return Err("current native summon assignment differs (dismissed or superseded)".into());
    }
    let account_name = file_name(text(&manifest["account"], "name")?);
    let mut custody = None;
    for (n, _) in p["files"].as_object().unwrap() {
        if n.starts_with("summon-") {
            continue;
        }
        let v = file(&p, n)?;
        let (capability, c, signed) =
            workspace::signed_view(root, &ws, &reference(&v)?, "capability")?;
        consistent(&mut image, &c)?;
        if n == &account_name {
            custody = Some(account_evidence(
                &p["recipient"],
                &p["world"],
                &v,
                &capability,
                &c,
                &read(&signed.with_file_name("challenge.bin"))?,
                &read(&signed)?,
            )?);
        }
    }
    let program = json!({"kind":"object","target":manifest["program"]["target"],"observeCapability":invitation["capability"]});
    let (_, c, _) = workspace::signed_view(root, &ws, &program, "resource")?;
    consistent(&mut image, &c)?;
    // Independent native reads tolerate unrelated world writes. The ready gate
    // is setup custody; every actual effect still re-admits under source grants.
    // Reobserve relevant assignment fields last to detect dismissal/replacement.
    let (final_view, c, _) =
        workspace::signed_view(root, &ws, &reference(&invitation)?, "resource")?;
    consistent(&mut image, &c)?;
    for n in ["1008", "1009", ASSIGNMENT_FIELD] {
        let entries = final_view
            .pointer("/cell/entries")
            .and_then(Value::as_array)
            .ok_or("final room entries absent")?;
        let values: Vec<_> = entries
            .iter()
            .filter(|e| e.pointer("/key/field").and_then(Value::as_str) == Some(n))
            .collect();
        if values.len() != 1 || values[0]["value"].as_str() != field(n) {
            return Err("room assignment changed during verification".into());
        }
    }

    Ok(
        json!({"type":"mini-hermes-handoff-verified-v1","id":id,"task":task,"recipient":p["recipient"],"room":room,"roomCell":p["roomCell"],"assignment":p["assignment"],"founder":p["founder"],"keyEpoch":owner["keyEpoch"],"world":p["world"],"originHeight":presentation["height"],"acceptedHeight":accepted_height,"acceptedCount":receipt["acceptedCount"],"origin":receipt,"image":image,"files":p["files"],"accountEvidence":custody.ok_or("native account custody absent")?}),
    )
}
/// The accepted call must be exactly the founder's assignment transition.
fn validate_origin_command(p: &Value, command: &Value) -> Result<()> {
    fields(command, &["subject", "nonce", "targets"])?;
    if command["subject"] != p["founder"] {
        return Err("summon origin issuer differs".into());
    }
    let targets = command["targets"]
        .as_array()
        .ok_or("origin targets absent")?;
    if targets.len() != 1 {
        return Err("summon origin must have exactly one room target".into());
    }
    let t = &targets[0];
    if t["kind"] != "object" || t["target"] != p["roomCell"] || t["payload"]["type"] != "scalar" {
        return Err("summon origin room target differs".into());
    }
    let m = file(p, &format!("summon-{}.json", text(p, "room")?))?;
    let actions = t["payload"]["actions"]
        .as_array()
        .ok_or("origin actions absent")?;
    if actions.len() != 3 {
        return Err("summon origin requires exactly subject/account/assignment actions".into());
    }
    for (key, value) in [
        ("1008", &p["recipient"]),
        ("1009", &m["account"]["target"]),
        (ASSIGNMENT_FIELD, &p["assignment"]),
    ] {
        let matches: Vec<_> = actions
            .iter()
            .filter(|a| a["key"]["field"] == key)
            .collect();
        if matches.len() != 1 {
            return Err("summon origin duplicate or missing field".into());
        }
        let a = matches[0];
        let dismiss = p["type"] == "mini-hermes-dismiss-bundle-v1";
        if a["key"]["resource"] != p["roomCell"]
            || if dismiss {
                a["type"] != "write" || a["value"] != "0" || a["expected"] != *value
            } else {
                !matches!(a["type"].as_str(), Some("create" | "write")) || a["value"] != *value
            }
        {
            return Err("assignment origin field value differs".into());
        }
    }
    Ok(())
}
fn ready_bundle(inbox: &Path) -> Result<Value> {
    let ready = json_file(&inbox.join("ready.json"))?;
    if ready["type"] != "mini-hermes-handoff-delivered-v1" {
        return Err("resident ready marker absent".into());
    }
    let (_, id) = decode(&ready["bundle"])?;
    if ready["id"] != id {
        return Err("resident ready id differs".into());
    }
    Ok(ready)
}
fn check_delivery(root: &Path, inbox: &Path, task: &str) -> Result<Value> {
    workspace::private_dir(inbox)?;
    let ready = ready_bundle(inbox)?;
    let (p, id) = decode(&ready["bundle"])?;
    let room = text(&p, "room")?;
    // Revalidate source assignment and grants every time the resident acts.
    let verified = verify(root, &ready["bundle"], task, room, false)?;
    for (n, b) in p["files"].as_object().unwrap() {
        if read(&inbox.join(n))? != unhex(b.as_str().unwrap())? {
            return Err(format!("resident delivered file differs: {n}"));
        }
    }
    Ok(
        json!({"type":"mini-hermes-handoff-ready-v1","id":id,"task":task,"recipient":p["recipient"],"room":room,"roomCell":p["roomCell"],"assignment":p["assignment"],"account":file(&p,&format!("summon-{room}.json"))?["account"],"world":verified["world"],"originHeight":verified["originHeight"],"acceptedHeight":verified["acceptedHeight"],"acceptedCount":verified["acceptedCount"],"image":verified["image"],"accountEvidence":verified["accountEvidence"]}),
    )
}
pub(crate) fn seal_dismiss(ws: &Value, out: &Path, origin: &Path) -> Result<()> {
    let prior = json_file(&out.join("handoff.json"))?;
    let (mut payload, _) = decode(&prior)?;
    payload["type"] = json!("mini-hermes-dismiss-bundle-v1");
    payload["origin"] = json!({"callHex":hex(&read(&origin.join("call.bin"))?),"planHex":hex(&read(&origin.join("plan.bin"))?),"signaturesHex":hex(&read(&origin.join("transaction-signatures.bin"))?),"command":json_file(&origin.join("intent.json"))?["purpose"]["draft"]["command"],"receipt":workspace::accepted_outcome(origin)?.ok_or("dismissal is not accepted")?});
    validate_origin_command(&payload, &payload["origin"]["command"])?;
    let bytes = serde_json::to_vec(&payload).map_err(|e| e.to_string())?;
    let mut seed: [u8; 32] =
        crate::agent_reserve::private_bytes(&workspace::member_path(ws, "key")?, 32)?
            .try_into()
            .map_err(|_| "signing key width")?;
    let key = SigningKey::from_bytes(&seed);
    seed.fill(0);
    let bundle = json!({"type":"mini-hermes-handoff-v1","payloadHex":hex(&bytes),"publicKey":hex(key.verifying_key().as_bytes()),"signature":hex(&key.sign(&message(&bytes)).to_bytes())});
    let target = out.join("dismissal.json");
    if target.exists() {
        if decode(&json_file(&target)?)?.0 != payload {
            return Err("retained dismissal differs".into());
        }
    }
    crate::chat::put_json(&target, &bundle)?;
    fs::File::open(out)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    Ok(())
}
fn check_dismissal(root: &Path, inbox: &Path, task: &str) -> Result<Value> {
    workspace::private_dir(inbox)?;
    let ready = ready_bundle(inbox)?;
    let (original, _) = decode(&ready["bundle"])?;
    let bundle = json_file(&inbox.join("dismissal.json"))?;
    let (p, id) = decode(&bundle)?;
    let mut normalized = p.clone();
    normalized["type"] = original["type"].clone();
    normalized["origin"] = original["origin"].clone();
    if normalized != original || p["type"] != "mini-hermes-dismiss-bundle-v1" {
        return Err("dismissal differs from delivered assignment".into());
    }
    // Dispatcher validated this current founder signature before durable publication.
    verify(root, &bundle, task, text(&p, "room")?, false)?;
    let m = file(&p, &format!("summon-{}.json", text(&p, "room")?))?;
    Ok(
        json!({"type":"mini-hermes-dismiss-ready-v1","id":id,"task":task,"roomCell":p["roomCell"],"assignment":p["assignment"],"returnTo":m["founderAccount"],"account":m["account"],"room":p["room"]}),
    )
}
fn publish_dismissal(inbox: &Path, bundle: &Value) -> Result<Value> {
    workspace::private_dir(inbox)?;
    let ready = ready_bundle(inbox)?;
    let (original, _) = decode(&ready["bundle"])?;
    let (p, id) = decode(bundle)?;
    let mut normalized = p.clone();
    normalized["type"] = original["type"].clone();
    normalized["origin"] = original["origin"].clone();
    if normalized != original {
        return Err("dismissal must preserve delivered assignment payload".into());
    }
    let target = inbox.join("dismissal.json");
    if target.exists() {
        if decode(&json_file(&target)?)?.0 != p {
            return Err("retained dismissal differs".into());
        }
    } else {
        let stage = inbox.join(format!(".dismissal-{id}"));
        let bytes = serde_json::to_vec(bundle).map_err(|e| e.to_string())?;
        // This name is uncommitted until renamed to dismissal.json. Recover
        // interrupted writes from the newly verified exact dismissal payload.
        staged_file(&stage, &bytes)?;
        fs::rename(&stage, &target).map_err(|e| e.to_string())?;
        fs::File::open(inbox)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
    }
    Ok(json!({"type":"mini-hermes-dismiss-dispatch-v1","id":id,"inbox":inbox}))
}
fn check_registration_custody(r: &Value) -> Result<()> {
    let root = PathBuf::from(text(&r, "workspace")?);
    let ws = workspace::load(&root)?;
    if workspace::member(&ws, "subject")? != text(&r, "subject")?
        || workspace::roomkey::enc_key_id_hex(&workspace::member_path(&ws, "key")?)?
            != r["encryptionKey"]
    {
        return Err("resident registration differs from custody subject/encryption key".into());
    }
    let mut seed: [u8; 32] =
        crate::agent_reserve::private_bytes(&workspace::member_path(&ws, "key")?, 32)?
            .try_into()
            .map_err(|_| "registered key width")?;
    let key = SigningKey::from_bytes(&seed);
    seed.fill(0);
    let host = workspace::workspace_host(&ws)?;
    let config = workspace::member_path(&ws, "config")?;
    let socket = crate::SOCKET.get().ok_or("registry socket absent")?;
    let reply = crate::session_invoke(
        &host,
        socket,
        &config,
        144,
        &serde_json::to_vec(
            &json!({"subject":r["subject"],"publicKey":hex(key.verifying_key().as_bytes())}),
        )
        .map_err(|e| e.to_string())?,
    )?;
    let [144, body @ ..] = reply.as_slice() else {
        return Err("registered subject key lookup refused".into());
    };
    let status: Value = serde_json::from_slice(body).map_err(|e| e.to_string())?;
    if status["isCurrent"] != true
        || status["currentRevoked"] != false
        || status["subject"] != r["subject"]
    {
        return Err("registered resident custody signing key is not current".into());
    }
    Ok(())
}
fn emit_registration(root: &Path, task: &str, cell: &str, inbox: &Path) -> Result<Value> {
    workspace::decimal(task, "task")?;
    workspace::decimal(cell, "room cell")?;
    if !root.is_absolute() || !inbox.is_absolute() {
        return Err("registration workspace/inbox must be absolute".into());
    }
    workspace::private_dir(root)?;
    workspace::private_dir(inbox)?;
    let ws = workspace::load(root)?;
    let r = json!({"type":"mini-hermes-dispatch-registration-v1","task":task,
        "subject":workspace::member(&ws,"subject")?,"roomCell":cell,
        "encryptionKey":workspace::roomkey::enc_key_id_hex(&workspace::member_path(&ws,"key")?)?,
        "workspace":root,"inbox":inbox});
    check_registration_custody(&r)?;
    Ok(r)
}
fn origin_count(payload: &Value) -> Result<&str> {
    let count = text(&payload["origin"]["receipt"], "acceptedCount")?;
    workspace::decimal(count, "accepted origin count")?;
    if count == "0" {
        return Err("assignment has no accepted origin".into());
    }
    Ok(count)
}
fn point_current(inbox: &Path, bundle: &Value) -> Result<()> {
    let (p, id) = decode(bundle)?;
    let parent = inbox.parent().ok_or("assignment room parent absent")?;
    workspace::private_dir(parent)?;
    // Source verification can finish before a later assignment lands. Serialize
    // the cache publication and compare exact admitted origins, so a delayed
    // old dispatcher never overwrites a newer delivered assignment's pointer.
    let _writer = crate::transport::service_lock(&parent.join("current.lock"))?;
    let target = parent.join("current.json");
    let incoming_count = origin_count(&p)?;
    if target.exists() {
        let prior = json_file(&target)?;
        fields(
            &prior,
            &["type", "task", "roomCell", "assignment", "id", "inbox"],
        )?;
        if prior["type"] != "mini-hermes-assignment-pointer-v1"
            || prior["roomCell"] != p["roomCell"]
        {
            return Err("retained assignment pointer differs from canonical room".into());
        }
        workspace::decimal(text(&prior, "assignment")?, "retained assignment")?;
        let previous_inbox = parent.join(format!("assignment-{}", text(&prior, "assignment")?));
        if prior["inbox"] != json!(previous_inbox) {
            return Err("retained assignment pointer selects a noncanonical inbox".into());
        }
        workspace::private_dir(&previous_inbox)?;
        let ready = ready_bundle(&previous_inbox)?;
        let (previous_payload, previous_id) = decode(&ready["bundle"])?;
        if prior["id"] != previous_id
            || prior["task"] != previous_payload["task"]
            || prior["roomCell"] != previous_payload["roomCell"]
            || prior["assignment"] != previous_payload["assignment"]
        {
            return Err("retained assignment pointer differs from immutable delivery".into());
        }
        let previous_count = origin_count(&previous_payload)?;
        let order =
            (incoming_count.len(), incoming_count).cmp(&(previous_count.len(), previous_count));
        if order.is_lt() {
            return Ok(());
        }
        if order.is_eq() && previous_payload != p {
            return Err("same accepted origin cannot replace assignment delivery".into());
        }
    }
    // Private routing cache only. Every selector below rechecks accepted source
    // assignment and current grants before returning an activation.
    crate::chat::put_json(
        &target,
        &json!({"type":"mini-hermes-assignment-pointer-v1","task":p["task"],
            "roomCell":p["roomCell"],"assignment":p["assignment"],"id":id,"inbox":inbox}),
    )
}
fn activation(registration: &Path) -> Result<Value> {
    let r = registration_file(registration)?;
    check_registration_custody(&r)?;
    let root = PathBuf::from(text(&r, "workspace")?);
    let base = PathBuf::from(text(&r, "inbox")?);
    if !root.is_absolute() || !base.is_absolute() {
        return Err("registered paths must be absolute".into());
    }
    workspace::private_dir(&base)?;
    let parent = base.join(format!("room-{}", text(&r, "roomCell")?));
    workspace::private_dir(&parent)?;
    let pointer = json_file(&parent.join("current.json"))?;
    fields(
        &pointer,
        &["type", "task", "roomCell", "assignment", "id", "inbox"],
    )?;
    if pointer["type"] != "mini-hermes-assignment-pointer-v1"
        || pointer["task"] != r["task"]
        || pointer["roomCell"] != r["roomCell"]
    {
        return Err("assignment routing pointer differs from registered room/task".into());
    }
    workspace::decimal(text(&pointer, "assignment")?, "assignment")?;
    let inbox = parent.join(format!("assignment-{}", text(&pointer, "assignment")?));
    if pointer["inbox"] != json!(inbox) {
        return Err("assignment routing pointer selects a noncanonical inbox".into());
    }
    let ready = ready_bundle(&inbox)?;
    let (_, expected_inbox, _) = registered(registration, &ready["bundle"])?;
    let (payload, id) = decode(&ready["bundle"])?;
    if expected_inbox != inbox
        || pointer["id"] != id
        || pointer["assignment"] != payload["assignment"]
    {
        return Err("assignment routing pointer differs from delivered source identity".into());
    }
    let mut result = check_delivery(&root, &inbox, text(&r, "task")?)?;
    result["type"] = json!("mini-hermes-assignment-activation-v1");
    result["inbox"] = json!(inbox);
    Ok(result)
}
fn registry(directory: &Path) -> Result<Value> {
    let mut residents = Vec::new();
    let mut diagnostics = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut paths = fs::read_dir(directory)
        .map_err(|e| e.to_string())?
        .map(|e| e.map(|e| e.path()).map_err(|e| e.to_string()))
        .collect::<Result<Vec<_>>>()?;
    paths.sort();
    if paths.len() > 4096 {
        return Err("resident registration inventory exceeds bound".into());
    }
    for path in paths {
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let r = registration_file(&path)?;
        for k in ["task", "subject", "roomCell"] {
            workspace::decimal(text(&r, k)?, k)?;
        }
        if !seen.insert((
            text(&r, "subject")?.to_owned(),
            text(&r, "roomCell")?.to_owned(),
        )) {
            return Err("ambiguous resident subject/room registration".into());
        }
        let eligible = check_registration_custody(&r).is_ok();
        // Custody/key availability is per recipient. It cannot stop unrelated
        // controllers. Public diagnostics disclose no workspace/key paths.
        diagnostics.push(
            json!({"task":r["task"],"subject":r["subject"],"roomCell":r["roomCell"],
            "eligible":eligible,"code":if eligible {"verified"} else {"custody_unavailable"}}),
        );
        if eligible {
            residents.push(json!({"subject":r["subject"],"task":r["task"],"roomCell":r["roomCell"],"encryptionKey":r["encryptionKey"]}));
        }
    }
    Ok(json!({"type":"mini-hermes-registry-v1","residents":residents,"diagnostics":diagnostics}))
}
fn registration_file(registration: &Path) -> Result<Value> {
    use std::os::unix::fs::MetadataExt;
    let meta = fs::symlink_metadata(registration).map_err(|e| e.to_string())?;
    if !meta.is_file()
        || meta.mode() & 0o022 != 0
        || (meta.uid() != 0 && meta.uid() != unsafe { libc::geteuid() })
    {
        return Err(
            "dispatcher registration must be operator-owned and not group/world writable".into(),
        );
    }
    let r = json_file(registration)?;
    fields(
        &r,
        &[
            "type",
            "task",
            "subject",
            "roomCell",
            "encryptionKey",
            "workspace",
            "inbox",
        ],
    )?;
    if r["type"] != "mini-hermes-dispatch-registration-v1" {
        return Err("dispatcher registration type refused".into());
    }
    Ok(r)
}
fn registered(registration: &Path, bundle: &Value) -> Result<(PathBuf, PathBuf, Value)> {
    let r = registration_file(registration)?;
    let (p, _) = decode(bundle)?;
    let m = file(&p, &format!("summon-{}.json", text(&p, "room")?))?;
    if r["type"] != "mini-hermes-dispatch-registration-v1"
        || r["task"] != p["task"]
        || r["subject"] != p["recipient"]
        || r["roomCell"] != p["roomCell"]
        || r["encryptionKey"] != m["encryptionKey"]
    {
        return Err("handoff differs from registered task/subject/room/key".into());
    }
    let root = PathBuf::from(text(&r, "workspace")?);
    let base = PathBuf::from(text(&r, "inbox")?);
    if !root.is_absolute() || !base.is_absolute() {
        return Err("registered paths must be absolute".into());
    }
    workspace::private_dir(&root)?;
    workspace::private_dir(&base)?;
    // No bundle path can choose where a resident receives its files.
    let destination = base
        .join(format!("room-{}", text(&p, "roomCell")?))
        .join(format!("assignment-{}", text(&p, "assignment")?));
    Ok((root, destination, r))
}
fn staged_file(path: &Path, bytes: &[u8]) -> Result<()> {
    if read(path).is_ok_and(|prior| prior == bytes) {
        return Ok(());
    }
    workspace::replace_private_file(path, bytes)
}
fn publish(inbox: &Path, bundle: &Value) -> Result<Value> {
    let (p, id) = decode(bundle)?;
    if inbox.exists() {
        workspace::private_dir(inbox)?;
        let ready = ready_bundle(inbox)?;
        if ready["id"] != id || decode(&ready["bundle"])?.0 != p {
            return Err("registered assignment inbox already contains another handoff".into());
        }
        for (n, b) in p["files"].as_object().unwrap() {
            if read(&inbox.join(n))? != unhex(b.as_str().unwrap())? {
                return Err("retained delivery differs".into());
            }
        }
        return Ok(json!({"type":"mini-hermes-dispatch-v1","id":id,"inbox":inbox,"replayed":true}));
    }
    let parent = inbox.parent().ok_or("delivery parent absent")?;
    if !parent.exists() {
        workspace::make_private_dir(parent)?;
    }
    workspace::private_dir(parent)?;
    let stage = parent.join(format!(".staging-{id}"));
    if !stage.exists() {
        workspace::make_private_dir(&stage)?;
    }
    workspace::private_dir(&stage)?;
    for (n, b) in p["files"].as_object().unwrap() {
        let file = stage.join(n);
        let bytes = unhex(b.as_str().unwrap())?;
        // The staging directory is uncommitted. Repair incomplete crash cuts
        // from this freshly verified payload, atomically before the ready gate.
        staged_file(&file, &bytes)?;
    }
    let ready = json!({"type":"mini-hermes-handoff-delivered-v1","id":id,"bundle":bundle});
    staged_file(
        &stage.join("ready.json"),
        &serde_json::to_vec(&ready).map_err(|e| e.to_string())?,
    )?;
    fs::File::open(&stage)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    fs::rename(&stage, inbox).map_err(|e| format!("atomic handoff publication refused: {e}"))?;
    fs::File::open(parent)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())?;
    Ok(json!({"type":"mini-hermes-dispatch-v1","id":id,"inbox":inbox,"replayed":false}))
}
pub(crate) fn run(mut args: Args) -> Result<()> {
    let action = args
        .required("action")?
        .into_string()
        .map_err(|_| "invalid action")?;
    match action.as_str() {
        "registration" => {
            let root = PathBuf::from(args.required("dir")?);
            let task = args
                .required("task")?
                .into_string()
                .map_err(|_| "invalid task")?;
            let cell = args
                .required("room-cell")?
                .into_string()
                .map_err(|_| "invalid room cell")?;
            let inbox = PathBuf::from(args.required("inbox")?);
            args.finish()?;
            crate::print_json(&emit_registration(&root, &task, &cell, &inbox)?)
        }
        "activation" => {
            let registration = PathBuf::from(args.required("registration")?);
            args.finish()?;
            crate::print_json(&activation(&registration)?)
        }
        "registry" => {
            let directory = PathBuf::from(args.required("registrations")?);
            args.finish()?;
            crate::print_json(&registry(&directory)?)
        }
        "dispatch" => {
            let registration = PathBuf::from(args.required("registration")?);
            let path = PathBuf::from(args.required("bundle")?);
            args.finish()?;
            let bundle = json_file(&path)?;
            let (root, inbox, r) = registered(&registration, &bundle)?;
            let (p, _) = decode(&bundle)?;
            if p["type"] == "mini-hermes-dismiss-bundle-v1" {
                let retained = inbox.join("dismissal.json");
                let first = !retained.exists();
                if !first && decode(&json_file(&retained)?)?.0 != p {
                    return Err("dismissal replacement refused".into());
                }
                verify(&root, &bundle, text(&r, "task")?, text(&p, "room")?, first)?;
                return crate::print_json(&publish_dismissal(&inbox, &bundle)?);
            }
            let first_delivery = !inbox.exists();
            if !first_delivery {
                let ready = ready_bundle(&inbox)?;
                if decode(&ready["bundle"])?.0 != p {
                    return Err("registered assignment payload replacement refused".into());
                }
            }
            verify(
                &root,
                &bundle,
                text(&r, "task")?,
                text(&p, "room")?,
                first_delivery,
            )?;
            let delivered = publish(&inbox, &bundle)?;
            point_current(&inbox, &bundle)?;
            crate::print_json(&delivered)
        }
        "verify" => {
            let root = PathBuf::from(args.required("dir")?);
            let task = args
                .required("task")?
                .into_string()
                .map_err(|_| "invalid task")?;
            let room = args
                .required("room")?
                .into_string()
                .map_err(|_| "invalid room")?;
            let path = PathBuf::from(args.required("bundle")?);
            args.finish()?;
            crate::print_json(&verify(&root, &json_file(&path)?, &task, &room, true)?)
        }
        "check-dismissal" => {
            let root = PathBuf::from(args.required("dir")?);
            let task = args
                .required("task")?
                .into_string()
                .map_err(|_| "invalid task")?;
            let inbox = PathBuf::from(args.required("inbox")?);
            args.finish()?;
            crate::print_json(&check_dismissal(&root, &inbox, &task)?)
        }
        "check-delivery" => {
            let root = PathBuf::from(args.required("dir")?);
            let task = args
                .required("task")?
                .into_string()
                .map_err(|_| "invalid task")?;
            let inbox = PathBuf::from(args.required("inbox")?);
            args.finish()?;
            crate::print_json(&check_delivery(&root, &inbox, &task)?)
        }
        _ => Err("unknown handoff action".into()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture(room_cell: &str, assignment: &str) -> (Value, Value) {
        let manifest = json!({"type":"mini-hermes-summon-v1","room":"lab","roomCell":room_cell,"task":"71","hermes":"8","founder":"7","assignment":assignment,"encryptionKey":"ab".repeat(32),"stream":"80","founderAccount":"7","account":{"name":"lab-hermes","target":"81"},"program":{"name":"lab-program","target":"82"},"docs":[]});
        let files = json!({"summon-lab.json":hex(&serde_json::to_vec(&manifest).unwrap()),"lab-invite.json":hex(&serde_json::to_vec(&json!({"type":"minidregg-delegated-reference-v1","recipient":"8","target":room_cell,"kind":"object","room":true,"capability":"91"})).unwrap()),"lab-hermes.json":hex(&serde_json::to_vec(&json!({"type":"minidregg-fleet-account-handoff-v1","owner":"8","kind":"account","target":"81","observeCapability":"92"})).unwrap())});
        let command = json!({"subject":"7","nonce":"4","targets":[{"kind":"object","target":room_cell,"payload":{"type":"scalar","actions":[{"type":"create","key":{"type":"object","resource":room_cell,"field":"1008"},"value":"8"},{"type":"create","key":{"type":"object","resource":room_cell,"field":"1009"},"value":"81"},{"type":"create","key":{"type":"object","resource":room_cell,"field":ASSIGNMENT_FIELD},"value":assignment}]}}]});
        let payload = json!({"type":"mini-hermes-summon-bundle-v1","world":{"domain":"31","expectedSeed":"0"},"recipient":"8","task":"71","founder":"7","room":"lab","roomCell":room_cell,"assignment":assignment,"origin":{"command":command,"receipt":{"acceptedCount":assignment}},"files":files});
        let bytes = serde_json::to_vec(&payload).unwrap();
        let key = SigningKey::from_bytes(&[7; 32]);
        let bundle = json!({"type":"mini-hermes-handoff-v1","payloadHex":hex(&bytes),"publicKey":hex(key.verifying_key().as_bytes()),"signature":hex(&key.sign(&message(&bytes)).to_bytes())});
        (payload, bundle)
    }
    fn scratch() -> PathBuf {
        let p = PathBuf::from(format!(
            "/tmp/mini-handoff-{}-{}",
            std::process::id(),
            workspace::random_nonce().unwrap()
        ));
        workspace::make_private_dir(&p).unwrap();
        p
    }
    #[test]
    fn complete_payload_tamper_is_refused() {
        let (_, mut b) = fixture("70", "1");
        assert!(decode(&b).is_ok());
        let mut bytes = unhex(b["payloadHex"].as_str().unwrap()).unwrap();
        bytes[5] ^= 1;
        b["payloadHex"] = json!(hex(&bytes));
        assert!(decode(&b).is_err());
    }
    #[test]
    fn unrelated_accepted_origin_cannot_summon() {
        let (p, _) = fixture("70", "1");
        let c = &p["origin"]["command"];
        validate_origin_command(&p, c).unwrap();
        for (path, value) in [
            ("/subject", json!("9")),
            ("/targets/0/target", json!("71")),
            ("/targets/0/payload/actions/2/value", json!("2")),
            ("/targets/0/payload/actions/2/key/field", json!("1008")),
        ] {
            let mut changed = c.clone();
            *changed.pointer_mut(path).unwrap() = value;
            assert!(validate_origin_command(&p, &changed).is_err(), "{path}");
        }
    }
    #[test]
    fn dismissal_requires_exact_old_generation_cas() {
        let (mut p, _) = fixture("70", "1");
        p["type"] = json!("mini-hermes-dismiss-bundle-v1");
        let mut c = p["origin"]["command"].clone();
        for a in c["targets"][0]["payload"]["actions"]
            .as_array_mut()
            .unwrap()
        {
            a["type"] = json!("write");
            a["expected"] = a["value"].clone();
            a["value"] = json!("0");
        }
        validate_origin_command(&p, &c).unwrap();
        c["targets"][0]["payload"]["actions"][2]["expected"] = json!("2");
        assert!(validate_origin_command(&p, &c).is_err());
    }
    #[test]
    fn durable_publication_retries_once_and_refuses_replacement() {
        let root = scratch();
        let inbox = root.join("room-70/assignment-1");
        let (_, b) = fixture("70", "1");
        assert_eq!(publish(&inbox, &b).unwrap()["replayed"], false);
        assert_eq!(publish(&inbox, &b).unwrap()["replayed"], true);
        let (_, other) = fixture("70", "2");
        assert!(publish(&inbox, &other).is_err());
        let ready = ready_bundle(&inbox).unwrap();
        assert_eq!(ready["bundle"], b);
        fs::write(inbox.join("lab-invite.json"), b"altered").unwrap();
        assert!(publish(&inbox, &b).is_err());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn same_display_alias_has_separate_custody() {
        let root = scratch();
        let (_, a) = fixture("70", "1");
        let (_, b) = fixture("71", "1");
        publish(&root.join("room-70/assignment-1"), &a).unwrap();
        publish(&root.join("room-71/assignment-1"), &b).unwrap();
        assert_ne!(
            ready_bundle(&root.join("room-70/assignment-1")).unwrap()["id"],
            ready_bundle(&root.join("room-71/assignment-1")).unwrap()["id"]
        );
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn operator_registration_binds_selected_key_task_room_and_subject() {
        let root = scratch();
        let ws = root.join("ws");
        let inbox = root.join("inbox");
        workspace::make_private_dir(&ws).unwrap();
        workspace::make_private_dir(&inbox).unwrap();
        let reg = root.join("registration.json");
        let (_, b) = fixture("70", "1");
        let r = json!({"type":"mini-hermes-dispatch-registration-v1","task":"71","subject":"8","roomCell":"70","encryptionKey":"ab".repeat(32),"workspace":ws,"inbox":inbox});
        workspace::private_file(&reg, &serde_json::to_vec(&r).unwrap()).unwrap();
        assert!(registered(&reg, &b).is_ok());
        for (key, value) in [
            ("task", "72"),
            ("subject", "9"),
            ("roomCell", "71"),
            ("encryptionKey", "wrong"),
        ] {
            let mut changed = r.clone();
            changed[key] = json!(value);
            fs::write(&reg, serde_json::to_vec(&changed).unwrap()).unwrap();
            assert!(registered(&reg, &b).is_err(), "{key}");
        }
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn uncommitted_partial_files_and_ready_recover_after_crash() {
        let root = scratch();
        let inbox = root.join("room-70/assignment-1");
        let (_, bundle) = fixture("70", "1");
        let (_, id) = decode(&bundle).unwrap();
        let parent = root.join("room-70");
        workspace::make_private_dir(&parent).unwrap();
        let stage = parent.join(format!(".staging-{id}"));
        workspace::make_private_dir(&stage).unwrap();
        workspace::private_file(&stage.join("lab-invite.json"), b"partial").unwrap();
        workspace::private_file(&stage.join("ready.json"), b"{").unwrap();
        publish(&inbox, &bundle).unwrap();
        assert_eq!(ready_bundle(&inbox).unwrap()["bundle"], bundle);
        assert_eq!(publish(&inbox, &bundle).unwrap()["replayed"], true);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn uncommitted_partial_dismissal_recovers_after_crash() {
        let root = scratch();
        let inbox = root.join("room-70/assignment-1");
        let (mut p, bundle) = fixture("70", "1");
        publish(&inbox, &bundle).unwrap();
        p["type"] = json!("mini-hermes-dismiss-bundle-v1");
        for action in p["origin"]["command"]["targets"][0]["payload"]["actions"]
            .as_array_mut()
            .unwrap()
        {
            action["type"] = json!("write");
            action["expected"] = action["value"].clone();
            action["value"] = json!("0");
        }
        let bytes = serde_json::to_vec(&p).unwrap();
        let key = SigningKey::from_bytes(&[7; 32]);
        let dismiss = json!({"type":"mini-hermes-handoff-v1","payloadHex":hex(&bytes),"publicKey":hex(key.verifying_key().as_bytes()),"signature":hex(&key.sign(&message(&bytes)).to_bytes())});
        let (_, id) = decode(&dismiss).unwrap();
        workspace::private_file(&inbox.join(format!(".dismissal-{id}")), b"{").unwrap();
        publish_dismissal(&inbox, &dismiss).unwrap();
        assert_eq!(json_file(&inbox.join("dismissal.json")).unwrap(), dismiss);
        publish_dismissal(&inbox, &dismiss).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn routing_pointer_uses_cell_assignment_and_exact_ready_identity() {
        let root = scratch();
        for (cell, assignment) in [("70", "1"), ("71", "1"), ("70", "2")] {
            let inbox = root.join(format!("room-{cell}/assignment-{assignment}"));
            let (_, bundle) = fixture(cell, assignment);
            publish(&inbox, &bundle).unwrap();
            point_current(&inbox, &bundle).unwrap();
            let pointer = json_file(&root.join(format!("room-{cell}/current.json"))).unwrap();
            assert_eq!(pointer["roomCell"], cell);
            assert_eq!(pointer["assignment"], assignment);
            assert_eq!(pointer["id"], ready_bundle(&inbox).unwrap()["id"]);
            assert_eq!(pointer["inbox"], json!(inbox));
        }
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn delayed_older_dispatch_cannot_replace_current_assignment_pointer() {
        let root = scratch();
        let first = root.join("room-70/assignment-1");
        let second = root.join("room-70/assignment-2");
        let (_, older) = fixture("70", "1");
        let (_, newer) = fixture("70", "2");
        publish(&first, &older).unwrap();
        publish(&second, &newer).unwrap();
        point_current(&second, &newer).unwrap();
        // T1 passed its source check before T2 was accepted, but its delayed
        // publication arrives after T2's ready gate and pointer are durable.
        point_current(&first, &older).unwrap();
        let pointer = json_file(&root.join("room-70/current.json")).unwrap();
        assert_eq!(pointer["assignment"], "2");
        assert_eq!(pointer["inbox"], json!(second));
        point_current(&second, &newer).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn source_seed_keeps_all_256_bits() {
        let root = scratch();
        let config = root.join("config.json");
        let seed = "22321621677379463296262690040024671810364854896513930816726568652528571384147";
        workspace::private_file(
            &config,
            format!("{{\"domain\":8501,\"expectedSeed\":{seed}}}").as_bytes(),
        )
        .unwrap();
        let bound = world(&json!({"config":config})).unwrap();
        assert_eq!(bound["expectedSeed"], seed);
        assert_eq!(bound["domain"], "8501");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn unrelated_writers_do_not_starve_delivery() {
        let mut image = None;
        consistent(
            &mut image,
            &json!({"worldRoot":"1","authorityRoot":"2","height":"3","domain":"31"}),
        )
        .unwrap();
        consistent(
            &mut image,
            &json!({"worldRoot":"4","authorityRoot":"5","height":"6","domain":"31"}),
        )
        .unwrap();
        assert!(consistent(
            &mut image,
            &json!({"worldRoot":"4","authorityRoot":"5","height":"6","domain":"32"})
        )
        .is_err());
    }
    #[test]
    fn account_custody_binds_native_query_and_distinguishes_operation_grant() {
        let recipient = json!("8");
        let world = json!({"domain":"31","expectedSeed":"99"});
        let mut account = json!({"kind":"account","target":"70",
            "observeCapability":"80","operationCapability":"80"});
        let view = json!({"type":"capability","kind":"account","head":{
            "id":"80","holder":{"type":"subject","subject":"8"},
            "room":"70","verbs":["observe","transfer"]}});
        let challenge = json!({"height":"3",
            "worldRoot":"49263608972345960957461998196908737762472409962603021562937875631642370926371",
            "authorityRoot":"60754036600791298313000201660134478268036195276917052611359876138565388040352",
            "domain":"31","intent":{"subject":"8","nonce":"1",
            "purpose":{"type":"query","kind":"account","target":"70","view":"capability"},
            "grants":[{"kind":"account","target":"70","capability":"80"}]}});
        let evidence = account_evidence(
            &recipient,
            &world,
            &account,
            &view,
            &challenge,
            b"challenge",
            b"signed",
        )
        .unwrap();
        assert_eq!(evidence["operationVerified"], true);
        assert_eq!(evidence["transferGranted"], true);
        assert_eq!(
            evidence["observation"]["challengeSha256"],
            digest(b"challenge")
        );
        assert_eq!(evidence["observation"]["signedSha256"], digest(b"signed"));
        assert!(evidence.get("owner").is_none());
        account["operationCapability"] = json!("81");
        let separate = account_evidence(
            &recipient,
            &world,
            &account,
            &view,
            &challenge,
            b"challenge",
            b"signed",
        )
        .unwrap();
        assert_eq!(separate["operationVerified"], false);
        assert_eq!(separate["transferGranted"], false);
        for pointer in ["/head/id", "/head/holder/subject", "/kind"] {
            let mut changed = view.clone();
            *changed.pointer_mut(pointer).unwrap() = json!("wrong");
            assert!(account_evidence(
                &recipient,
                &world,
                &account,
                &changed,
                &challenge,
                b"challenge",
                b"signed"
            )
            .is_err());
        }
        for pointer in [
            "/intent/subject",
            "/intent/purpose/target",
            "/intent/grants/0/capability",
            "/domain",
            "/worldRoot",
            "/authorityRoot",
        ] {
            let mut changed = challenge.clone();
            *changed.pointer_mut(pointer).unwrap() = json!("wrong");
            assert!(account_evidence(
                &recipient,
                &world,
                &account,
                &view,
                &changed,
                b"challenge",
                b"signed"
            )
            .is_err());
        }
        let mut no_transfer = view.clone();
        no_transfer["head"]["verbs"] = json!(["observe"]);
        account["operationCapability"] = json!("80");
        assert_eq!(
            account_evidence(
                &recipient,
                &world,
                &account,
                &no_transfer,
                &challenge,
                b"challenge",
                b"signed"
            )
            .unwrap()["transferGranted"],
            false
        );
    }
}
