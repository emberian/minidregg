//! Shared room names are current bindings, not object identities.
//! A successful resolution returns a target-pinned reference. The caller must
//! retain it through authoring/replanning; exact submission retries use retained
//! signed bytes and must never resolve a name again.
use super::{decimal, member, validate_name, validate_ref_name};
use crate::Result;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::path::Path;

pub(crate) const INDEX_FIELD: &str = crate::room_schema::NAMES_FIELD;
pub(crate) const SCHEME: &str = "mini-name";

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Binding {
    pub name: String,
    pub kind: String,
    pub target: String,
    pub link: String,
}

fn text(value: &Value, field: &str) -> Result<String> {
    let encoded = member(value, field)?;
    let bytes = crate::decode_hex(encoded)?;
    // Canonical bytes have only one JSON hex spelling. Reject alternate
    // presentations rather than letting different clients normalize differently.
    if crate::hex(&bytes) != encoded {
        return Err(format!("noncanonical shared-name {field}"));
    }
    String::from_utf8(bytes).map_err(|_| format!("shared-name {field} is not UTF-8"))
}

pub(crate) fn target(name: &str, kind: &str, id: &str) -> Result<Value> {
    validate_name(name)?;
    if !matches!(kind, "object" | "account" | "program") {
        return Err("shared name has unknown target kind".into());
    }
    decimal(id, "shared-name target")?;
    Ok(
        json!({"type":"external", "scheme":crate::hex(SCHEME.as_bytes()),
        "authority":crate::hex(name.as_bytes()),
        "path":crate::hex(format!("{kind}/{id}").as_bytes())}),
    )
}

/// Decode only the reserved link convention. Malformed records in this
/// namespace are errors, including records for names other than the query.
pub(crate) fn binding(entry: &Value) -> Result<Option<Binding>> {
    if entry.get("type").and_then(Value::as_str) != Some("link") {
        return Ok(None);
    }
    let link_target = entry.get("target").ok_or("link lacks target")?;
    if link_target.get("type").and_then(Value::as_str) != Some("external") {
        return Ok(None);
    }
    if crate::decode_hex(member(link_target, "scheme")?)? != SCHEME.as_bytes() {
        return Ok(None);
    }
    text(link_target, "scheme")?;
    // Missing tombstone is malformed, not an assertion that it is live.
    let retired = entry
        .get("tombstonedAt")
        .ok_or("shared-name link lacks retirement state")?;
    if !retired.is_null() {
        // Retirement is a source-derived version event digest, not a short
        // user-selected identifier. The native host emits its full width.
        super::field_decimal(
            retired.as_str().ok_or("invalid shared-name retirement")?,
            "retirement",
        )?;
        return Ok(None);
    }
    if member(entry, "relation")? != "0" || !entry.get("source").is_some_and(Value::is_null) {
        return Err("shared-name link must have relation zero and no source range".into());
    }
    let name = text(link_target, "authority")?;
    validate_name(&name)?;
    let path = text(link_target, "path")?;
    let (kind, id) = path.split_once('/').ok_or("shared-name path is KIND/ID")?;
    let canonical = target(&name, kind, id)?;
    if &canonical != link_target {
        return Err("shared-name target is not canonical".into());
    }
    let link = member(entry, "id")?;
    decimal(link, "shared-name link")?;
    Ok(Some(Binding {
        name,
        kind: kind.to_owned(),
        target: id.to_owned(),
        link: link.to_owned(),
    }))
}

pub(crate) fn bindings(view: &Value) -> Result<BTreeMap<String, Binding>> {
    let cell = view.get("cell").ok_or("signed index view lacks cell")?;
    let entries = cell
        .get("entries")
        .and_then(Value::as_array)
        .ok_or("signed index view lacks entries")?;
    if entries
        .iter()
        .any(|entry| entry.get("type").and_then(Value::as_str).is_none())
    {
        return Err("room index is not a content document".into());
    }
    let mut found = BTreeMap::new();
    for entry in entries {
        if let Some(binding) = binding(entry)? {
            if found.insert(binding.name.clone(), binding).is_some() {
                return Err("shared room index contains ambiguous duplicate names".into());
            }
        }
    }
    Ok(found)
}

pub(crate) fn index_target(view: &Value) -> Result<Option<String>> {
    let entries = view
        .pointer("/cell/entries")
        .and_then(Value::as_array)
        .ok_or("signed room view lacks declared entries")?;
    let mut index = None;
    let mut present = false;
    for entry in entries {
        if entry.pointer("/key/field").and_then(Value::as_str) != Some(INDEX_FIELD) {
            continue;
        }
        if present {
            return Err("room contains duplicate index-pointer fields".into());
        }
        present = true;
        let value = member(entry, "value")?;
        decimal(value, "room index pointer")?;
        if value != "0" {
            index = Some(value.to_owned());
        }
    }
    Ok(index)
}

fn same_snapshot(a: &Value, b: &Value) -> Result<()> {
    if member(a, "worldRoot")? != member(b, "worldRoot")?
        || member(a, "height")? != member(b, "height")?
    {
        return Err("shared-name discovery moved between room and index; reopen the name".into());
    }
    Ok(())
}

/// This adapter calls the ordinary signed observation receiver. No unsigned
/// discovery endpoint or cached index is accepted as evidence of absence.
pub(crate) fn resolve(root: &Path, workspace: &Value, name: &str) -> Result<Value> {
    let mut opened = resolve_many(root, workspace, &[name.to_owned()])?;
    Ok(opened.remove(0))
}

/// Keep one coherent admitted room/index chain per room within this command.
/// A bootstrap read supplies only an index candidate; the paired batch checks
/// the room's pointer again in the same image that admits the index read.
pub(crate) fn resolve_many(root: &Path, workspace: &Value, names: &[String]) -> Result<Vec<Value>> {
    let mut chains = BTreeMap::<String, Vec<(Value, String, Value, Value)>>::new();
    names.iter().map(|name| {
        let chain = name.rsplit_once('/').map(|(room, _)| room).unwrap_or(name);
        let mut opened = resolve_with(name, |n| super::local_reference(root,n), |reference,field| {
            if !chains.contains_key(chain) {
                chains.insert(chain.to_owned(), coherent_discovery(root,workspace,reference)?);
            }
            chains[chain].iter().find(|(r,f,_,_)|
                f == field && r["kind"] == reference["kind"] && r["target"] == reference["target"])
                .map(|(_,_,view,at)| (view.clone(),at.clone()))
                .ok_or("coherent discovery lacks the requested dependency".into())
        })?;
        // Preserve the actually invoked discovery candidates, including an
        // existing direct index capability selected by exact target identity.
        if let Some(reads) = chains.get(chain) {
            opened["sharedName"]["roomRef"] = reads[0].0.clone();
            opened["sharedName"]["indexRef"] = reads.get(1)
                .map(|read| read.0.clone()).unwrap_or(Value::Null);
        }
        existing_authority(root,&opened)
    }).collect()
}

/// The room's index pointer as this workspace last read it, in a coherent
/// room/index pair: a candidate, like the bootstrap read it replaces, never
/// evidence. The pair batch reads the room's pointer in the same image as the
/// index either way and replans when it moved.
fn hint_path(root: &Path, room: &Value) -> Result<std::path::PathBuf> {
    let target = member(room, "target")?;
    decimal(target, "room target")?;
    Ok(root.join("discovery").join(format!("{target}.index")))
}

fn index_hint(root: &Path, room: &Value) -> Option<String> {
    let text = std::fs::read_to_string(hint_path(root, room).ok()?).ok()?;
    let index = text.trim();
    decimal(index, "index hint").ok()?;
    Some(index.to_owned())
}

fn remember_index(root: &Path, room: &Value, index: &str) {
    let Ok(path) = hint_path(root, room) else { return };
    if index_hint(root, room).as_deref() == Some(index) { return; }
    let directory = root.join("discovery");
    let _ = std::fs::create_dir(&directory);
    if super::private_dir(&directory).is_ok() {
        let _ = super::replace_private_file(&path, format!("{index}\n").as_bytes());
    }
}

fn forget_index(root: &Path, room: &Value) {
    if let Ok(path) = hint_path(root, room) { let _ = std::fs::remove_file(path); }
}

/// The room's discovery fields and, when it has an index, the index's names,
/// read together in one native image.
fn coherent_discovery(root: &Path, workspace: &Value, room: &Value)
    -> Result<Vec<(Value,String,Value,Value)>> {
    let room = existing_authority(root,room)?;
    if let Some(hint) = index_hint(root, &room) {
        // A stale candidate (an index this grant no longer reads, a cell gone)
        // is not a decision about the name: discover from the room again.
        match coherent_pair(root, workspace, &room, hint) {
            Ok(chain) => return Ok(chain),
            Err(_) => forget_index(root, &room),
        }
    }
    let (room_view, room_at) = discovery_read(root,workspace,&room,INDEX_FIELD)?;
    let Some(index) = index_target(&room_view)? else {
        return Ok(vec![(room,INDEX_FIELD.to_owned(),room_view,room_at)]);
    };
    coherent_pair(root, workspace, &room, index)
}

/// Read the room and an index candidate in one batch. Replan only a changed
/// room pointer, never a different unrelated world head.
fn coherent_pair(root: &Path, workspace: &Value, room: &Value, mut index: String)
    -> Result<Vec<(Value,String,Value,Value)>> {
    for _ in 0..3 {
        let mut index_ref = room.clone();
        index_ref["target"] = json!(index);
        index_ref.as_object_mut().unwrap().remove("room");
        let index_ref = existing_authority(root,&index_ref)?;
        let references = vec![room.clone(),index_ref.clone()];
        let result = super::signed_views(root,workspace,&references,"resource-scope")?;
        let current_room = scoped_resource(&result[0].0,room,INDEX_FIELD)?;
        let current_index = index_target(&current_room)?;
        if current_index.as_deref() != Some(&index) {
            let Some(next) = current_index else {
                forget_index(root, room);
                return Ok(vec![(room.clone(),INDEX_FIELD.to_owned(),current_room,result[0].1.clone())]);
            };
            index = next;
            continue;
        }
        let index_view = scoped_resource(&result[1].0,&index_ref,"annotations")?;
        remember_index(root, room, &index);
        return Ok(vec![(room.clone(),INDEX_FIELD.to_owned(),current_room,result[0].1.clone()),
            (index_ref,"annotations".to_owned(),index_view,result[1].1.clone())]);
    }
    Err("shared-name room pointer changed repeatedly; reopen the name".into())
}

fn resolve_many_with(
    names: &[String],
    mut local: impl FnMut(&str) -> Result<Value>,
    mut read: impl FnMut(&Value, &str) -> Result<(Value, Value)>,
) -> Result<Vec<Value>> {
    let mut reads = BTreeMap::<(String, String, String, String, String), (Value, Value)>::new();
    names.iter().map(|name| {
        let chain = name.rsplit_once('/').map(|(room, _)| room).unwrap_or(name);
        resolve_with(name, &mut local, |reference, field| {
            let key = (chain.to_owned(), member(reference, "kind")?.to_owned(),
                member(reference, "target")?.to_owned(),
                member(reference, "observeCapability")?.to_owned(), field.to_owned());
            if let Some(retained) = reads.get(&key) { return Ok(retained.clone()); }
            let result = read(reference, field)?;
            reads.insert(key, result.clone());
            Ok(result)
        })
    }).collect()
}

/// Signed entries may be narrowed. Only an authenticated capability scope
/// that includes the discovery field can establish absence in that field.
fn visible_field(capability: &Value, reference: &Value, field: &str) -> Result<()> {
    let head = capability
        .get("head")
        .ok_or("signed capability lacks head")?;
    if member(head, "id")? != member(reference, "observeCapability")?
        || member(capability, "kind")? != member(reference, "kind")?
    {
        return Err("shared-name capability identity differs from signed query".into());
    }
    if let Some(fields) = head.get("fields").filter(|value| !value.is_null()) {
        let fields = fields.as_array().ok_or("capability fields are malformed")?;
        if !fields.iter().any(|value| value.as_str() == Some(field)) {
            return Err(format!("shared-name discovery does not cover {field}; a narrowed view cannot prove absence"));
        }
    }
    Ok(())
}

/// One native result binds coverage and narrowed payload to the same admitted
/// observation. Missing metadata refuses rather than implying an unrestricted grant.
fn scoped_resource(scoped: &Value, reference: &Value, field: &str) -> Result<Value> {
    if scoped.get("type").and_then(Value::as_str) != Some("resource-scope") {
        return Err("expected a source-owned resource scope view".into());
    }
    let capability = scoped.get("capability").ok_or("resource scope lacks its invoked capability")?;
    if capability.pointer("/head/fields").is_none() {
        return Err("resource scope lacks explicit field coverage".into());
    }
    visible_field(capability, reference, field)?;
    let view = scoped.get("resource").ok_or("resource scope lacks its narrowed resource")?;
    if view.get("type").and_then(Value::as_str) != Some("resource") {
        return Err("resource scope lacks a canonical narrowed resource view".into());
    }
    Ok(view.clone())
}

fn discovery_read(
    root: &Path,
    workspace: &Value,
    reference: &Value,
    field: &str,
) -> Result<(Value, Value)> {
    let reference = existing_authority(root, reference)?;
    let (scoped, at, _) = super::signed_view(root, workspace, &reference, "resource-scope")?;
    Ok((scoped_resource(&scoped, &reference, field)?, at))
}

/// A participant may hold a direct grant in addition to a room grant. Reuse
/// its authority only when the resolved identity matches exactly; a stale
/// same-spelled private hint never changes the shared target.
fn existing_authority(root: &Path, opened: &Value) -> Result<Value> {
    let mut result = opened.clone();
    let target = member(opened, "target")?;
    // The member named this exact reference for this exact target: its own
    // grant is the authority. Another reference to the same cell (an older
    // grant, revoked by a kick before a rejoin) must never replace it.
    if let Some(name) = opened.get("name").and_then(Value::as_str) {
        if super::local_reference(root, name).is_ok_and(|local| local["target"].as_str() == Some(target)) {
            return Ok(result);
        }
    }
    if let Some(local) = super::reference_for_target(root, target)? {
        if member(&local, "kind")? == member(opened, "kind")? {
            for field in [
                "observeCapability",
                "operationCapability",
                "controlCapability",
                "sealedIn",
            ] {
                if let Some(value) = local.get(field) {
                    result[field] = value.clone();
                }
            }
        }
    }
    Ok(result)
}

fn resolve_with(
    name: &str,
    mut local: impl FnMut(&str) -> Result<Value>,
    mut read: impl FnMut(&Value, &str) -> Result<(Value, Value)>,
) -> Result<Value> {
    validate_ref_name(name)?;
    let Some((room_name, leaf)) = name.rsplit_once('/') else {
        return local(name);
    };
    // Nested room paths must be resolved recursively by the integration adapter;
    // never confuse a local dotted filename with an authenticated namespace.
    let room = local(room_name)?;
    if member(&room, "kind")? != "object" || !room.get("room").is_some() {
        return Err("shared-name prefix is not an imported room reference".into());
    }
    let (room_view, room_at) = read(&room, INDEX_FIELD)?;
    let Some(index) = index_target(&room_view)? else {
        return absent_fallback(local(name)?, &room, leaf, None, &room_at);
    };
    let mut index_ref = room.clone();
    index_ref["name"] = json!(format!("{room_name}/index"));
    index_ref["target"] = json!(index);
    index_ref.as_object_mut().unwrap().remove("room");
    let (index_view, index_at) = read(&index_ref, "annotations")?;
    same_snapshot(&room_at, &index_at)?;
    // `index` is the room's canonical map, not a mutable entry in itself.
    if leaf == "index" {
        index_ref["sharedName"] = json!({"room":member(&room,"target")?,"index":index,
            "name":"index","roomRef":room,"indexRef":index_ref.clone(),"worldRoot":member(&index_at,"worldRoot")?,"height":member(&index_at,"height")?});
        return Ok(index_ref);
    }
    let names = bindings(&index_view)?;
    let Some(binding) = names.get(leaf) else {
        return absent_fallback(local(name)?, &room, leaf, Some(&index), &index_at);
    };
    // The room grant is a candidate capability, not new authority. The target's
    // own signed read and admission still decide whether it covers this target.
    let mut opened = room.clone();
    opened["name"] = json!(name);
    opened["kind"] = json!(binding.kind);
    opened["target"] = json!(binding.target);
    opened.as_object_mut().unwrap().remove("room");
    if room.get("room").and_then(Value::as_str) == Some("private") || room.get("private").is_some()
    {
        opened["sealedIn"] = json!(room_name);
    }
    opened["sharedName"] = json!({"room":member(&room,"target")?,"index":index,
        "name":leaf,"link":binding.link,"roomRef":room,"indexRef":index_ref,"worldRoot":member(&index_at,"worldRoot")?,
        "height":member(&index_at,"height")?});
    Ok(opened)
}

/// An absence decision is snapshot-bound too: a shared entry appearing before
/// the target read must not silently leave the client on its old private hint.
fn absent_fallback(
    mut opened: Value,
    room: &Value,
    name: &str,
    index: Option<&str>,
    at: &Value,
) -> Result<Value> {
    let index_ref = index.map(|id| {
        let mut reference = room.clone();
        reference["target"] = json!(id);
        reference.as_object_mut().unwrap().remove("room");
        reference
    });
    opened["sharedName"] = json!({"room":member(room,"target")?,"name":name,"index":index,
        "roomRef":room,"indexRef":index_ref,
        "fallback":"private","worldRoot":member(at,"worldRoot")?,"height":member(at,"height")?});
    Ok(opened)
}

/// Verify a target read belongs to the snapshot that resolved its shared name.
/// Exact recovery never calls this: it works on the already signed target ID.
pub(crate) fn check_opened(reference: &Value, challenge: &Value) -> Result<()> {
    if let Some(discovery) = reference.get("sharedName") {
        same_snapshot(discovery, challenge)?;
    }
    Ok(())
}

/// These are candidates only: the batch independently admits their current
/// invoked capabilities. Retained discovery is never authority for later use.
pub(crate) fn guard_references(reference: &Value) -> Result<Vec<Value>> {
    let discovery = reference.get("sharedName").ok_or("reference lacks shared discovery")?;
    let room = discovery.get("roomRef").ok_or("shared-name guard lacks its room reference")?;
    if member(room,"kind")? != "object" || member(room,"target")? != member(discovery,"room")? {
        return Err("shared-name room guard differs from discovery".into());
    }
    let mut guards = vec![room.clone()];
    if let Some(index) = discovery.get("index").filter(|v| !v.is_null()) {
        let index_ref = discovery.get("indexRef").ok_or("shared-name guard lacks its index reference")?;
        if member(index_ref,"kind")? != "object" || index_ref.get("target") != Some(index) {
            return Err("shared-name index guard differs from discovery".into());
        }
        guards.push(index_ref.clone());
    }
    for guard in &guards {
        if guard.get("sharedName").is_some() {
            return Err("shared-name guard cannot recursively claim discovery".into());
        }
    }
    Ok(guards)
}

/// Validate the exact pinned name/absence decision against dependencies read
/// in the same current native batch as the opened target. Only the discovery
/// projections are compared; unrelated accepted writes need not stand still.
pub(crate) fn check_opened_views(reference: &Value, guards: &[Value], views: &[Value]) -> Result<()> {
    let expected = guard_references(reference)?;
    if guards != expected || views.len() != guards.len() {
        return Err("shared-name read lacks its exact discovery guards".into());
    }
    let discovery = &reference["sharedName"];
    let room = scoped_resource(&views[0],&guards[0],INDEX_FIELD)?;
    let index = index_target(&room)?;
    if index.as_deref() != discovery.get("index").and_then(Value::as_str) {
        return Err("shared-name room pointer changed; reopen the name".into());
    }
    let leaf = member(discovery,"name")?;
    let Some(index) = index else {
        if member(discovery,"fallback")? == "private" { return Ok(()); }
        return Err("shared-name index disappeared; reopen the name".into());
    };
    let names = bindings(&scoped_resource(&views[1],&guards[1],"annotations")?)?;
    if discovery.get("fallback").and_then(Value::as_str) == Some("private") {
        if !names.contains_key(leaf) { return Ok(()); }
        return Err("shared name now exists; reopen the name".into());
    }
    if leaf == "index" {
        if member(reference,"kind")? == "object" && member(reference,"target")? == index {
            return Ok(());
        }
        return Err("shared-name index target differs".into());
    }
    let binding = names.get(leaf).ok_or("shared name disappeared; reopen the name")?;
    if binding.kind != member(reference,"kind")? || binding.target != member(reference,"target")?
        || binding.link != member(discovery,"link")? {
        return Err("shared name changed; reopen the name".into());
    }
    Ok(())
}

/// Law for an index document. Management verbs remain subject to their own
/// capability; content writes must preserve unique live names. Other documents
/// do not acquire this restriction merely because they contain links.
pub(crate) fn index_law() -> Value {
    json!({"type":"any","predicates":[
        {"type":"not","predicate":{"type":"eq","slot":"request/verb","value":"2"}},
        {"type":"eq","slot":"content/names/unique","value":"1"}]})
}

/// Retain a target-pinned private reference for this command. Its random name
/// is never used as a public namespace; the command journal records its exact
/// source, preventing a retry from consulting a renamed shared binding.
fn pin(root: &Path, reference: &Value) -> Result<String> {
    let name = format!("name-open-{}", super::random_nonce()?);
    let mut reference = reference.clone();
    reference["name"] = json!(name);
    // Replanning uses the same object identity with a new target read. The
    // initial discovery check happened before this pin was retained.
    reference
        .as_object_mut()
        .ok_or("reference is not an object")?
        .remove("sharedName");
    crate::create_private(
        &root.join("refs").join(format!("{name}.json")),
        &serde_json::to_vec(&reference).map_err(|e| e.to_string())?,
    )?;
    Ok(name)
}

fn json_file(path: &Path, value: &Value) -> Result<()> {
    crate::create_private(
        path,
        &serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?,
    )
}

fn finish(root: &Path, workspace: &Value, id: &str, request: &Value) -> Result<()> {
    let source = root
        .join("sources")
        .join(format!("shared-name-{id}.request.json"));
    if source.exists() {
        if super::bounded_json(&source)? != *request {
            return Err("retained naming request changed".into());
        }
    } else {
        json_file(&source, request)?;
    }
    let proposal = root.join("proposals").join(id);
    if !proposal.join("proposal.json").exists() {
        super::propose(root, workspace, &source, id, None)?;
    }
    if super::bounded_json(&proposal.join("request.json"))? != *request {
        return Err("naming operation ID belongs to a different retained proposal".into());
    }
    let summary = super::bounded_json(&proposal.join("proposal.json"))?;
    let intent = std::fs::read(proposal.join("intent.json")).map_err(|e| e.to_string())?;
    if member(&summary, "proposalId")? != id
        || member(&summary, "intentSha256")? != format!("{:x}", Sha256::digest(&intent))
    {
        return Err("naming proposal identity or intent digest differs".into());
    }
    let attempt = root.join("attempts").join(id);
    if attempt.join("call.bin").exists() {
        if std::fs::read(attempt.join("intent.json")).map_err(|e| e.to_string())? != intent {
            return Err("naming attempt does not contain this exact retained proposal".into());
        }
        return super::recover(root, &attempt);
    }
    if attempt.exists() {
        return Err(format!(
            "naming attempt {} exists without complete signed bytes; inspect it before recovery",
            attempt.display()
        ));
    }
    super::submit_intent(
        root,
        workspace,
        &proposal.join("intent.json"),
        "intent",
        false,
        Some(&attempt),
    )
}

/// User-facing namespace operations all use ordinary document/room admission.
/// The retained request is inspected before any network read on a retry.
pub(crate) fn command(
    root: &Path,
    workspace: &Value,
    op: &str,
    room_name: &str,
    name: Option<&str>,
    to: Option<&str>,
    id: Option<&str>,
) -> Result<()> {
    validate_ref_name(room_name)?;
    if op == "resolve" {
        return crate::print_json(&resolve(root, workspace, room_name)?);
    }
    let id = id.ok_or("shared-name writes require --id")?;
    validate_name(id)?;
    let command = json!({"op":op,"room":room_name,"name":name,"to":to});
    let command_path = root
        .join("sources")
        .join(format!("shared-name-{id}.command.json"));
    let retained = root
        .join("sources")
        .join(format!("shared-name-{id}.request.json"));
    if command_path.exists() {
        if super::bounded_json(&command_path)? != command {
            return Err("naming operation ID already belongs to a different command".into());
        }
        if retained.exists() {
            return finish(root, workspace, id, &super::bounded_json(&retained)?);
        }
        return Err("naming command stopped before retaining its prepared request; use a new ID after inspecting it".into());
    }
    if retained.exists()
        || root.join("proposals").join(id).exists()
        || root.join("attempts").join(id).exists()
    {
        return Err("naming operation ID is already used by another workspace operation".into());
    }
    // Verify all input before claiming the operation identity.
    let mut room = super::reference(root, room_name)?;
    if member(&room, "kind")? != "object" || room.get("room").is_none() {
        return Err("name operation requires a room reference".into());
    }
    let request = match op {
        "attach" => {
            let index = existing_authority(root, &super::reference(root, to.ok_or("attach requires --to INDEX")?)?)?;
            // The room's pointer and the new index, one native image.
            let reader = existing_authority(root, &room)?;
            let pair = super::signed_views(root, workspace, &[reader.clone(), index.clone()], "resource-scope")?;
            let room_view = scoped_resource(&pair[0].0, &reader, INDEX_FIELD)?;
            let index_view = scoped_resource(&pair[1].0, &index, "annotations")?;
            same_snapshot(&pair[0].1, &pair[1].1)?;
            if super::cell_storage(index_view.get("cell").ok_or("index lacks cell")?)? != "content"
            {
                return Err("room index must be a content document".into());
            }
            bindings(&index_view)?;
            let value = member(&index, "target")?;
            let old = room_view
                .pointer("/cell/entries")
                .and_then(Value::as_array)
                .ok_or("room lacks entries")?
                .iter()
                .find(|row| row.pointer("/key/field").and_then(Value::as_str) == Some(INDEX_FIELD));
            let action = match old {
                None => {
                    json!({"type":"create","key":{"type":"object","field":INDEX_FIELD},"value":value})
                }
                Some(old) => {
                    json!({"type":"write","key":{"type":"object","field":INDEX_FIELD},"value":value,"expected":member(old,"value")?})
                }
            };
            let pinned = pin(root, &room)?;
            json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                "targets":[{"name":pinned,"payload":{"type":"scalar","actions":[action]}}]})
        }
        "bind" | "rename" | "unbind" => {
            let leaf = name.ok_or("name operation requires --name")?;
            validate_name(leaf)?;
            if leaf == "index" {
                return Err("index is the reserved room map name".into());
            }
            // The room's pointer and its index's names, one native image.
            let chain = coherent_discovery(root, workspace, &room)?;
            let Some((index_ref, _, index_view, index_at)) = chain.get(1).cloned() else {
                return Err("room has no index document".into());
            };
            room = index_ref;
            let names = bindings(&index_view)?;
            let mut actions = vec![];
            if op == "bind" {
                // Do not hide duplicate refusal behind a client precheck: the
                // source-owned index law judges the final live bindings.
                let target_ref = super::reference(root, to.ok_or("bind requires --to TARGET")?)?;
                let (_, target_at, _) =
                    super::signed_view(root, workspace, &target_ref, "resource")?;
                same_snapshot(&index_at, &target_at)?;
                actions.push(json!({"type":"link","link":super::random_nonce()?,"source":null,"relation":"0",
                    "target":target(leaf,member(&target_ref,"kind")?,member(&target_ref,"target")?)?}));
            } else {
                let previous = names.get(leaf).ok_or("shared name does not exist")?;
                actions.push(json!({"type":"unlink","link":previous.link}));
                if op == "rename" {
                    let new = to.ok_or("rename requires --to NEW-NAME")?;
                    if new == "index" {
                        return Err("index is the reserved room map name".into());
                    }
                    actions.push(json!({"type":"link","link":super::random_nonce()?,"source":null,"relation":"0",
                        "target":target(new,&previous.kind,&previous.target)?}));
                }
            }
            let pinned = pin(root, &room)?;
            json!({"type":"minidregg-workspace-proposal-v1","action":"invoke",
                "targets":[{"name":pinned,"payload":{"type":"content","actions":actions}}]})
        }
        _ => return Err("shared-name operation is attach, bind, rename, unbind or resolve".into()),
    };
    json_file(&command_path, &command)?;
    finish(root, workspace, id, &request)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn link(name: &str, id: &str) -> Value {
        json!({"type":"link","id":id,"source":null,"relation":"0","tombstonedAt":null,
            "target":target(name,"object","42").unwrap()})
    }
    fn view(links: Vec<Value>) -> Value {
        json!({"cell":{"entries":links}})
    }
    fn room() -> Value {
        json!({"name":"lab","kind":"object","target":"10","room":"open",
        "observeCapability":"7","operationCapability":"8"})
    }
    fn at(root: &str) -> Value {
        json!({"worldRoot":root,"height":"50"})
    }
    fn scope(reference: &Value, mut resource: Value) -> Value {
        resource["type"] = json!("resource");
        json!({"type":"resource-scope","capability":{"kind":reference["kind"],
            "head":{"id":reference["observeCapability"],"fields":null}},
            "resource":resource})
    }
    fn opened_guard(leaf: &str, entries: Vec<Value>) -> (Value,Vec<Value>,Vec<Value>) {
        let opened = resolve_with(&format!("lab/{leaf}"), |_| Ok(room()), |reference,_| {
            Ok((if reference["target"] == "10" {
                view(vec![json!({"key":{"field":INDEX_FIELD},"value":"11"})])
            } else { view(entries.clone()) },at("99")))
        }).unwrap();
        let guards = guard_references(&opened).unwrap();
        let views = vec![scope(&guards[0],view(vec![
            json!({"key":{"field":INDEX_FIELD},"value":"11"})])),
            scope(&guards[1],view(entries))];
        (opened,guards,views)
    }
    #[test]
    fn opened_target_accepts_current_unchanged_projection_after_unrelated_writes() {
        let (mut opened,guards,views) = opened_guard("board",vec![link("board","1")]);
        // Historic discovery coordinates are deliberately different; only the
        // current same-batch admitted dependency projections establish binding.
        opened["sharedName"]["worldRoot"] = json!("old-head");
        opened["sharedName"]["height"] = json!("1");
        assert!(check_opened_views(&opened,&guards,&views).is_ok());
    }
    #[test]
    fn opened_target_refuses_retarget_rename_removal_pointer_or_narrow_scope() {
        let (opened,guards,views) = opened_guard("board",vec![link("board","1")]);
        let mut changed = views.clone();
        changed[1]["resource"]["cell"]["entries"][0]["target"] = target("board","object","43").unwrap();
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
        changed = views.clone();
        changed[1]["resource"]["cell"]["entries"][0]["id"] = json!("2");
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
        changed = views.clone();
        changed[1]["resource"]["cell"]["entries"] = json!([]);
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
        changed = views.clone();
        changed[0]["resource"]["cell"]["entries"][0]["value"] = json!("12");
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
        changed = views.clone();
        changed[1]["capability"]["head"]["fields"] = json!(["1010"]);
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
        changed = views.clone();
        changed[1]["capability"]["head"]["id"] = json!("99");
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
    }
    #[test]
    fn current_absence_guard_refuses_new_shared_binding_and_missing_guard() {
        let (opened,guards,views) = opened_guard("board",vec![]);
        assert!(check_opened_views(&opened,&guards,&views).is_ok());
        let mut changed = views.clone();
        changed[1]["resource"]["cell"]["entries"] = json!([link("board","1")]);
        assert!(check_opened_views(&opened,&guards,&changed).is_err());
        assert!(check_opened_views(&opened,&guards[..1],&views[..1]).is_err());
        let mut legacy = opened.clone();
        legacy["sharedName"].as_object_mut().unwrap().remove("roomRef");
        assert!(guard_references(&legacy).is_err());
    }
    #[test]
    fn naming_id_cannot_recover_another_workspace_operation() {
        let root = std::env::temp_dir().join(format!(
            "mini-names-collision-{}",
            super::super::random_nonce().unwrap()
        ));
        std::fs::create_dir_all(root.join("proposals").join("used")).unwrap();
        let error = command(
            &root,
            &Value::Null,
            "bind",
            "lab",
            Some("board"),
            Some("paper"),
            Some("used"),
        )
        .unwrap_err();
        assert!(error.contains("already used by another workspace operation"));
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn exact_recovery_checks_proposal_bytes_before_network() {
        let root = std::env::temp_dir().join(format!(
            "mini-names-exact-{}",
            super::super::random_nonce().unwrap()
        ));
        for dir in ["sources", "proposals/names", "attempts/names"] {
            std::fs::create_dir_all(root.join(dir)).unwrap();
        }
        let request = json!({"type":"test-request"});
        json_file(&root.join("proposals/names/request.json"), &request).unwrap();
        std::fs::write(root.join("proposals/names/intent.json"), b"original intent").unwrap();
        json_file(
            &root.join("proposals/names/proposal.json"),
            &json!({"proposalId":"names",
            "intentSha256":format!("{:x}",Sha256::digest(b"original intent"))}),
        )
        .unwrap();
        std::fs::write(root.join("attempts/names/call.bin"), b"other call").unwrap();
        std::fs::write(root.join("attempts/names/intent.json"), b"different intent").unwrap();
        assert!(finish(&root, &Value::Null, "names", &request)
            .unwrap_err()
            .contains("does not contain this exact retained proposal"));
        std::fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn same_snapshot_scope_requires_exact_grant_and_explicit_coverage() {
        let reference = room();
        let mut scoped = json!({"type":"resource-scope",
            "capability":{"kind":"object","head":{"id":"7","fields":["1010"]}},
            "resource":{"type":"resource","cell":{"entries":[]}}});
        assert!(scoped_resource(&scoped, &reference, INDEX_FIELD).is_ok());
        assert!(scoped_resource(&scoped, &reference, "annotations").is_err());
        scoped["capability"]["head"]["fields"] = Value::Null;
        assert!(scoped_resource(&scoped, &reference, "annotations").is_ok());
        scoped["capability"]["head"]["id"] = json!("8");
        assert!(scoped_resource(&scoped, &reference, INDEX_FIELD).is_err());
        scoped["capability"]["head"]["id"] = json!("7");
        scoped["capability"]["head"].as_object_mut().unwrap().remove("fields");
        assert!(scoped_resource(&scoped, &reference, INDEX_FIELD).is_err());
    }

    #[test]
    fn narrowed_signed_view_cannot_prove_absence() {
        let reference = room();
        let mut cap = json!({"kind":"object","head":{"id":"7","fields":["2"]}});
        assert!(visible_field(&cap, &reference, INDEX_FIELD).is_err());
        cap["head"]["fields"] = json!(["1010"]);
        assert!(visible_field(&cap, &reference, INDEX_FIELD).is_ok());
        assert!(visible_field(&cap, &reference, "annotations").is_err());
        cap["head"].as_object_mut().unwrap().remove("fields");
        assert!(visible_field(&cap, &reference, "annotations").is_ok());
        cap["head"]["id"] = json!("8");
        assert!(visible_field(&cap, &reference, "annotations").is_err());
    }
    #[test]
    fn opened_target_rejects_a_different_discovery_snapshot() {
        let reference = json!({"target":"42","sharedName":at("99")});
        assert!(check_opened(&reference, &at("99")).is_ok());
        assert!(check_opened(&reference, &at("100")).is_err());
    }
    #[test]
    fn codec_has_no_path_alias_or_name_normalization() {
        for invalid in ["a.b", "a/b", "", "a%2Fb", "../lab"] {
            assert!(target(invalid, "object", "42").is_err());
        }
        assert_ne!(
            target("Board", "object", "42").unwrap(),
            target("board", "object", "42").unwrap()
        );
        assert!(target("board", "object", "042").is_err());
        assert!(target("board", "alien", "42").is_err());
    }
    #[test]
    fn duplicate_live_binding_refuses_even_same_target() {
        assert!(bindings(&view(vec![link("board", "1"), link("board", "2")])).is_err());
        let mut retired = link("board", "1");
        retired["tombstonedAt"] = json!("3");
        assert_eq!(
            bindings(&view(vec![retired, link("board", "2")]))
                .unwrap()
                .len(),
            1
        );
    }
    #[test]
    fn renamed_binding_accepts_native_full_width_retirement() {
        let mut retired = link("board", "1");
        retired["tombstonedAt"] =
            json!("105864688476342976361059645019308680758459110999958598611326832182121287435193");
        let names = bindings(&view(vec![retired.clone(), link("current", "2")])).unwrap();
        assert!(!names.contains_key("board"));
        assert_eq!(names["current"].target, "42");
        for malformed in ["01", "-1", "", "not-an-event"] {
            retired["tombstonedAt"] = json!(malformed);
            assert!(bindings(&view(vec![retired.clone()])).is_err());
        }
    }
    #[test]
    fn malformed_namespace_never_means_absence() {
        let mut bad = link("other", "1");
        bad["target"]["path"] = json!(crate::hex(b"object/042"));
        assert!(bindings(&view(vec![bad])).is_err());
        let mut bad = link("board", "1");
        bad.as_object_mut().unwrap().remove("tombstonedAt");
        assert!(bindings(&view(vec![bad])).is_err());
    }
    #[test]
    fn independent_room_chains_accept_different_heads_without_cross_reusing_index() {
        let names = ["lab/board", "other/board", "lab/notes", "other/notes"].map(str::to_owned);
        let mut reads = 0;
        let opened = resolve_many_with(&names, |name| {
            let mut value = room();
            if name == "other" { value["target"] = json!("20"); }
            Ok(value)
        }, |reference, _| {
            reads += 1;
            // The rooms deliberately share an index ID and grant: its cached
            // head from lab must not be paired with other's later room head.
            Ok((if reference["target"] == "10" || reference["target"] == "20" {
                view(vec![json!({"key":{"field":"1010"},"value":"11"})])
            } else { view(vec![link("board", "1"), link("notes", "2")]) },
                at(if reads <= 2 { "99" } else { "100" })))
        }).unwrap();
        assert_eq!(reads, 4);
        assert_eq!(opened[0]["sharedName"]["worldRoot"], "99");
        assert_eq!(opened[1]["sharedName"]["worldRoot"], "100");
        assert_eq!(opened[2]["sharedName"]["worldRoot"], "99");
        assert_eq!(opened[3]["sharedName"]["worldRoot"], "100");
    }

    #[test]
    fn listing_reuses_one_snapshot_and_refuses_moved_or_revoked_discovery() {
        let names = ["lab/board", "lab/notes", "lab/index"].map(str::to_owned);
        let mut reads = 0;
        let opened = resolve_many_with(&names, |_| Ok(room()), |reference, _| {
            reads += 1;
            Ok((if reference["target"] == "10" {
                view(vec![json!({"key":{"field":"1010"},"value":"11"})])
            } else { view(vec![link("board", "1"), link("notes", "2")]) }, at("99")))
        }).unwrap();
        assert_eq!(reads, 2);
        assert_eq!(opened.len(), 3);
        assert!(opened.iter().all(|value| value["sharedName"]["worldRoot"] == "99"));
        assert!(resolve_many_with(&names, |_| Ok(room()), |_, _| Err("revoked".into())).is_err());
        let mut reads = 0;
        assert!(resolve_many_with(&names, |_| Ok(room()), |reference, _| {
            reads += 1;
            Ok((if reference["target"] == "10" {
                view(vec![json!({"key":{"field":"1010"},"value":"11"})])
            } else { view(vec![link("board", "1")]) }, at(if reads == 1 { "99" } else { "100" })))
        }).is_err());
    }

    #[test]
    fn shared_entry_wins_without_local_child_and_keeps_target_authority() {
        let mut reads = 0;
        let opened = resolve_with(
            "lab/board",
            |name| {
                assert_eq!(name, "lab");
                Ok(room())
            },
            |_, _| {
                reads += 1;
                Ok((
                    if reads == 1 {
                        view(vec![json!({"key":{"field":"1010"},"value":"11"})])
                    } else {
                        view(vec![link("board", "5")])
                    },
                    at("99"),
                ))
            },
        )
        .unwrap();
        assert_eq!(opened["target"], "42");
        assert_eq!(opened["observeCapability"], "7");
        assert_eq!(opened["operationCapability"], "8");
        assert_eq!(opened["sharedName"]["index"], "11");
    }
    #[test]
    fn unauthorized_or_moved_discovery_does_not_use_private_fallback() {
        let local = |name: &str| {
            assert_eq!(name, "lab");
            Ok(room())
        };
        assert!(resolve_with("lab/board", local, |_, _| Err("no grant".into())).is_err());
        let mut reads = 0;
        assert!(resolve_with("lab/board", local, |_, _| {
            reads += 1;
            Ok((
                if reads == 1 {
                    view(vec![json!({"key":{"field":"1010"},"value":"11"})])
                } else {
                    view(vec![link("board", "1")])
                },
                at(if reads == 1 { "99" } else { "100" }),
            ))
        })
        .is_err());
    }
    #[test]
    fn only_authenticated_absence_allows_private_hint() {
        let opened = resolve_with(
            "lab/board",
            |name| {
                if name == "lab" {
                    Ok(room())
                } else {
                    Ok(json!({"target":"private-hint"}))
                }
            },
            |_, _| Ok((view(vec![]), at("99"))),
        )
        .unwrap();
        assert_eq!(opened["target"], "private-hint");
        assert_eq!(opened["sharedName"]["fallback"], "private");
        assert!(check_opened(&opened, &at("99")).is_ok());
        assert!(check_opened(&opened, &at("100")).is_err());
    }

    /// After a kick and a rejoin a member holds two references to one room:
    /// the old one (revoked grant) and the new one. Naming the new one uses
    /// its own grant; a derived reference (the index) still borrows a direct
    /// grant for its exact target.
    #[test]
    fn named_reference_keeps_its_own_grant_over_an_older_one_for_the_same_room() {
        let root = std::env::temp_dir().join(format!("mini-shared-rejoin-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        super::super::make_private_dir(&root).unwrap();
        super::super::make_private_dir(&root.join("refs")).unwrap();
        let write = |name: &str, target: &str, cap: &str| {
            crate::create_private(&root.join("refs").join(format!("{}.json", super::super::ref_file(name))),
                &serde_json::to_vec(&json!({"type":"minidregg-participant-reference-v1","name":name,"kind":"object",
                    "target":target,"observeCapability":cap,"operationCapability":cap,"controlCapability":null,
                    "room":"member"})).unwrap()).unwrap();
        };
        write("lab", "10", "100");
        write("lab-again", "10", "200");
        write("index-direct", "11", "300");
        let again = super::super::local_reference(&root, "lab-again").unwrap();
        assert_eq!(existing_authority(&root, &again).unwrap()["observeCapability"], "200");
        let old = super::super::local_reference(&root, "lab").unwrap();
        assert_eq!(existing_authority(&root, &old).unwrap()["observeCapability"], "100");
        let mut index = again.clone();
        index["target"] = json!("11");
        assert_eq!(existing_authority(&root, &index).unwrap()["observeCapability"], "300");
        std::fs::remove_dir_all(&root).unwrap();
    }
}
