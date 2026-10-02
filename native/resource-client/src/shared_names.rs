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
    let opened = resolve_with(
        name,
        |name| super::local_reference(root, name),
        |reference, field| discovery_read(root, workspace, reference, field),
    )?;
    existing_authority(root, &opened)
}

/// Resolve a listing with one immutable discovery snapshot per room chain.
/// Repeated aliases reuse only that chain's admitted reads. Independent rooms
/// may observe different heads; no retained read survives this command.
pub(crate) fn resolve_many(root: &Path, workspace: &Value, names: &[String]) -> Result<Vec<Value>> {
    resolve_many_with(names, |name| super::local_reference(root, name),
        |reference, field| discovery_read(root, workspace, reference, field))?
        .into_iter().map(|opened| existing_authority(root, &opened)).collect()
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
    if let Some(local) = super::reference_for_target(root, member(opened, "target")?)? {
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
            "name":"index","worldRoot":member(&index_at,"worldRoot")?,"height":member(&index_at,"height")?});
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
        "name":leaf,"link":binding.link,"worldRoot":member(&index_at,"worldRoot")?,
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
    opened["sharedName"] = json!({"room":member(room,"target")?,"name":name,"index":index,
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
    super::private_file(
        &root.join("refs").join(format!("{name}.json")),
        &serde_json::to_vec(&reference).map_err(|e| e.to_string())?,
    )?;
    Ok(name)
}

fn json_file(path: &Path, value: &Value) -> Result<()> {
    super::private_file(
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
    let (room_view, room_at) = discovery_read(root, workspace, &room, INDEX_FIELD)?;
    let request = match op {
        "attach" => {
            let index = super::reference(root, to.ok_or("attach requires --to INDEX")?)?;
            let (index_view, index_at) = discovery_read(root, workspace, &index, "annotations")?;
            same_snapshot(&room_at, &index_at)?;
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
            let index = index_target(&room_view)?.ok_or("room has no index document")?;
            room["target"] = json!(index);
            room.as_object_mut().unwrap().remove("room");
            room = existing_authority(root, &room)?;
            let (index_view, index_at) = discovery_read(root, workspace, &room, "annotations")?;
            same_snapshot(&room_at, &index_at)?;
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
}
