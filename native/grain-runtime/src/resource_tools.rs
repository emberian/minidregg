//! Operator-named, signed reads of shared Mini resources. This module only
//! selects a fixed observe grant and invokes the native client; the Lean host
//! checks the current grant and materializes the resource view.
use crate::{write_new, Config, PublicationGrant, Result, ToolTask};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::fs;
use std::path::Path;
use std::process::{Command, Stdio};

// A complete content page can include the fn consumer's typed inbox atom and
// exact carrier. Refuse larger results explicitly instead of returning a
// prefix. The raw JSON presentation repeats whole-page and per-entry bytes;
// named fn reads ask Lean for its typed presentation of the same signed view.
const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;
// The typed view may be larger, but the returned JSON is nested as MCP text
// before reaching the ACP peer. Leave room for that escaping and its envelope.
const MAX_TOOL_RESULT_BYTES: usize = 256 * 1024;
const MAX_BIRTH_SOURCE_BYTES: usize = 256 * 1024;

/// An operator-approved, repeatable family of new content objects. The
/// controller allocates fresh IDs within these bounded namespaces; Hermes
/// selects only the family name. The native factory still derives and checks
/// the empty content page, owner/control grants, policy record, fee and absent
/// roots. The predicate is operator-pinned source input, never an MCP argument.
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct AllowedBirthFamily {
    pub name: String,
    pub genesis: Value,
    pub template: Value,
    pub predicate: Value,
    pub factory_target: String,
    pub factory_observe_capability: String,
    pub payer_account: String,
    pub payer_capability: String,
    pub payer_observe_capability: String,
    pub tariff_base: String,
    pub tariff_per_birth: String,
    pub target_start: String,
    pub owner_capability_start: String,
    pub control_capability_start: String,
    pub max_births: u16,
    pub max_result_bytes: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct BornResource {
    pub name: String,
    pub kind: String,
    pub target: String,
    pub owner_capability: String,
    pub control_capability: String,
    pub max_result_bytes: usize,
}

fn bounded_id(start: &str, offset: u16, label: &str) -> Result<String> {
    crate::decimal(start, label)?;
    let value = start
        .parse::<u64>()
        .map_err(|_| format!("{label} exceeds the bounded birth namespace"))?;
    value
        .checked_add(u64::from(offset))
        .map(|id| id.to_string())
        .ok_or_else(|| format!("{label} birth namespace overflows"))
}

fn id_range(start: &str, count: u16, label: &str) -> Result<(u64, u64)> {
    let first = start
        .parse::<u64>()
        .map_err(|_| format!("{label} exceeds the bounded birth namespace"))?;
    let last = bounded_id(start, count - 1, label)?
        .parse::<u64>()
        .map_err(|_| format!("{label} exceeds the bounded birth namespace"))?;
    Ok((first, last))
}

fn overlaps(left: (u64, u64), right: (u64, u64)) -> bool {
    left.0 <= right.1 && right.0 <= left.1
}

pub(super) fn validate_birth_families(
    families: &[AllowedBirthFamily],
    reads: &[AllowedResourceRead],
    publications: &[PublicationGrant],
    peer_targets: &[&str],
    peer_capabilities: &[&str],
) -> Result<()> {
    if families.len() > 8 {
        return Err("at most eight resource birth families may be configured".into());
    }
    for (index, family) in families.iter().enumerate() {
        if family.name.is_empty()
            || family.name.len() > 32
            || !family
                .name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
            || families[..index]
                .iter()
                .any(|prior| prior.name == family.name)
            || reads.iter().any(|read| read.name == family.name)
        {
            return Err("resource birth family needs a unique alphanumeric name".into());
        }
        if family.max_births == 0 || family.max_births > 1024 {
            return Err(format!("{} maxBirths must be 1..1024", family.name));
        }
        if family.max_result_bytes == 0 || family.max_result_bytes > MAX_RESULT_BYTES {
            return Err(format!(
                "{} maxResultBytes must be 1..{MAX_RESULT_BYTES}",
                family.name
            ));
        }
        for (value, label) in [
            (&family.factory_target, "factoryTarget"),
            (
                &family.factory_observe_capability,
                "factoryObserveCapability",
            ),
            (&family.payer_account, "payerAccount"),
            (&family.payer_capability, "payerCapability"),
            (&family.payer_observe_capability, "payerObserveCapability"),
            (&family.tariff_base, "tariffBase"),
            (&family.tariff_per_birth, "tariffPerBirth"),
            (&family.target_start, "targetStart"),
            (&family.owner_capability_start, "ownerCapabilityStart"),
            (&family.control_capability_start, "controlCapabilityStart"),
        ] {
            crate::decimal(value, label)?;
        }
        if family.tariff_base == "0" {
            return Err(format!("{} tariffBase must be positive", family.name));
        }
        if !family.genesis.is_object()
            || !family.template.is_object()
            || !family.predicate.is_object()
        {
            return Err(format!(
                "{} genesis, template and predicate must be objects",
                family.name
            ));
        }
        let template_len = serde_json::to_vec(&json!({
            "genesis":family.genesis,"template":family.template,
            "predicate":family.predicate
        }))
        .map_err(|e| e.to_string())?
        .len();
        if template_len > MAX_BIRTH_SOURCE_BYTES / 2 {
            return Err(format!(
                "{} birth source template exceeds bound",
                family.name
            ));
        }
        for (start, label) in [
            (&family.target_start, "targetStart"),
            (&family.owner_capability_start, "ownerCapabilityStart"),
            (&family.control_capability_start, "controlCapabilityStart"),
        ] {
            bounded_id(start, family.max_births - 1, label)?;
        }
        let ranges = [
            id_range(&family.target_start, family.max_births, "targetStart")?,
            id_range(
                &family.owner_capability_start,
                family.max_births,
                "ownerCapabilityStart",
            )?,
            id_range(
                &family.control_capability_start,
                family.max_births,
                "controlCapabilityStart",
            )?,
        ];
        let occupied_targets = peer_targets
            .iter()
            .copied()
            .chain(reads.iter().map(|read| read.target.as_str()))
            .chain(publications.iter().map(|grant| grant.target.as_str()))
            .chain(families.iter().flat_map(|configured| {
                [
                    configured.factory_target.as_str(),
                    configured.payer_account.as_str(),
                ]
            }));
        let occupied_capabilities =
            peer_capabilities
                .iter()
                .copied()
                .chain(reads.iter().map(|read| read.observe_capability.as_str()))
                .chain(publications.iter().flat_map(|grant| {
                    [grant.capability.as_str(), grant.observe_capability.as_str()]
                }))
                .chain(families.iter().flat_map(|configured| {
                    [
                        configured.factory_observe_capability.as_str(),
                        configured.payer_capability.as_str(),
                        configured.payer_observe_capability.as_str(),
                    ]
                }));
        let in_range = |id: &str, range: (u64, u64)| {
            id.parse::<u64>()
                .is_ok_and(|value| range.0 <= value && value <= range.1)
        };
        if occupied_targets
            .into_iter()
            .any(|id| in_range(id, ranges[0]))
            || occupied_capabilities
                .into_iter()
                .any(|id| in_range(id, ranges[1]) || in_range(id, ranges[2]))
        {
            return Err(format!(
                "{} birth namespace collides with a configured target or capability",
                family.name
            ));
        }
        if overlaps(ranges[1], ranges[2]) {
            return Err(format!(
                "{} owner and control capability namespaces overlap",
                family.name
            ));
        }
        for ordinal in 0..family.max_births {
            let name = format!("{}-{ordinal}", family.name);
            if reads.iter().any(|read| read.name == name) {
                return Err(format!(
                    "{name} would collide with a configured resource read"
                ));
            }
        }
        for prior in &families[..index] {
            let prior_target = id_range(&prior.target_start, prior.max_births, "targetStart")?;
            let prior_owner = id_range(
                &prior.owner_capability_start,
                prior.max_births,
                "ownerCapabilityStart",
            )?;
            let prior_control = id_range(
                &prior.control_capability_start,
                prior.max_births,
                "controlCapabilityStart",
            )?;
            if overlaps(ranges[0], prior_target)
                || [ranges[1], ranges[2]]
                    .iter()
                    .any(|range| overlaps(*range, prior_owner) || overlaps(*range, prior_control))
            {
                return Err(format!(
                    "{} birth namespace overlaps {}",
                    family.name, prior.name
                ));
            }
        }
    }
    Ok(())
}

pub(super) fn select_birth<'a>(
    families: &'a [AllowedBirthFamily],
    arguments: &Value,
) -> Result<&'a AllowedBirthFamily> {
    let object = arguments
        .as_object()
        .ok_or("mini_create_resource arguments must be an object")?;
    if object.len() != 1 {
        return Err("mini_create_resource requires exactly one family argument".into());
    }
    let name = object
        .get("family")
        .and_then(Value::as_str)
        .ok_or("mini_create_resource family must be a string")?;
    families
        .iter()
        .find(|family| family.name == name)
        .ok_or_else(|| format!("resource birth family {name} is not allowlisted"))
}

/// Controller bookkeeping bound for one resource in this v1 family. The
/// source-owned tariff and native admission decide the actual settlement;
/// this calculation never authorizes a Mini transition.
pub(super) fn planned_birth_charge(family: &AllowedBirthFamily) -> Result<String> {
    let base = family
        .tariff_base
        .parse::<u64>()
        .map_err(|_| "tariffBase exceeds u64")?;
    let per_birth = family
        .tariff_per_birth
        .parse::<u64>()
        .map_err(|_| "tariffPerBirth exceeds u64")?;
    base.checked_add(per_birth)
        .map(|charge| charge.to_string())
        .ok_or("resource birth charge exceeds u64".into())
}

fn signed_grain_peer(view: &Value, task: &str, capability: &str, observe: &str) -> Result<Value> {
    let root = view
        .get("targetRoot")
        .and_then(Value::as_str)
        .ok_or("signed grain targetRoot absent")?;
    crate::decimal(root, "signed grain targetRoot")?;
    let before = view.get("grain").ok_or("signed grain state absent")?;
    let mut fields = serde_json::Map::new();
    for key in ["generation", "status", "remaining", "reserved"] {
        let value = before
            .get(key)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("signed grain {key} absent"))?;
        crate::decimal(value, "signed grain field")?;
        fields.insert(key.to_owned(), json!(value));
    }
    Ok(
        json!({"task":task,"capability":capability,"observeCapability":observe,
        "targetRoot":root,"before":fields}),
    )
}

/// Pure source construction only. The caller must durably reserve the tool,
/// retain this exact intent before native submit, and record a confirmed
/// composite receipt before enrolling the returned owner grant.
pub(super) fn plan_content_birth(
    family: &AllowedBirthFamily,
    tool: &ToolTask,
    parent_task: &str,
    nonce: u64,
    ordinal: u16,
    tool_view: &Value,
    parent_view: &Value,
) -> Result<(Value, BornResource)> {
    if ordinal >= family.max_births {
        return Err(format!("{} birth family is exhausted", family.name));
    }
    let target = bounded_id(&family.target_start, ordinal, "targetStart")?;
    let owner_capability = bounded_id(
        &family.owner_capability_start,
        ordinal,
        "ownerCapabilityStart",
    )?;
    let control_capability = bounded_id(
        &family.control_capability_start,
        ordinal,
        "controlCapabilityStart",
    )?;
    if target == family.factory_target
        || target == family.payer_account
        || target == tool.task
        || target == parent_task
        || owner_capability == control_capability
        || [
            tool.capability.as_str(),
            tool.query_capability.as_str(),
            tool.parent_capability.as_str(),
            tool.parent_observe_capability.as_str(),
            family.factory_observe_capability.as_str(),
            family.payer_capability.as_str(),
            family.payer_observe_capability.as_str(),
        ]
        .iter()
        .any(|existing| *existing == owner_capability || *existing == control_capability)
    {
        return Err("resource birth namespace overlaps an existing authority".into());
    }
    let tool_peer = signed_grain_peer(
        tool_view,
        &tool.task,
        &tool.capability,
        &tool.query_capability,
    )?;
    let parent_peer = signed_grain_peer(
        parent_view,
        parent_task,
        &tool.parent_capability,
        &tool.parent_observe_capability,
    )?;
    let authority_root = tool_view
        .get("authorityRoot")
        .and_then(Value::as_str)
        .ok_or("signed tool authorityRoot absent")?;
    crate::decimal(authority_root, "signed tool authorityRoot")?;
    if parent_view.get("authorityRoot").and_then(Value::as_str) != Some(authority_root) {
        return Err("tool and parent observations have different authority roots".into());
    }
    let height = tool_view
        .get("height")
        .and_then(Value::as_str)
        .ok_or("signed tool challenge height absent")?;
    crate::decimal(height, "signed tool challenge height")?;
    if parent_view.get("height").and_then(Value::as_str) != Some(height)
        || parent_view.get("imageBoundary").and_then(Value::as_str)
            != tool_view.get("imageBoundary").and_then(Value::as_str)
    {
        return Err("tool and parent observations have different signed height or image".into());
    }
    let image_boundary = tool_view
        .get("imageBoundary")
        .and_then(Value::as_str)
        .ok_or("signed tool challenge imageBoundary absent")?;
    crate::decimal(image_boundary, "signed tool challenge imageBoundary")?;
    let born = BornResource {
        name: format!("{}-{ordinal}", family.name),
        kind: "object".into(),
        target: target.clone(),
        owner_capability: owner_capability.clone(),
        control_capability: control_capability.clone(),
        max_result_bytes: family.max_result_bytes,
    };
    let birth = json!({
        "genesis":family.genesis,"template":family.template,
        "height":height,
        "creator":tool.subject,"nonce":nonce.to_string(),
        "resources":[{"kind":"object","storage":"content","target":target,
            "owner":tool.subject,"ownerCapability":owner_capability,
            "controlCapability":control_capability,
            "predicate":family.predicate}],
        "sourceCapabilities":[family.payer_capability],
        "funding":[],"feePayer":family.payer_account
    });
    let source = json!({"subject":tool.subject,"nonce":nonce.to_string(),
    "grainBirth":{"tariff":{"base":family.tariff_base,"perBirth":family.tariff_per_birth},
        "birth":birth,"authorityRoot":authority_root,
        "tool":tool_peer,"parent":parent_peer},
    "grants":[
        {"kind":"object","target":family.factory_target,
            "capability":family.factory_observe_capability},
        {"kind":"account","target":family.payer_account,
            "capability":family.payer_observe_capability},
        {"kind":"object","target":tool.task,"capability":tool.query_capability},
        {"kind":"object","target":parent_task,
            "capability":tool.parent_observe_capability}
    ]});
    if serde_json::to_vec(&source)
        .map_err(|e| e.to_string())?
        .len()
        > MAX_BIRTH_SOURCE_BYTES
    {
        return Err("resource birth intent exceeds source bound".into());
    }
    Ok((source, born))
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct AllowedResourceRead {
    pub name: String,
    pub kind: String,
    pub target: String,
    pub observe_capability: String,
    pub max_result_bytes: usize,
    #[serde(default)]
    pub fn_inbox_summary: bool,
}

pub(super) fn validate_reads(
    reads: &[AllowedResourceRead],
    publications: &[PublicationGrant],
) -> Result<()> {
    for (index, read) in reads.iter().enumerate() {
        if read.name.is_empty()
            || !read
                .name
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b == b'-')
        {
            return Err("resource read name must be alphanumeric or '-'".into());
        }
        if reads[..index].iter().any(|prior| prior.name == read.name) {
            return Err(format!("duplicate resource read name {}", read.name));
        }
        if !matches!(read.kind.as_str(), "object" | "account" | "program") {
            return Err(format!("unknown resource read kind for {}", read.name));
        }
        if read.fn_inbox_summary && read.kind != "object" {
            return Err(format!(
                "{} fnInboxSummary requires an object content resource",
                read.name
            ));
        }
        crate::decimal(&read.target, "resource read target")?;
        crate::decimal(&read.observe_capability, "resource observe capability")?;
        if read.max_result_bytes == 0 || read.max_result_bytes > MAX_RESULT_BYTES {
            return Err(format!(
                "{} maxResultBytes must be between 1 and {MAX_RESULT_BYTES}",
                read.name
            ));
        }
        if publications
            .iter()
            .any(|publication| publication.capability == read.observe_capability)
        {
            return Err(format!(
                "{} needs a distinct observe capability outside publication authority",
                read.name
            ));
        }
    }
    Ok(())
}

pub(super) fn select_read<'a>(
    reads: &'a [AllowedResourceRead],
    arguments: &Value,
) -> Result<&'a AllowedResourceRead> {
    let object = arguments
        .as_object()
        .ok_or("mini_read_resource arguments must be an object")?;
    if object.len() != 1 {
        return Err("mini_read_resource requires exactly one name argument".into());
    }
    let name = object
        .get("name")
        .and_then(Value::as_str)
        .ok_or("mini_read_resource name must be a string")?;
    reads
        .iter()
        .find(|read| read.name == name)
        .ok_or_else(|| format!("resource read {name} is not allowlisted"))
}

/// A born owner grant has observe and mutate verbs in the source factory law.
/// These adapters only locate its recorded capability for an ordinary signed
/// Mini query/publication. The caller must derive `born` from a retained,
/// verified historical birth receipt. Each subsequent Mini operation still
/// checks the current signed grant and policy; neither adapter creates authority.
pub(super) fn born_read(born: &BornResource) -> AllowedResourceRead {
    AllowedResourceRead {
        name: born.name.clone(),
        kind: born.kind.clone(),
        target: born.target.clone(),
        observe_capability: born.owner_capability.clone(),
        max_result_bytes: born.max_result_bytes,
        fn_inbox_summary: false,
    }
}

pub(super) fn born_publication(born: &BornResource) -> PublicationGrant {
    PublicationGrant {
        kind: born.kind.clone(),
        target: born.target.clone(),
        capability: born.owner_capability.clone(),
        observe_capability: born.owner_capability.clone(),
    }
}

pub(super) fn read_resource(
    config: &Config,
    tool: &ToolTask,
    read: &AllowedResourceRead,
    nonce: u64,
) -> Result<Value> {
    if read.observe_capability == tool.capability
        || read.observe_capability == tool.parent_capability
    {
        return Err("resource read needs an observe grant distinct from mutation authority".into());
    }
    // The caller selects `read` by its configured name and allocates `nonce`
    // from the durable journal before entering this function. No caller-supplied
    // target, grant, signer, or path is accepted here.
    let dir = config.state_dir.join(format!("resource-read-{nonce:016}"));
    fs::create_dir(&dir).map_err(|e| format!("resource read directory: {e}"))?;
    let intent = json!({
        "subject": tool.subject,
        "nonce": nonce.to_string(),
        "purpose": {
            "type": "query", "kind": read.kind, "target": read.target,
            "view": "resource"
        },
        "grants": [{
            "kind": read.kind, "target": read.target,
            "capability": read.observe_capability
        }]
    });
    let intent_path = dir.join("intent-source.json");
    let intent_bytes = serde_json::to_vec_pretty(&intent).map_err(|e| e.to_string())?;
    write_new(&intent_path, &intent_bytes)?;

    let attempt = dir.join("attempt");
    let mut command = Command::new(&config.mini);
    command
        .arg("query")
        .arg("--host")
        .arg(&config.host)
        .arg("--config")
        .arg(&config.host_config)
        .arg("--intent")
        .arg(&intent_path)
        .arg("--key")
        .arg(&tool.custody_key)
        .arg("--view")
        .arg("resource")
        .arg("--dir")
        .arg(&attempt)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    if let Some(socket) = &config.host_socket {
        command.arg("--socket").arg(socket);
    }
    if read.fn_inbox_summary {
        command.arg("--presentation").arg("fn-inbox-resource");
    }
    let status = command
        .status()
        .map_err(|e| format!("native Mini resource query: {e}"))?;
    if !status.success() {
        return Err(format!(
            "native Mini refused resource read {} ({}); retained attempt at {}",
            read.name,
            status,
            attempt.display()
        ));
    }
    // The query above is the only authority-bearing read. With fn summary
    // selected, the native client asks Lean to present its exact retained
    // view.bin directly as typed JSON. It skips the potentially much larger
    // raw JSON rendering of the same content page.
    let path = attempt.join("view.json");
    let bytes = read_bounded(&path, read.max_result_bytes)?;
    let view: Value = serde_json::from_slice(&bytes)
        .map_err(|e| format!("native resource view is not JSON: {e}"))?;
    let expected_type = if read.fn_inbox_summary {
        "fn-inbox-resource-summary-v1"
    } else {
        "resource"
    };
    let expected_content = if read.fn_inbox_summary {
        view.get("entries").is_some_and(Value::is_array)
    } else {
        view.get("page").is_some_and(Value::is_object)
    };
    if view.get("type").and_then(Value::as_str) != Some(expected_type) || !expected_content {
        return Err("native resource query returned the wrong view shape".into());
    }
    let result = json!({
        "kind": read.kind,
        "target": read.target,
        "presentation": if read.fn_inbox_summary { "fn-inbox-resource" } else { "resource" },
        "view": view
    });
    let result_len = serde_json::to_vec(&result)
        .map_err(|e| e.to_string())?
        .len();
    if result_len > read.max_result_bytes {
        return Err(format!(
            "signed resource result is {result_len} bytes, above {} maxResultBytes; complete attempt retained at {}",
            read.max_result_bytes,
            attempt.display()
        ));
    }
    if result_len > MAX_TOOL_RESULT_BYTES {
        return Err(format!(
            "signed resource result is {result_len} bytes, above {MAX_TOOL_RESULT_BYTES} byte MCP/ACP response budget; complete attempt retained at {}",
            attempt.display()
        ));
    }
    Ok(result)
}

fn read_bounded(path: &Path, max: usize) -> Result<Vec<u8>> {
    let size = fs::metadata(path)
        .map_err(|e| format!("native resource view unavailable: {e}"))?
        .len();
    if size > max as u64 {
        return Err(format!(
            "signed resource view is {size} bytes, above {max} maxResultBytes; complete view retained at {}",
            path.display()
        ));
    }
    let bytes = fs::read(path).map_err(|e| format!("native resource view read: {e}"))?;
    if bytes.len() > max {
        return Err(format!(
            "signed resource view grew beyond {max} maxResultBytes; complete view retained at {}",
            path.display()
        ));
    }
    Ok(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn birth_family() -> AllowedBirthFamily {
        AllowedBirthFamily {
            name: "notes".into(),
            genesis: json!({"source":"operator-pinned-genesis"}),
            template: json!({"issuer":"5","ownerBudget":"100000","lifetime":"10000"}),
            predicate: json!({"type":"all","predicates":[]}),
            factory_target: "10".into(),
            factory_observe_capability: "58".into(),
            payer_account: "8".into(),
            payer_capability: "48".into(),
            payer_observe_capability: "48".into(),
            tariff_base: "1".into(),
            tariff_per_birth: "1".into(),
            target_start: "9000".into(),
            owner_capability_start: "90000".into(),
            control_capability_start: "91000".into(),
            max_births: 16,
            max_result_bytes: 64 * 1024,
        }
    }

    #[test]
    fn content_birth_uses_exact_factory_payer_tool_parent_footprint() {
        let family = birth_family();
        let tool = ToolTask {
            task: "7002".into(),
            subject: "8".into(),
            capability: "81".into(),
            query_capability: "81".into(),
            custody_key: "/unused/tool.key".into(),
            parent_capability: "73".into(),
            parent_observe_capability: "73".into(),
            reserve: "3".into(),
            charge: "1".into(),
            allowed_publications: vec![],
            allowed_reads: vec![],
            allowed_birth_families: vec![],
        };
        let peer = |root: &str| {
            json!({"authorityRoot":"123","targetRoot":root,"height":"20",
            "imageBoundary":"456",
            "grain":{"generation":"1","status":"3","remaining":"97","reserved":"3"}})
        };
        let (intent, born) =
            plan_content_birth(&family, &tool, "7001", 50, 2, &peer("111"), &peer("222")).unwrap();
        assert_eq!(born.target, "9002");
        assert_eq!(born.owner_capability, "90002");
        assert_eq!(born.control_capability, "91002");
        assert_eq!(intent["grainBirth"]["birth"]["height"], "20");
        assert_eq!(born_read(&born).observe_capability, "90002");
        assert_eq!(born_publication(&born).capability, "90002");
        // Static configuration requires separated observe/mutate grants. The
        // born owner grant instead carries both verbs under the factory law;
        // only a verified composite receipt may enter the dynamic registry.
        assert!(validate_reads(&[born_read(&born)], &[born_publication(&born)]).is_err());
        assert_eq!(intent["subject"], "8");
        assert_eq!(
            intent["grainBirth"]["birth"]["resources"][0]["storage"],
            "content"
        );
        assert_eq!(intent["grainBirth"]["birth"]["resources"][0]["owner"], "8");
        assert_eq!(
            intent["grainBirth"]["birth"]["resources"][0]["predicate"],
            json!({"type":"all","predicates":[]})
        );
        assert_eq!(intent["grainBirth"]["birth"]["funding"], json!([]));
        assert_eq!(intent["grainBirth"]["tool"]["before"]["reserved"], "3");
        assert_eq!(
            intent["grants"],
            json!([
                {"kind":"object","target":"10","capability":"58"},
                {"kind":"account","target":"8","capability":"48"},
                {"kind":"object","target":"7002","capability":"81"},
                {"kind":"object","target":"7001","capability":"73"}
            ])
        );
        let mut stale_parent = peer("222");
        stale_parent["height"] = json!("21");
        assert!(
            plan_content_birth(&family, &tool, "7001", 50, 2, &peer("111"), &stale_parent).is_err()
        );
        stale_parent["height"] = json!("20");
        stale_parent["imageBoundary"] = json!("457");
        assert!(
            plan_content_birth(&family, &tool, "7001", 50, 2, &peer("111"), &stale_parent).is_err()
        );
    }

    #[test]
    fn birth_selection_and_namespaces_are_bounded() {
        let family = birth_family();
        let validate = |family: &[AllowedBirthFamily]| {
            validate_birth_families(family, &[], &[], &["7001", "7002"], &["73", "81"])
        };
        assert!(validate(std::slice::from_ref(&family)).is_ok());
        assert!(select_birth(std::slice::from_ref(&family), &json!({"family":"notes"})).is_ok());
        assert!(select_birth(
            std::slice::from_ref(&family),
            &json!({"family":"notes","target":"1"})
        )
        .is_err());
        assert!(select_birth(std::slice::from_ref(&family), &json!({"family":"unknown"})).is_err());
        let mut overflow = family.clone();
        overflow.target_start = u64::MAX.to_string();
        assert!(validate(&[overflow]).is_err());
        let mut free = family;
        free.tariff_base = "0".into();
        assert!(validate(&[free]).is_err());
        let first = birth_family();
        let mut overlapping = birth_family();
        overlapping.name = "other".into();
        assert!(validate(&[first.clone(), overlapping]).is_err());
        let mut second = first.clone();
        second.name = "second".into();
        second.target_start = "10000".into();
        second.owner_capability_start = "100000".into();
        second.control_capability_start = "101000".into();
        second.factory_target = "9002".into();
        assert!(validate(&[first.clone(), second]).is_err());
        assert!(validate_birth_families(
            std::slice::from_ref(&first),
            &[read("notes-0", "90")],
            &[],
            &[],
            &[]
        )
        .is_err());
        assert!(
            validate_birth_families(std::slice::from_ref(&first), &[], &[], &["9002"], &[])
                .is_err()
        );
        assert!(
            validate_birth_families(std::slice::from_ref(&first), &[], &[], &[], &["90002"])
                .is_err()
        );
        assert!(validate_birth_families(
            &[first],
            &[],
            &[PublicationGrant {
                kind: "object".into(),
                target: "9003".into(),
                capability: "95".into(),
                observe_capability: "96".into()
            }],
            &[],
            &[]
        )
        .is_err());
    }

    fn read(name: &str, capability: &str) -> AllowedResourceRead {
        AllowedResourceRead {
            name: name.into(),
            kind: "object".into(),
            target: "8001".into(),
            observe_capability: capability.into(),
            max_result_bytes: 64 * 1024,
            fn_inbox_summary: false,
        }
    }

    #[test]
    fn rejects_publication_authority_and_ambiguous_names() {
        let publications = vec![PublicationGrant {
            kind: "object".into(),
            target: "8001".into(),
            capability: "88".into(),
            observe_capability: "89".into(),
        }];
        assert!(validate_reads(&[read("inbox", "90")], &publications).is_ok());
        assert!(validate_reads(&[read("inbox", "88")], &publications).is_err());
        assert!(validate_reads(&[read("inbox", "89")], &publications).is_ok());
        assert!(validate_reads(&[read("inbox", "90"), read("inbox", "91")], &[]).is_err());
    }

    #[test]
    fn refuses_unbounded_view() {
        let mut entry = read("inbox", "90");
        entry.max_result_bytes = MAX_RESULT_BYTES + 1;
        assert!(validate_reads(&[entry], &[]).is_err());
    }

    #[test]
    fn accepts_only_exact_allowlisted_name_argument() {
        let reads = [read("inbox", "90")];
        assert!(select_read(&reads, &json!({"name":"inbox"})).is_ok());
        assert!(select_read(&reads, &json!({"name":"other"})).is_err());
        assert!(select_read(&reads, &json!({"name":"inbox","target":"999"})).is_err());
        assert!(select_read(&reads, &json!({"name":90})).is_err());
    }
}
