//! Operator-named, signed reads of shared Mini resources. This module only
//! selects a fixed observe grant and invokes the native client; the Lean host
//! checks the current grant and materializes the resource view.
use crate::{write_new, Config, PublicationGrant, Result, ToolTask};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::os::unix::fs::{MetadataExt, PermissionsExt};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

// A complete content page can include the fn consumer's typed inbox atom and
// exact carrier. Refuse larger results explicitly instead of returning a
// prefix. The raw JSON presentation repeats whole-page and per-entry bytes;
// named fn reads ask Lean for its typed presentation of the same signed view.
const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;
// The typed view may be larger, but the returned JSON is nested as MCP text
// before reaching the ACP peer. Leave room for that escaping and its envelope.
const MAX_TOOL_RESULT_BYTES: usize = 256 * 1024;
pub(super) const MAX_BIRTH_SOURCE_BYTES: usize = 256 * 1024;

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

pub(super) fn signed_grain_peer(
    view: &Value,
    task: &str,
    capability: &str,
    observe: &str,
) -> Result<Value> {
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
    let height = tool_view
        .get("height")
        .and_then(Value::as_str)
        .ok_or("signed tool challenge height absent")?;
    crate::decimal(height, "signed tool challenge height")?;
    if parent_view.get("height").and_then(Value::as_str) != Some(height)
        || parent_view.get("worldRoot").and_then(Value::as_str)
            != tool_view.get("worldRoot").and_then(Value::as_str)
    {
        return Err("tool and parent observations have different signed height or image".into());
    }
    let world_root = tool_view
        .get("worldRoot")
        .and_then(Value::as_str)
        .ok_or("signed tool challenge worldRoot absent")?;
    crate::decimal(world_root, "signed tool challenge worldRoot")?;
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
        "birth":birth,
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
    let mut matches = reads.iter().filter(|read| read.name == name);
    let read = matches.next()
        .ok_or_else(|| format!("resource read {name} is not allowlisted"))?;
    if matches.next().is_some() {
        return Err(format!("resource read {name} is ambiguous"));
    }
    Ok(read)
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

/// Only already configured custody can be selected. Controller custody is used
/// solely after the caller verifies a controller-owned session birth receipt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum ResourceReadSigner {
    Tool,
    Controller,
}

/// `run` owns the exact child lifetime. Production callers use CustodyGate so
/// hard disconnect cancels and reaps a query rather than leaving a child.
pub(super) fn read_resource_with(
    config: &Config,
    tool: &ToolTask,
    read: &AllowedResourceRead,
    nonce: u64,
    signer: ResourceReadSigner,
    run: impl FnOnce(&mut Command) -> Result<()>,
) -> Result<Value> {
    let (subject, key) = match signer {
        ResourceReadSigner::Tool => (&tool.subject, &tool.custody_key),
        ResourceReadSigner::Controller => (&config.subject, &config.custody_key),
    };
    if read.observe_capability == tool.capability
        || read.observe_capability == tool.parent_capability
        || (signer == ResourceReadSigner::Controller && read.observe_capability == config.capability)
    {
        return Err("resource read needs an observe grant distinct from mutation authority".into());
    }
    // The caller selects `read` by its configured name and allocates `nonce`
    // from the durable journal before entering this function. No caller-supplied
    // target, grant, signer, or path is accepted here.
    let dir = config.state_dir.join(format!("resource-read-{nonce:016}"));
    fs::create_dir(&dir).map_err(|e| format!("resource read directory: {e}"))?;
    let intent = json!({
        "subject": subject,
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
        .arg(key)
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
    run(&mut command).map_err(|error| {
        format!(
            "native Mini refused resource read {} ({error}); retained attempt at {}",
            read.name,
            attempt.display()
        )
    })?;
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
        view.get("cell").is_some_and(Value::is_object)
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

// ---------------------------------------------------------------- room tools

/// Hermes's tools in a room (docs/PLACE.md §2.7, §5 item 7). Each is one or two lines
/// of the pinned `mini` client's shell, run under HERMES'S OWN workspace (its
/// key, its references, its grants): no tool holds or lends authority the
/// workspace lacks, and a line the Host refuses comes back as the Host's
/// refusal, verbatim. The controller pins the room; the model names no room,
/// no capability and no proposal id.
///
/// Every WRITE is a turn: before it, one fleet turn pays the room's
/// `hermes/turn` price from Hermes's budget account to the room's till
/// (`mini credit --action turn`). When the account cannot cover it the Host
/// refuses that payment at plan (`bookRefused`) and the write is not
/// attempted: the error starts `out of budget:`.
///
/// Seams: `mini_doc_quote` and `mini_doc_history` (docs/DEOS.md §2.3) wait for the
/// docuverse-on-final lane (the content cell's transclusion action and the
/// history view); they are not offered.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct RoomToolsConfig {
    /// Offer and accept only room tools for this resident. Generic workspace
    /// mutations would bypass the room turn payment, so this is on unless a
    /// config says `"restrictTools": false` explicitly.
    #[serde(default = "restrict_tools_default")]
    pub restrict_tools: bool,
    /// The pinned `mini` client.
    pub mini: PathBuf,
    pub host: PathBuf,
    pub host_config: PathBuf,
    pub socket: PathBuf,
    /// Hermes's own workspace and shell home.
    pub workspace: PathBuf,
    pub home: PathBuf,
    /// The room (Hermes's name for the chat room it joined).
    pub room: String,
    /// Hermes's budget account reference (`ROOM-hermes`). Absent: writes are
    /// not metered (a room without a Hermes tariff).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub account: Option<String>,
}

fn restrict_tools_default() -> bool { true }

/// One resident client per room tool identity: its pinned `mini`, Host,
/// settings, socket, workspace and home (one client process pins each once).
type RoomResidentKey = [PathBuf; 6];
static ROOM_RESIDENTS: std::sync::Mutex<Vec<(RoomResidentKey, std::sync::Arc<crate::custody_gate::CustodyGate>)>> =
    std::sync::Mutex::new(Vec::new());

fn room_resident(config: &RoomToolsConfig) -> Option<std::sync::Arc<crate::custody_gate::CustodyGate>> {
    // Test room tools run one-shot `mini` scripts.
    if cfg!(test) {
        return None;
    }
    let key: RoomResidentKey = [config.mini.clone(), config.host.clone(), config.host_config.clone(),
        config.socket.clone(), config.workspace.clone(), config.home.clone()];
    let mut residents = ROOM_RESIDENTS.lock().ok()?;
    if let Some((_, gate)) = residents.iter().find(|(k, _)| k == &key) {
        return Some(gate.clone());
    }
    let gate = std::sync::Arc::new(crate::custody_gate::CustodyGate::with_resident(&config.mini, None));
    residents.push((key, gate.clone()));
    Some(gate)
}

/// End every idle room resident client (before a physical quiescence proof).
pub(crate) fn retire_room_residents() -> Result<()> {
    let residents = ROOM_RESIDENTS.lock().map_err(|_| "room resident registry poisoned")?;
    for (_, gate) in residents.iter() {
        gate.retire().map_err(|e| format!("room resident client: {e}"))?;
    }
    Ok(())
}

/// The room tools' MCP schemas (also the provider's function list).
pub(crate) fn room_tool_specs() -> Vec<Value> {
    let name = json!({"type":"string","maxLength":64,"pattern":"^[A-Za-z0-9-]+$",
        "description":"An existing workspace reference alias (for example lab-index), or a canonical resource ID with exactly one existing workspace binding. Unknown or ambiguous IDs refuse; IDs do not import authority."});
    vec![
        json!({"name":"mini_room_ls",
            "description":"The cells written under this room, from the Host's signed history (since HEIGHT, default 0): each cell's first and last height, its writers, whether it is a member's stream, and the names this workspace holds for it (unnamed cells are named ROOM-cell-ID under your room grant). Read-only.",
            "inputSchema":{"type":"object","properties":{"since":{"type":"string","pattern":"^[0-9]+$","maxLength":20}},"additionalProperties":false}}),
        json!({"name":"mini_room_status",
            "description":"This room's tariff (what a turn costs), its till, and your budget account's balance. Signed reads; read-only.",
            "inputSchema":{"type":"object","properties":{},"additionalProperties":false}}),
        json!({"name":"mini_stream_tail",
            "description":"Visible streams merged by height, author, cell and sequence. Reply number #N refers to this observed feed; the cell/sequence pair is the stable identity if newly visible history changes numbering. Only Host-verified text is shown. Read-only.",
            "inputSchema":{"type":"object","properties":{
                "n":{"type":"string","pattern":"^[0-9]+$","maxLength":6},
                "since":{"type":"string","pattern":"^[0-9]+$","maxLength":20}},"additionalProperties":false}}),
        json!({"name":"mini_say",
            "description":"Append one entry to YOUR stream in this room (a turn: it pays the room's hermes/turn first). `to` addresses a member (a subject), `re` replies to entry #N.",
            "inputSchema":{"type":"object","properties":{
                "text":{"type":"string","maxLength":3000},
                "to":{"type":"string","pattern":"^[0-9]+$","maxLength":20},
                "re":{"type":"string","pattern":"^[0-9]+$","maxLength":10}},
                "required":["text"],"additionalProperties":false}}),
        json!({"name":"mini_doc_context",
            "description":"Select bounded current document context with exact source/revision/placement dependencies. Derived summaries lose inference text after their support changes.",
            "inputSchema":{"type":"object","properties":{"doc":{"type":"string"},"maxRows":{"type":"string"},"maxBytes":{"type":"string"}},"required":["doc"],"additionalProperties":false}}),
        json!({"name":"mini_doc_show",
            "description":"Read a document’s current signed lines and links. After a confirmed write, read again to verify the change. Use document aliases in replies; renderer headers and hashes are observation metadata, not document prose. Read-only.",
            "inputSchema":{"type":"object","properties":{"doc":name},"required":["doc"],"additionalProperties":false}}),
        json!({"name":"mini_doc_link",
            "description":"Add a link from document reference `from` to existing workspace reference `to` (a turn). Use the programName from the assignment for the librarian program; aliases are preferred. A resource ID is accepted only when it uniquely names an existing binding. Admitted only where you hold a grant to write `from` and its law admits you; otherwise the Host refuses and says why.",
            "inputSchema":{"type":"object","properties":{"from":name,"to":name,
                "relation":{"type":"string","pattern":"^[0-9]+$","maxLength":10}},
                "required":["from","to"],"additionalProperties":false}}),
        json!({"name":"mini_doc_review",
            "description":"Land an explicit reviewed document proposal against selected source context. Supply the exact context bundle and intended ordinary document actions. Changed or revoked cited inputs refuse; prior started operations require exact recovery. Ordinary document append remains separate.",
            "inputSchema":{"type":"object","properties":{"context":{"type":"object"},"targets":{"type":"array","minItems":1,"maxItems":8}},"required":["context","targets"],"additionalProperties":false}}),
        json!({"name":"mini_doc_append",
            "description":"Append a line to document `doc` (a turn). Admitted only where you hold a grant to write `doc` and its law admits you; otherwise the Host refuses and says why (no-grant, law-denied).",
            "inputSchema":{"type":"object","properties":{"doc":name,"text":{"type":"string","maxLength":3000}},
                "required":["doc","text"],"additionalProperties":false}}),
        json!({"name":"mini_pending_awaits",
            "description":"World programs waiting for YOUR answer: the activities a room member announced in this room (a message `await OBJECT TRANSACTION`) whose current await is a reply slot you decide. Each names its slot, deadline, the object's declared state (the question's data) and who announced it. Signed reads; read-only.",
            "inputSchema":{"type":"object","properties":{},"additionalProperties":false}}),
        json!({"name":"mini_answer_await",
            "description":"Answer one pending await (a turn): decide `slot` with `reply` (the value, in the program's data JSON, e.g. {\"tag\":\"record\",\"fields\":[{\"name\":\"amount\",\"value\":{\"tag\":\"natural\",\"value\":\"5\"}}]}) or `refused` (a reason). Only awaits announced in this room are answerable; the kernel admits only the slot's decider (notDecider) and only once (a decided slot refuses).",
            "inputSchema":{"type":"object","properties":{"slot":{"type":"string","pattern":"^[0-9]+$","maxLength":80},
                "reply":{"type":"object"},"refused":{"type":"string","maxLength":500}},
                "required":["slot"],"additionalProperties":false}}),
    ]
}

/// Validate the complete write before a room turn is charged.
pub(crate) fn validate_room_write(name: &str, arguments: &Value) -> Result<()> {
    match name {
        "mini_say" => {
            only_keys(arguments, &["text", "to", "re"])?;
            bounded_text(arguments, "text")?;
            bounded_decimal(arguments, "to", 20)?;
            bounded_decimal(arguments, "re", 10)?;
        }
        "mini_doc_append" => {
            only_keys(arguments, &["doc", "text"])?;
            bounded_name(arguments, "doc")?;
            bounded_text(arguments, "text")?;
        }
        "mini_doc_review" => {
            crate::resident_context::reviewed_arguments(arguments)?;
        }
        "mini_doc_link" => {
            only_keys(arguments, &["from", "to", "relation"])?;
            bounded_name(arguments, "from")?;
            bounded_name(arguments, "to")?;
            bounded_decimal(arguments, "relation", 10)?;
        }
        "mini_answer_await" => { await_answer(arguments)?; }
        _ => return Err(format!("{name} is not a room write tool")),
    }
    Ok(())
}

/// Remove only the renderer's fixed 38-column continuation gutter. The
/// signed header, atom creator/line labels and every content byte remain.
pub(crate) fn compact_doc_rendering(text: &str) -> String {
    if !text.starts_with("# doc ") { return text.to_owned(); }
    text.split_inclusive('\n').map(|line|
        line.strip_prefix("                                      ").unwrap_or(line)).collect()
}

/// The room tools that write (each one a metered turn).
pub(crate) const ROOM_WRITE_TOOLS: &[&str] = &["mini_say", "mini_doc_link", "mini_doc_append", "mini_doc_review", "mini_answer_await"];

pub(crate) fn is_room_tool(name: &str) -> bool {
    room_tool_specs().iter().any(|spec| spec["name"] == name)
}

/// One shell line's ending: (exit code, stdout, stderr).
pub(crate) struct LineRun {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

impl LineRun {
    /// The refusal or error block as the client printed it (from its first
    /// `refused:`/`error:`/`usage:`/`undecided:` line), verbatim and bounded.
    pub fn ending(&self) -> String {
        let lines: Vec<&str> = self.stderr.lines().collect();
        let at = lines
            .iter()
            .position(|l| ["refused: ", "error: ", "usage: ", "undecided: ", "not here: "].iter().any(|p| l.starts_with(p)))
            .unwrap_or(0);
        let mut text = lines[at..].join("\n");
        if text.trim().is_empty() {
            text = format!("the client exited {} with no message", self.code);
        }
        text.chars().take(4096).collect()
    }
}

fn bounded_name(value: &Value, key: &str) -> Result<String> {
    let text = value.get(key).and_then(Value::as_str).ok_or_else(|| format!("{key} absent"))?;
    if text.is_empty() || text.len() > 64 || !text.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-') {
        return Err(format!("{key} must be 1..64 ASCII letters, digits or hyphens"));
    }
    Ok(text.to_owned())
}

fn bounded_decimal(value: &Value, key: &str, max: usize) -> Result<Option<String>> {
    match value.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(Value::String(text)) if !text.is_empty() && text.len() <= max && text.bytes().all(|b| b.is_ascii_digit()) => {
            Ok(Some(text.clone()))
        }
        Some(_) => Err(format!("{key} must be a decimal string")),
    }
}

fn bounded_text(value: &Value, key: &str) -> Result<String> {
    let text = value.get(key).and_then(Value::as_str).ok_or_else(|| format!("{key} absent"))?;
    if text.trim().is_empty() || text.len() > 3000 || text.chars().any(|c| c.is_control() && c != '\n') {
        return Err(format!("{key} must be 1..3000 bytes of text"));
    }
    Ok(text.to_owned())
}

/// `mini_answer_await`'s arguments: (slot, the answer as `bend answer` takes it).
fn await_answer(arguments: &Value) -> Result<(String, Value)> {
    only_keys(arguments, &["slot", "reply", "refused"])?;
    let slot = bounded_decimal(arguments, "slot", 80)?.ok_or("slot absent")?;
    let answer = match (arguments.get("reply"), arguments.get("refused")) {
        (Some(reply), None) if reply.is_object() => json!({"reply": reply}),
        (None, Some(Value::String(reason))) if !reason.trim().is_empty() && reason.len() <= 500 => json!({"refused": reason}),
        _ => return Err("answer with exactly one of reply (an object) or refused (a reason)".into()),
    };
    if serde_json::to_vec(&answer).map_err(|e| e.to_string())?.len() > 4096 {
        return Err("an answer is at most 4096 bytes".into());
    }
    Ok((slot, answer))
}

/// The births room members announced to the resident: `await OBJECT TRANSACTION` in an entry
/// not written by `me`, newest first, at most eight. Announcing in the room is the member's
/// allowance: a resident answers only programs its room's members named.
pub(crate) fn announced_awaits(entries: &[Value], me: &str) -> Vec<(String, String, String)> {
    let mut found: Vec<(String, String, String)> = Vec::new();
    for entry in entries.iter().rev() {
        if entry["author"].as_str() == Some(me) { continue; }
        let author = entry["author"].as_str().unwrap_or("").to_owned();
        let words: Vec<&str> = entry["text"].as_str().unwrap_or("").split_whitespace().collect();
        for w in words.windows(3) {
            let decimal = |t: &str| !t.is_empty() && t.len() <= 80 && t.bytes().all(|b| b.is_ascii_digit());
            if w[0] == "await" && decimal(w[1]) && decimal(w[2])
                && !found.iter().any(|(o, t, _)| o == w[1] && t == w[2]) && found.len() < 8 {
                found.push((w[1].to_owned(), w[2].to_owned(), author.clone()));
            }
        }
    }
    found
}

fn only_keys(value: &Value, keys: &[&str]) -> Result<()> {
    let object = value.as_object().ok_or("tool arguments must be an object")?;
    if let Some(extra) = object.keys().find(|k| !keys.contains(&k.as_str())) {
        return Err(format!("unknown argument {extra}"));
    }
    Ok(())
}

/// The last JSON document a client printed (pretty or compact): the last
/// one that starts at a line beginning with `{`.
pub(crate) fn last_json(stdout: &str) -> Option<Value> {
    let mut starts: Vec<usize> = stdout.match_indices("\n{").map(|(at, _)| at + 1).collect();
    if stdout.starts_with('{') {
        starts.insert(0, 0);
    }
    starts
        .iter()
        .rev()
        .find_map(|&at| serde_json::Deserializer::from_str(&stdout[at..]).into_iter::<Value>().next()?.ok())
}

/// The links a `doc show` rendering states: `link ID -> … (KIND TARGET) …` or
/// `link ID -> KIND TARGET …`; the target ids, in order.
pub(crate) fn rendered_links(text: &str) -> Vec<String> {
    text.lines()
        .filter_map(|line| line.strip_prefix("link "))
        .filter_map(|rest| rest.split_once(" -> ").map(|(_, target)| target))
        .filter_map(|target| {
            let inner = match (target.find('('), target.find(')')) {
                (Some(open), Some(close)) if open < close => &target[open + 1..close],
                _ => target,
            };
            let mut words = inner.split_whitespace();
            words.next()?;
            words.next().filter(|id| id.bytes().all(|b| b.is_ascii_digit())).map(str::to_owned)
        })
        .collect()
}

pub(crate) struct RoomTools<'a> {
    pub config: &'a RoomToolsConfig,
}

impl RoomTools<'_> {
    /// Run one shell line under Hermes's workspace; `spawned` sees the child's
    /// pid before it is waited on (the controller journals it: a submitter it
    /// can later prove stopped).
    pub fn line_with(&self, line: &str, spawned: &mut dyn FnMut(u32)) -> Result<LineRun> {
        self.line_with_input(line, None, Some(spawned))
    }

    /// A line no journal names a submitter for runs as a frame to this room
    /// identity's resident client (`room_resident`); a journaled write keeps
    /// its own child, whose /proc cmdline is the proof it stopped.
    fn line_with_input(&self, line: &str, input: Option<&[u8]>, spawned: Option<&mut dyn FnMut(u32)>) -> Result<LineRun> {
        let config = self.config;
        let Some(spawned) = spawned else {
            if let Some(gate) = room_resident(config) {
                let arguments: Vec<&std::ffi::OsStr> = vec![
                    "shell".as_ref(), "--socket".as_ref(), config.socket.as_os_str(), "--host".as_ref(),
                    config.host.as_os_str(), "--config".as_ref(), config.host_config.as_os_str(),
                    "--workspace".as_ref(), config.workspace.as_os_str(), "--home".as_ref(),
                    config.home.as_os_str(), "--line".as_ref(), line.as_ref(),
                ];
                let out = gate
                    .run_frame(&std::sync::atomic::AtomicBool::new(false), &arguments, input.unwrap_or(&[]), crate::deadline::NATIVE_CALL)
                    .map_err(|e| match e {
                        crate::custody_gate::CustodyError::Uncertain(e) => crate::deadline::describe("mini shell", e),
                        other => format!("mini shell: {other}"),
                    })?;
                return Ok(LineRun {
                    code: out.status.code().unwrap_or(-1),
                    stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
                    stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
                });
            }
            return self.line_with_input(line, input, Some(&mut |_| {}));
        };
        let mut child = crate::deadline::spawn(Command::new(&config.mini)
            .arg("shell")
            .arg("--socket")
            .arg(&config.socket)
            .arg("--host")
            .arg(&config.host)
            .arg("--config")
            .arg(&config.host_config)
            .arg("--workspace")
            .arg(&config.workspace)
            .arg("--home")
            .arg(&config.home)
            .arg("--line")
            .arg(line)
            .stdin(if input.is_some() { Stdio::piped() } else { Stdio::null() }))
            .map_err(|e| format!("{}: {e}", config.mini.display()))?;
        spawned(child.id());
        if let Some(bytes) = input {
            use std::io::Write;
            let sent = child.stdin.take().ok_or("discovery stdin absent")?.write_all(bytes);
            if let Err(error) = sent {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("discovery stdin: {error}"));
            }
        }
        // On the deadline the submitter's process group is killed and reaped
        // before this returns, so the journaled submitter is provably stopped.
        let out = crate::deadline::wait(child, crate::deadline::NATIVE_CALL)
            .map_err(|e| crate::deadline::describe("mini shell", e))?;
        Ok(LineRun {
            code: out.status.code().unwrap_or(-1),
            stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
        })
    }

    /// A `mini` command no journal names a submitter for: a frame to the room
    /// resident client, or (test room tools) its own child, under the same deadline.
    fn client(&self, command: &mut Command) -> std::io::Result<std::process::Output> {
        match room_resident(self.config) {
            Some(gate) => {
                let arguments: Vec<&std::ffi::OsStr> = command.get_args().collect();
                gate.run_frame(&std::sync::atomic::AtomicBool::new(false), &arguments, &[], crate::deadline::NATIVE_CALL)
                    .map_err(|e| match e {
                        crate::custody_gate::CustodyError::Uncertain(e) => e,
                        other => std::io::Error::other(other.to_string()),
                    })
            }
            None => crate::deadline::output(command, crate::deadline::NATIVE_CALL),
        }
    }

    pub fn line(&self, line: &str) -> Result<LineRun> {
        self.line_with_input(line, None, None)
    }

    fn ok_or_ending(run: LineRun) -> Result<LineRun> {
        if run.code == 0 {
            Ok(run)
        } else {
            Err(run.ending())
        }
    }

    /// A plain file in Hermes's `HOME/requests` (`@FILE` arguments).
    fn request_file(&self, name: &str, text: &str) -> Result<String> {
        let dir = self.config.home.join("requests");
        fs::create_dir_all(&dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        let path = dir.join(name);
        let _ = fs::remove_file(&path);
        fs::write(&path, text).map_err(|e| format!("{}: {e}", path.display()))?;
        Ok(name.to_owned())
    }

    /// A read-only tool.
    pub fn read(&self, name: &str, arguments: &Value) -> Result<Value> {
        let room = &self.config.room;
        match name {
            "mini_room_ls" => {
                only_keys(arguments, &["since"])?;
                let since = bounded_decimal(arguments, "since", 20)?.unwrap_or_else(|| "0".into());
                let run = Self::ok_or_ending(self.line(&format!("room ls {room} --since {since} --import --json"))?)?;
                last_json(&run.stdout).ok_or_else(|| "room ls printed no JSON".to_owned())
            }
            "mini_room_status" => {
                only_keys(arguments, &[])?;
                let status = Self::ok_or_ending(self.line(&format!("room status {room}"))?)?;
                let budget = match &self.config.account {
                    Some(account) => Self::ok_or_ending(self.line(&format!("credit {account}"))?)?.stdout,
                    None => "no budget account".into(),
                };
                Ok(json!({"status":status.stdout,"budget":budget.trim()}))
            }
            "mini_stream_discovery" => {
                only_keys(arguments,&["cursor","n"])?;
                let cursor = arguments.get("cursor").ok_or("discovery cursor absent")?;
                if !cursor.is_object() { return Err("discovery cursor must be JSON object".into()); }
                let bytes = serde_json::to_vec(cursor).map_err(|e| e.to_string())?;
                if bytes.len() > 262144 { return Err("discovery cursor exceeds bound".into()); }
                let n=bounded_decimal(arguments,"n",3)?.ok_or("discovery page size absent")?;
                let run=Self::ok_or_ending(self.line_with_input(&format!("tail --in {room} --json --discover-json - -n {n}"), Some(&bytes), None)?)?;
                let mut docs=run.stdout.lines().filter_map(|l|serde_json::from_str::<Value>(l).ok());
                let state=docs.next().ok_or("discovery printed no room state")?;
                Ok(json!({"room":state,"entries":docs.collect::<Vec<_>>()}))
            }
            "mini_stream_entry" => {
                only_keys(arguments, &["cell", "sequence"])?;
                let cell = bounded_decimal(arguments, "cell", 78)?.ok_or("source cell absent")?;
                let sequence = bounded_decimal(arguments, "sequence", 20)?.ok_or("source sequence absent")?;
                let run = Self::ok_or_ending(self.line(&format!("tail --in {room} --json --entry {cell}:{sequence}"))?)?;
                let mut docs = run.stdout.lines().filter_map(|l| serde_json::from_str::<Value>(l).ok());
                let state = docs.next().ok_or("entry lookup printed no room state")?;
                Ok(json!({"room":state,"entries":docs.collect::<Vec<_>>()}))
            }
            "mini_pending_awaits" => {
                only_keys(arguments, &[])?;
                Ok(json!({"awaits": self.pending_awaits(true)?}))
            }
            "mini_stream_tail" => {
                only_keys(arguments, &["n", "since"])?;
                let n = bounded_decimal(arguments, "n", 6)?.unwrap_or_else(|| "100".into());
                let mut line = format!("tail --in {room} --json -n {n}");
                if let Some(since) = bounded_decimal(arguments, "since", 20)? {
                    line.push_str(&format!(" --since {since}"));
                }
                let run = Self::ok_or_ending(self.line(&line)?)?;
                let mut docs = run.stdout.lines().filter_map(|l| serde_json::from_str::<Value>(l).ok());
                let state = docs.next().ok_or("tail printed no room state")?;
                Ok(json!({"room":state,"entries":docs.collect::<Vec<_>>()}))
            }
            "mini_doc_context" => {
                only_keys(arguments,&["doc","maxRows","maxBytes"])?;
                let doc=bounded_name(arguments,"doc")?;
                let rows=bounded_decimal(arguments,"maxRows",3)?.unwrap_or_else(||"64".into());
                let bytes=bounded_decimal(arguments,"maxBytes",5)?.unwrap_or_else(||"8192".into());
                let run=Self::ok_or_ending(self.line(&format!("doc context {doc} {rows} {bytes}"))?)?;
                serde_json::from_str(run.stdout.trim()).map_err(|e|format!("signed context document output: {e}"))
            }
            "mini_doc_show" => {
                only_keys(arguments, &["doc"])?;
                let doc = bounded_name(arguments, "doc")?;
                let run = Self::ok_or_ending(self.line(&format!("doc show {doc}"))?)?;
                // `doc show` prints the text only; the links come from the
                // Host's link index (`doc links`).
                let links = Self::ok_or_ending(self.line(&format!("doc links {doc}"))?)?;
                Ok(json!({"doc":doc,"text":compact_doc_rendering(&run.stdout),"links":rendered_links(&links.stdout)}))
            }
            _ => Err(format!("{name} is not a room read tool")),
        }
    }

    /// One controller-chosen operation record, retained before the client's
    /// send boundary. Paths never come from model tool arguments.
    pub fn operation_record(&self, op: &str, effect: &str) -> Result<PathBuf> {
        if op.is_empty() || !op.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')
            || !matches!(effect, "payment" | "write") {
            return Err("invalid room operation identity".into());
        }
        let dir = self.config.workspace.join("room-operations");
        fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
        let meta = fs::symlink_metadata(&dir).map_err(|e| e.to_string())?;
        if !meta.is_dir() || meta.uid() != unsafe { libc::geteuid() } {
            return Err("room operation directory must be an owned real directory".into());
        }
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).map_err(|e| e.to_string())?;
        Ok(dir.join(format!("{op}-{effect}.json")))
    }

    /// Exact client lookup only. The controller must already have proved the
    /// submitter stopped before interpreting a missing record/call as absent.
    pub fn lookup_operation(&self, op: &str, effect: &str) -> Result<Value> {
        let record = self.operation_record(op, effect)?;
        match fs::symlink_metadata(&record) {
            Err(error) if error.kind() == std::io::ErrorKind::NotFound =>
                return Ok(json!({"resolution":"refused","basis":"operation-not-started","effect":effect})),
            Err(error) => return Err(format!("operation record metadata: {error}")),
            Ok(_) => {}
        }
        let mut command = Command::new(&self.config.mini);
        command.args(["credit", "--action", "lookup-operation", "--dir"])
            .arg(&self.config.workspace).arg("--operation-record").arg(&record)
            .arg("--socket").arg(&self.config.socket);
        let output = self.client(&mut command).map_err(|e| crate::deadline::describe("operation lookup", e))?;
        let recovered = last_json(&String::from_utf8_lossy(&output.stdout));
        let status = recovered.as_ref().filter(|v| v["type"] == "minidregg-operation-recovery-v1").and_then(|v| v["status"].as_str());
        let resolution = match status {
            Some("confirmed") => "performed",
            Some("refused") => "refused",
            // "The Host never got the write" is not "the Host refused the write": only the latter is a
            // verdict. It is its own resolution, so no caller can read it as a refusal by matching one value.
            Some("not-submitted") => "not-submitted",
            _ => "uncertain",
        };
        let basis = if status == Some("not-submitted") { "not-submitted" } else { "exact-operation-record" };
        Ok(json!({"resolution":resolution,"basis":basis,"effect":effect,
            "lookup":recovered,"exitCode":output.status.code()}))
    }

    /// A write whose submit failed on the transport (a reset before the Host held its bytes) is recorded by
    /// the client as `not-submitted`: it never reached the Host, so nothing can have happened. Submit the
    /// retained signed call once more, byte for byte (`retry --mode submit`); the Host admits an exact
    /// retry at most once and answers a call it already holds with its original receipt. Whatever this
    /// returns, the caller then asks the exact lookup again and records that answer. `None`: the write is
    /// not in the not-submitted state, so there is nothing to resubmit.
    pub fn resubmit_unsubmitted_write(&self, op: &str) -> Option<Result<()>> {
        let found = self.lookup_operation(op, "write").ok()?;
        if found["basis"] != "not-submitted" { return None; }
        let Some(attempt) = found["lookup"]["attempt"].as_str() else {
            return Some(Err("the operation record names no attempt to resubmit".into()));
        };
        // An attempt that failed before it was sealed holds no signed call (no call.bin): nothing was
        // ever signed or sent, so there is nothing to submit again and the write must be authored anew.
        if !Path::new(attempt).join("call.bin").exists() {
            return Some(Err(format!("the write was never sealed, so it holds no signed call to submit again (attempt {attempt}); author it anew")));
        }
        let mut command = Command::new(&self.config.mini);
        command.args(["retry", "--attempt"]).arg(attempt).args(["--mode", "submit", "--socket"]).arg(&self.config.socket);
        Some(match self.client(&mut command) {
            Ok(output) if output.status.success() => Ok(()),
            Ok(output) => Err(format!("exact resubmit exited {}: {}", output.status.code().map_or("by signal".into(), |c| c.to_string()),
                String::from_utf8_lossy(&output.stderr).chars().take(240).collect::<String>())),
            Err(error) => Err(crate::deadline::describe("exact resubmit", error)),
        })
    }

    /// Pay one turn for `tool` as operation `op`. Ok: the payment (or the
    /// room's statement that it does not charge). Err starting `out of
    /// budget:` when the Host refused the payment at plan.
    pub fn pay(&self, op: &str, tool: &str) -> Result<Value> {
        let Some(account) = &self.config.account else {
            return Ok(json!({"paid":false,"note":"unmetered"}));
        };
        let output = self.client(Command::new(&self.config.mini)
            .arg("credit")
            .arg("--action")
            .arg("turn")
            .arg("--dir")
            .arg(&self.config.workspace)
            .arg("--room")
            .arg(&self.config.room)
            .arg("--account")
            .arg(account)
            .arg("--memo")
            .arg(format!("op {op} {tool}"))
            .arg("--operation-record")
            .arg(self.operation_record(op, "payment")?)
            .arg("--socket")
            .arg(&self.config.socket))
            // A timed-out payment may have been sent: the caller recovers it by
            // its exact operation record, never by this error's text.
            .map_err(|e| crate::deadline::describe("the turn's payment", e))?;
        let stderr = String::from_utf8_lossy(&output.stderr);
        if !output.status.success() {
            let run = LineRun { code: output.status.code().unwrap_or(-1), stdout: String::new(), stderr: stderr.into_owned() };
            let ending = run.ending();
            if run.stderr.contains("bookRefused") {
                return Err(format!("out of budget: {ending}"));
            }
            return Err(format!("the turn's payment failed: {ending}"));
        }
        last_json(&String::from_utf8_lossy(&output.stdout)).ok_or_else(|| "the turn's payment printed no JSON".to_owned())
    }

    /// The proposal id of operation `op` (fixed: a rerun looks it up).
    pub fn proposal(op: &str) -> String {
        format!("hr-{op}")
    }

    /// A write tool as operation `op`, already paid for. `spawned` sees each
    /// child's pid (the submitter).
    pub fn write(&self, op: &str, name: &str, arguments: &Value, spawned: &mut dyn FnMut(u32)) -> Result<Value> {
        self.write_with_reply_guard(op,name,arguments,spawned,None)
    }

    /// Source-only stable thread guard; never taken from model tool arguments.
    pub fn write_with_reply_guard(&self, op: &str, name: &str, arguments: &Value,
        spawned: &mut dyn FnMut(u32), expected_reply: Option<(&str,u64)>) -> Result<Value> {
        if expected_reply.is_some() && (name != "mini_say" || arguments["re"].as_str().is_none()) {
            return Err("stable reply guard requires a threaded room say".into());
        }
        let id = Self::proposal(op);
        match name {
            "mini_say" => {
                only_keys(arguments, &["text", "to", "re"])?;
                let text = bounded_text(arguments, "text")?;
                let file = self.request_file(&format!("{id}.txt"), &text)?;
                let mut line = format!("say --in {} --operation-record {}", self.config.room, self.operation_record(op, "write")?.display());
                if let Some(to) = bounded_decimal(arguments, "to", 20)? {
                    line.push_str(&format!(" --to {to}"));
                }
                if let Some(re) = bounded_decimal(arguments, "re", 10)? {
                    line.push_str(&format!(" --re {re}"));
                }
                if let Some((cell,sequence)) = expected_reply {
                    if cell.is_empty() || cell.len()>39 || !cell.bytes().all(|b|b.is_ascii_digit())
                        || (cell.len()>1 && cell.starts_with('0')) || sequence==0 {
                        return Err("invalid stable reply reference".into());
                    }
                    line.push_str(&format!(" --expect-re-cell {cell} --expect-re-sequence {sequence}"));
                }
                line.push_str(&format!(" --file {file}"));
                let run = Self::ok_or_ending(self.line_with(&line, spawned)?)?;
                Ok(json!({"said":run.stdout.trim(),"text":text}))
            }
            "mini_doc_review" => {
                let (context,request)=crate::resident_context::reviewed_arguments(arguments)?;
                let dir=self.config.home.join("requests");
                fs::create_dir_all(&dir).map_err(|e|e.to_string())?;
                let metadata=fs::symlink_metadata(&dir).map_err(|e|e.to_string())?;
                if !metadata.is_dir()||metadata.uid()!=unsafe{libc::geteuid()} {
                    return Err("review requests must be an owned real directory".into());
                }
                fs::set_permissions(&dir,fs::Permissions::from_mode(0o700)).map_err(|e|e.to_string())?;
                let context_name=format!("{id}-context.json");
                let request_name=format!("{id}-review.json");
                crate::resident_context::retain_review_file(&dir.join(&context_name),&context)?;
                crate::resident_context::retain_review_file(&dir.join(&request_name),&request)?;
                if !self.config.workspace.join("proposals").join(&id).join("proposal.json").exists() {
                    Self::ok_or_ending(self.line(&format!("doc review {id} @{context_name} @{request_name}"))?)?;
                }
                let run=Self::ok_or_ending(self.line_with(&format!("submit {id}"),spawned)?)?;
                Ok(json!({"proposal":id,"reviewed":true,"support":"selected-current-base-native-guards","submitted":run.stdout.trim()}))
            }
            "mini_doc_link" | "mini_doc_append" => {
                let propose = if name == "mini_doc_link" {
                    only_keys(arguments, &["from", "to", "relation"])?;
                    let from = bounded_name(arguments, "from")?;
                    let to = bounded_name(arguments, "to")?;
                    let relation = bounded_decimal(arguments, "relation", 10)?.unwrap_or_else(|| "0".into());
                    format!("doc link {id} {from} {to} {relation}")
                } else {
                    only_keys(arguments, &["doc", "text"])?;
                    let doc = bounded_name(arguments, "doc")?;
                    let text = bounded_text(arguments, "text")?;
                    let file = self.request_file(&format!("{id}.txt"), &text)?;
                    format!("doc append {id} {doc} @{file}")
                };
                if !self.config.workspace.join("proposals").join(&id).join("proposal.json").exists() {
                    Self::ok_or_ending(self.line(&propose)?)?;
                }
                let run = Self::ok_or_ending(self.line_with(&format!("submit {id}"), spawned)?)?;
                Ok(json!({"proposal":id,"submitted":run.stdout.trim()}))
            }
            "mini_answer_await" => {
                let (slot, answer) = await_answer(arguments)?;
                // The room's allowance, read fresh: the slot must belong to an await a member
                // announced here. Who decides it and whether it is still open is the kernel's.
                if !self.pending_awaits(false)?.iter().any(|a| a["slot"].as_str() == Some(slot.as_str())) {
                    return Err(format!("refused: await-not-in-room: no await announced in {} has slot {slot}", self.config.room));
                }
                let dir = self.config.workspace.join("answers");
                fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
                fs::write(dir.join(format!("{id}.json")), json!({"slot":slot}).to_string()).map_err(|e| e.to_string())?;
                let file = self.request_file(&format!("{id}-answer.json"), &answer.to_string())?;
                let run = Self::ok_or_ending(self.line_with(&format!("bend answer {slot} @{file}"), spawned)?)?;
                Ok(json!({"slot":slot,"answered":run.stdout.trim()}))
            }
            _ => Err(format!("{name} is not a room write tool")),
        }
    }

    /// The awaits members announced in this room, read through the Host. With `mine`, only those
    /// whose current await is a reply slot this workspace's subject decides.
    fn pending_awaits(&self, mine: bool) -> Result<Vec<Value>> {
        let me = fs::read(self.config.workspace.join("workspace.json")).ok().and_then(|b| serde_json::from_slice::<Value>(&b).ok())
            .and_then(|ws| ws["subject"].as_str().map(str::to_owned)).ok_or("the resident's workspace names no subject")?;
        let tail = self.read("mini_stream_tail", &json!({"n":"200"}))?;
        let entries: Vec<Value> = tail["entries"].as_array().cloned().unwrap_or_default();
        let mut awaits = Vec::new();
        for (object, transaction, announced_by) in announced_awaits(&entries, &me) {
            let run = Self::ok_or_ending(self.line(&format!("bend await {object} {transaction}"))?)?;
            let Some(view) = last_json(&run.stdout) else { continue };
            if view["phase"] != "awaiting" || view["slot"].is_null() { continue; }
            if mine && view["decider"].as_str() != Some(me.as_str()) { continue; }
            awaits.push(json!({"object":object,"transaction":transaction,"announcedBy":announced_by,
                "slot":view["slot"],"decider":view["decider"],"deadline":view["deadline"],"height":view["height"],
                "state":view["stateText"]}));
        }
        Ok(awaits)
    }

    /// Exact lookup of operation `op`'s submission (never a resend): its
    /// attempt's outcome after `mini workspace --action recover`.
    pub fn lookup(&self, op: &str) -> Result<Value> {
        let id = Self::proposal(op);
        let answer = self.config.workspace.join("answers").join(format!("{id}.json"));
        if answer.exists() {
            // A resolve turn: its exact retained ingress, looked up by `bend lookup` (never resent).
            let slot = fs::read(&answer).ok().and_then(|b| serde_json::from_slice::<Value>(&b).ok()).and_then(|a| a["slot"].as_str().map(str::to_owned)).ok_or("answer record has no slot")?;
            let name = format!("answer-{}", &crate::sha256_bytes(slot.as_bytes())?[..16]);
            let run = self.line(&format!("bend lookup {name}"))?;
            if run.code == 0 && run.stdout.contains("admitted:") {
                return Ok(json!({"resolution":"performed","basis":"exact-lookup","proposal":id,"detail":run.stdout.trim()}));
            }
            if run.code == 3 || run.stdout.contains("no attempt") || run.stderr.contains("no attempt") {
                return Ok(json!({"resolution":"refused","basis":"host-refusal-or-not-submitted","proposal":id,"detail":run.ending()}));
            }
            return Ok(json!({"resolution":"uncertain","basis":"lookup-inconclusive","proposal":id,"detail":run.ending()}));
        }
        let attempt = self.config.workspace.join("attempts").join(&id);
        if !attempt.join("call.bin").exists() {
            return Ok(json!({"resolution":"refused","basis":"not-submitted","proposal":id}));
        }
        let run = self.line(&format!("lookup {id}"))?;
        let outcome: Option<Value> = fs::read(attempt.join("outcome.json")).ok().and_then(|b| serde_json::from_slice(&b).ok());
        let accepted = outcome.as_ref().is_some_and(|o| o["type"] == "confirmed" && matches!(o["confirmation"].as_str(), Some("installed" | "replayed")));
        if accepted {
            return Ok(json!({"resolution":"performed","basis":"exact-lookup","proposal":id,"outcome":outcome}));
        }
        if last_json(&run.stdout).as_ref().is_some_and(|o| o["type"] == "absent") {
            return Ok(json!({"resolution":"refused","basis":"absent-after-submitter-stop","proposal":id}));
        }
        if run.code == 3 || outcome.as_ref().and_then(|o| o.get("type")).and_then(Value::as_str) == Some("refused") {
            return Ok(json!({"resolution":"refused","basis":"host-refusal","proposal":id,"detail":run.ending()}));
        }
        Ok(json!({"resolution":"uncertain","basis":"lookup-inconclusive","proposal":id,"detail":run.ending()}))
    }

    /// A source-only request-status entry (never a model tool): one typed
    /// `say --status` replying to the request's feed number, guarded by its
    /// stable cell/sequence, addressed to its author, under the exact write
    /// record of operation `op`. Re-entering looks the record up.
    pub fn write_status(&self, op: &str, notice: &crate::resident_requests::Notice) -> Result<Value> {
        if !crate::resident_requests::STATUSES.contains(&notice.status.as_str()) || notice.text.is_empty()
            || notice.sequence == 0
            || !notice.author.bytes().all(|b| b.is_ascii_digit()) || !notice.cell.bytes().all(|b| b.is_ascii_digit()) {
            return Err("request-status notice is malformed".into());
        }
        // The feed number moves as history grows: take it from a fresh signed
        // read of the exact request (which also refreshes the number the
        // client resolves `--re` against), as the final reply does.
        let fresh = self.read("mini_stream_entry", &json!({"cell":notice.cell,"sequence":notice.sequence.to_string()}))?;
        let numbers: Vec<u64> = fresh["entries"].as_array().into_iter().flatten()
            .filter(|e| e["author"] == notice.author && e["cell"] == notice.cell && e["sequence"] == notice.sequence)
            .filter_map(|e| e["n"].as_u64()).collect();
        let [number] = numbers[..] else {
            return Err("request entry absent or ambiguous in fresh signed room history".into());
        };
        let file = self.request_file(&format!("{}.txt", Self::proposal(op)), &notice.text)?;
        let line = format!("say --in {} --operation-record {} --to {} --re {number} --expect-re-cell {} --expect-re-sequence {} --status {} --file {file}",
            self.config.room, self.operation_record(op, "write")?.display(), notice.author,
            notice.cell, notice.sequence, notice.status);
        let run = Self::ok_or_ending(self.line(&line)?)?;
        Ok(json!({"said":run.stdout.trim()}))
    }

    /// An unmetered notice in Hermes's stream (the one write that is not a
    /// turn: saying that the budget is spent).
    pub fn notice(&self, text: &str) -> Result<LineRun> {
        let file = self.request_file("hr-notice.txt", text)?;
        Self::ok_or_ending(self.line(&format!("say --in {} --file {file}", self.config.room))?)
    }
}

#[cfg(test)]
mod tests {

    #[test]
    fn only_awaits_a_member_announced_are_answerable_and_answers_are_shaped() {
        let entries = vec![
            json!({"author":"21","text":"hermes, please answer await 12 34 when you can"}),
            json!({"author":"8","text":"await 99 1"}),
            json!({"author":"22","text":"await 12 34 again, and await 56 78"}),
            json!({"author":"21","text":"await x 1 and await 1"}),
        ];
        let found = announced_awaits(&entries, "8");
        assert_eq!(found, vec![("12".into(),"34".into(),"22".into()), ("56".into(),"78".into(),"22".into())],
            "newest first, deduplicated, never the resident's own words, decimals only");
        assert_eq!(await_answer(&json!({"slot":"5","reply":{"tag":"natural","value":"7"}})).unwrap().1,
            json!({"reply":{"tag":"natural","value":"7"}}));
        assert_eq!(await_answer(&json!({"slot":"5","refused":"no"})).unwrap().1, json!({"refused":"no"}));
        assert!(await_answer(&json!({"slot":"5"})).is_err());
        assert!(await_answer(&json!({"slot":"5","reply":{},"refused":"no"})).is_err());
        assert!(await_answer(&json!({"slot":"x","refused":"no"})).is_err());
        assert!(validate_room_write("mini_answer_await", &json!({"slot":"5","refused":"no"})).is_ok());
        assert!(is_room_tool("mini_pending_awaits") && is_room_tool("mini_answer_await"));
    }
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn a_lookup_keeps_a_never_submitted_write_apart_from_a_host_refusal() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("mini-lookup-basis-{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir_all(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let fake = root.join("mini");
        fs::write(&fake, "#!/bin/sh\ncase \"$*\" in\n*lookup-operation*) echo \"{\\\"type\\\":\\\"minidregg-operation-recovery-v1\\\",\\\"status\\\":\\\"$STATUS\\\"}\" ;;\n*) exit 9 ;;\nesac\n").unwrap();
        fs::set_permissions(&fake, fs::Permissions::from_mode(0o700)).unwrap();
        let config: RoomToolsConfig = serde_json::from_value(json!({"mini":fake,"host":"/h","hostConfig":"/c",
            "socket":"/s","workspace":root,"home":root,"room":"lab"})).unwrap();
        let tools = RoomTools { config: &config };
        fs::write(tools.operation_record("g1", "write").unwrap(), b"{}").unwrap();
        for (status, resolution, basis) in [("not-submitted", "not-submitted", "not-submitted"),
            ("refused", "refused", "exact-operation-record"), ("confirmed", "performed", "exact-operation-record")] {
            std::env::set_var("STATUS", status);
            let found = tools.lookup_operation("g1", "write").unwrap();
            assert_eq!((found["resolution"].as_str(), found["basis"].as_str()), (Some(resolution), Some(basis)), "{status}");
        }
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn a_never_submitted_write_is_resubmitted_once_and_then_looked_up_again() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("mini-resubmit-{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir_all(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let state = root.join("state");
        fs::write(&state, "not-submitted").unwrap();
        let fake = root.join("mini");
        fs::write(&fake, format!("#!/bin/sh\ncase \"$*\" in\n*lookup-operation*) echo \"{{\\\"type\\\":\\\"minidregg-operation-recovery-v1\\\",\\\"status\\\":\\\"$(cat '{s}')\\\",\\\"attempt\\\":\\\"/a/1\\\"}}\" ;;\nretry*--attempt\\ /a/1\\ --mode\\ submit*) echo confirmed > '{s}' ;;\n*) exit 9 ;;\nesac\n", s = state.display())).unwrap();
        fs::set_permissions(&fake, fs::Permissions::from_mode(0o700)).unwrap();
        let config: RoomToolsConfig = serde_json::from_value(json!({"mini":fake,"host":"/h","hostConfig":"/c",
            "socket":"/s","workspace":root,"home":root,"room":"lab"})).unwrap();
        let tools = RoomTools { config: &config };
        fs::write(tools.operation_record("g1", "write").unwrap(), b"{}").unwrap();
        // not-submitted: resubmitted, and the lookup that follows decides.
        assert!(matches!(tools.resubmit_unsubmitted_write("g1"), Some(Ok(()))));
        assert_eq!(tools.lookup_operation("g1", "write").unwrap()["resolution"], "performed");
        // A write the Host holds (confirmed) or refused is never resubmitted.
        assert!(tools.resubmit_unsubmitted_write("g1").is_none());
        fs::write(&state, "refused").unwrap();
        assert!(tools.resubmit_unsubmitted_write("g1").is_none());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn restrict_tools_is_on_unless_a_config_turns_it_off() {
        let base = json!({"mini":"/m","host":"/h","hostConfig":"/c","socket":"/s",
            "workspace":"/w","home":"/home","room":"lab"});
        let config: RoomToolsConfig = serde_json::from_value(base.clone()).unwrap();
        assert!(config.restrict_tools);
        let mut off = base;
        off["restrictTools"] = json!(false);
        let config: RoomToolsConfig = serde_json::from_value(off).unwrap();
        assert!(!config.restrict_tools);
    }

    #[test]
    fn discovery_pipes_bounded_json_and_never_reads_model_paths() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("mini-discovery-pipe-{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&root).unwrap();
        let mini = root.join("mini");
        let received = root.join("received.json");
        let argv = root.join("argv.txt");
        fs::write(&mini, format!("#!/bin/sh\nprintf '%s\\n' \"$@\" > '{}'\ncat > '{}'\nprintf '{{\"type\":\"room\"}}\\n'\n", argv.display(), received.display())).unwrap();
        fs::set_permissions(&mini, fs::Permissions::from_mode(0o700)).unwrap();
        let config = RoomToolsConfig { restrict_tools:true, mini, host:"/unused".into(), host_config:"/unused".into(), socket:"/unused".into(), workspace:root.join("workspace"), home:root.join("home"), room:"lab".into(), account:None };
        let tools = RoomTools { config:&config };
        assert!(tools.read("mini_stream_discovery", &json!({"cursorFile":"/etc/passwd","n":"10"})).is_err());
        assert!(!received.exists());
        let cursor = json!({"type":"mini-resident-discovery-v1","cursors":{},"retained":[],"padding":"x".repeat(140000)});
        let expected = serde_json::to_vec(&cursor).unwrap();
        assert!(tools.read("mini_stream_discovery", &json!({"cursor":cursor,"n":"10"})).is_ok());
        assert_eq!(fs::read(&received).unwrap(), expected);
        assert!(fs::read_to_string(&argv).unwrap().contains("tail --in lab --json --discover-json - -n 10"));
        let huge = json!({"padding":"x".repeat(262144)});
        assert!(tools.read("mini_stream_discovery", &json!({"cursor":huge,"n":"10"})).is_err());
        assert_eq!(fs::read(&received).unwrap(), expected);
        fs::remove_dir_all(root).unwrap();
    }

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
    fn supervised_read_runner_can_refuse_before_native_spawn() {
        let suffix = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let state = std::env::temp_dir().join(format!("mini-supervised-read-{suffix}"));
        fs::create_dir(&state).unwrap();
        let config: Config = serde_json::from_value(json!({
            "mini":"/unused/mini","host":"/unused/host",
            "hostConfig":"/unused/config","controlSocket":"/unused/control.sock",
            "custodyKey":"/unused/parent.key","stateDir":state,
            "cwd":"/unused/workspace","task":"1","subject":"7",
            "capability":"71","queryCapability":"72","commands":[]
        }))
        .unwrap();
        let tool: ToolTask = serde_json::from_value(json!({
            "task":"2","subject":"8","capability":"81",
            "queryCapability":"82","custodyKey":"/unused/tool.key",
            "parentCapability":"83","parentObserveCapability":"84",
            "reserve":"3","charge":"1","allowedPublications":[]
        }))
        .unwrap();
        let read = AllowedResourceRead {
            name: "shared-app".into(),
            kind: "object".into(),
            target: "100".into(),
            observe_capability: "90".into(),
            max_result_bytes: 1024,
            fn_inbox_summary: false,
        };
        let mut entered = false;
        let error = read_resource_with(&config, &tool, &read, 5, ResourceReadSigner::Tool, |command| {
            entered = true;
            assert_eq!(command.get_program(), "/unused/mini");
            Err("fenced before spawn".into())
        })
        .unwrap_err();
        assert!(entered && error.contains("fenced before spawn"));
        let dir = config.state_dir.join("resource-read-0000000000000005");
        let intent: Value =
            serde_json::from_slice(&fs::read(dir.join("intent-source.json")).unwrap()).unwrap();
        assert_eq!(intent["grants"][0]["capability"], "90");
        assert_eq!(intent["subject"], "8");
        assert!(!dir.join("attempt").exists());
        let error = read_resource_with(
            &config, &tool, &read, 6, ResourceReadSigner::Controller, |command| {
                let args = command.get_args().collect::<Vec<_>>();
                let key = args.iter().position(|arg| *arg == "--key").unwrap();
                assert_eq!(args[key + 1], config.custody_key.as_os_str());
                Err("controller fenced before spawn".into())
            },
        ).unwrap_err();
        assert!(error.contains("controller fenced before spawn"));
        let dir = config.state_dir.join("resource-read-0000000000000006");
        let intent: Value =
            serde_json::from_slice(&fs::read(dir.join("intent-source.json")).unwrap()).unwrap();
        assert_eq!(intent["subject"], "7");
        assert_eq!(intent["grants"][0]["capability"], "90");
        assert_eq!(intent["purpose"]["target"], "100");
        assert!(!dir.join("attempt").exists());
        // A static name must not borrow the signer selected for a born member
        // of the same name. Reject before choosing either grant/target pair.
        let mut conflicting = read.clone();
        conflicting.target = "999".into();
        assert!(select_read(&[read.clone(), conflicting], &json!({"name":read.name})).is_err());
        let mut task_grant = read.clone();
        task_grant.observe_capability = config.capability.clone();
        assert!(read_resource_with(
            &config, &tool, &task_grant, 7, ResourceReadSigner::Controller,
            |_| panic!("task mutation grant must refuse before spawn"),
        ).is_err());
        assert!(!config.state_dir.join("resource-read-0000000000000007").exists());
        fs::remove_dir_all(&config.state_dir).unwrap();
    }

    #[test]
    fn content_birth_uses_exact_factory_payer_tool_parent_footprint() {
        let family = birth_family();
        let tool = ToolTask {
            room: None,
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
            resource_workspace: None,
            allowed_birth_families: vec![],
            allowed_application_families: vec![],
            allowed_session_families: vec![],
            registered_shared_applications: vec![],
            allowed_application_api_routes: vec![],
            allowed_application_lifetime_routes: vec![],
            application_services: vec![],
            typed_applications: vec![],
            agent_api_host_sha256: None,
            lifetime_api_host_sha256: None,
            current_birth_host_sha256: None,
        };
        let peer = |root: &str| {
            json!({"authorityRoot":"123","targetRoot":root,"height":"20",
            "worldRoot":"456",
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
        stale_parent["worldRoot"] = json!("457");
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

    /// The room tools ARE the spec table (no list kept beside it), and metering is structural: every
    /// spec is exactly one of a write tool (ROOM_WRITE_TOOLS, the only names the resident pays a room
    /// turn for, which the unmetered read path refuses) or a read tool (the read path handles it, and
    /// it has no write arm). A tool added to the table without a side fails here.
    #[test]
    fn room_tools_are_the_spec_table_and_every_write_is_metered() {
        use std::os::unix::fs::PermissionsExt;
        let names: Vec<String> = super::room_tool_specs().iter().map(|s| s["name"].as_str().unwrap().to_owned()).collect();
        let mut unique = names.clone();
        unique.sort();
        unique.dedup();
        assert_eq!(unique.len(), names.len(), "each tool is named once: {names:?}");
        for write in super::ROOM_WRITE_TOOLS {
            assert!(names.iter().any(|n| n == write), "{write} is metered but not offered");
        }
        let root = std::env::temp_dir().join(format!("mini-room-sides-{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&root).unwrap();
        let mini = root.join("mini");
        let ran = root.join("ran.txt");
        fs::write(&mini, format!("#!/bin/sh\nprintf '%s\\n' \"$*\" >> '{}'\nexit 7\n", ran.display())).unwrap();
        fs::set_permissions(&mini, fs::Permissions::from_mode(0o700)).unwrap();
        let config = RoomToolsConfig { restrict_tools:true, mini, host:"/unused".into(), host_config:"/unused".into(), socket:"/unused".into(), workspace:root.join("workspace"), home:root.join("home"), room:"lab".into(), account:Some("lab-hermes".into()) };
        let tools = RoomTools { config:&config };
        for name in &names {
            let read = tools.read(name, &json!({}));
            let not_read = matches!(&read, Err(e) if e == &format!("{name} is not a room read tool"));
            if super::ROOM_WRITE_TOOLS.contains(&name.as_str()) {
                assert!(not_read, "{name} writes, so the unmetered read path must refuse it: {read:?}");
            } else {
                assert!(!not_read, "{name} is offered and not metered, so it must be a read tool");
                let write = tools.write("op1", name, &json!({}), &mut |_| {});
                assert!(matches!(&write, Err(e) if e == &format!("{name} is not a room write tool")),
                    "{name} is not metered, so it must have no write arm: {write:?}");
            }
        }
        // No read ever spends: nothing a read tool ran names an operation record (the write's payment proof).
        let lines = fs::read_to_string(&ran).unwrap_or_default();
        assert!(!lines.contains("--operation-record") && !lines.contains("pay"), "{lines}");
        let _ = fs::remove_dir_all(&root);
        // The seams are not offered.
        assert!(!super::is_room_tool("mini_doc_quote") && !super::is_room_tool("mini_doc_history"));
        // No tool takes a room, a capability or a proposal id from the model.
        for spec in super::room_tool_specs() {
            let props = spec["inputSchema"]["properties"].as_object().unwrap();
            for forbidden in ["room", "capability", "proposalId", "operation", "account"] {
                assert!(!props.contains_key(forbidden), "{} takes {forbidden}", spec["name"]);
            }
        }
    }

    #[test]
    fn rendered_links_name_their_targets() {
        let text = "# doc lab-index: document 77 cell root 1 at height 9\n  1  created-by 7   map\nlink 3 -> lab-cell-501 (document 501) relation 0 created-by 42\nlink 4 -> object 502 relation 0 created-by 42\n# 3 cell entries\n";
        assert_eq!(super::rendered_links(text), vec!["501".to_owned(), "502".to_owned()]);
        // `doc links` as the client prints it: by ID, or by name with the ID.
        let links = "# links from lab-index (document 77) at height 9\nlink 3 -> object 501 relation 0 revision 4 since 8\nlink 5 -> object lab-cell-502 (target 502) relation 0 revision 6 since 9\n# 2 links\n";
        assert_eq!(super::rendered_links(links), vec!["501".to_owned(), "502".to_owned()]);
    }

    #[test]
    fn the_last_printed_json_document_is_read() {
        let out = "paid\n{\n  \"a\": 1\n}\n{\n  \"b\": {\"c\": 2}\n}\n";
        assert_eq!(super::last_json(out), Some(serde_json::json!({"b":{"c":2}})));
        assert_eq!(super::last_json("no json here"), None);
    }

    #[test]
    fn room_tool_arguments_are_bounded() {
        assert!(super::bounded_name(&serde_json::json!({"doc":"lab-index"}), "doc").is_ok());
        assert!(super::bounded_name(&serde_json::json!({"doc":"../x"}), "doc").is_err());
        assert!(super::bounded_name(&serde_json::json!({"doc":"a b"}), "doc").is_err());
        assert!(super::bounded_decimal(&serde_json::json!({"since":"12"}), "since", 20).unwrap() == Some("12".into()));
        assert!(super::bounded_decimal(&serde_json::json!({"since":12}), "since", 20).is_err());
        assert!(super::bounded_text(&serde_json::json!({"text":"hi\u{0007}"}), "text").is_err());
        assert!(super::only_keys(&serde_json::json!({"doc":"x","room":"y"}), &["doc"]).is_err());
    }
}
