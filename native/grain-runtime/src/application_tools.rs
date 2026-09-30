//! Operator-selected namespaces for metered application and session births.
//!
//! These checks are configuration bounds, not Mini admission. The native
//! source author and receiver decide the actual cells, grants, fee, current
//! authority, and durable transition.
use crate::resource_tools::{self, AllowedBirthFamily, AllowedResourceRead, BornResource};
use crate::{PublicationGrant, Result, ToolTask};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};

const MAX_FAMILIES: usize = 8;
const MAX_BIRTHS: u16 = 1024;
const MAX_SOURCE_TEMPLATE_BYTES: usize = 131_072;
const MAX_RESULT_BYTES: usize = 4 * 1024 * 1024;

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct BirthProfile {
    pub genesis: Value,
    pub template: Value,
    pub factory_target: String,
    pub factory_observe_capability: String,
    pub payer_account: String,
    pub payer_capability: String,
    pub payer_observe_capability: String,
    pub tariff_base: String,
    pub tariff_per_birth: String,
}

/// The ordered target/capability starts correspond to the source-owned
/// ApplicationGrainBirth.Spec fields. Every range is reserved for all ordinals
/// in the family, including ordinals not yet used.
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct ApplicationNamespace {
    pub app: String,
    pub package_manifest: String,
    pub snapshot_manifest: String,
    pub app_owner_capability: String,
    pub app_control_capability: String,
    pub package_owner_capability: String,
    pub package_control_capability: String,
    pub snapshot_owner_capability: String,
    pub snapshot_control_capability: String,
}

impl ApplicationNamespace {
    fn targets(&self) -> [&str; 3] {
        [&self.app, &self.package_manifest, &self.snapshot_manifest]
    }
    fn capabilities(&self) -> [&str; 6] {
        [
            &self.app_owner_capability,
            &self.app_control_capability,
            &self.package_owner_capability,
            &self.package_control_capability,
            &self.snapshot_owner_capability,
            &self.snapshot_control_capability,
        ]
    }
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct ApplicationFamily {
    pub name: String,
    pub profile: BirthProfile,
    pub namespace: ApplicationNamespace,
    pub max_births: u16,
    pub max_result_bytes: usize,
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct SessionNamespace {
    pub session: String,
    pub descriptor: String,
    pub session_owner_capability: String,
    pub session_control_capability: String,
    pub descriptor_owner_capability: String,
    pub descriptor_control_capability: String,
}

impl SessionNamespace {
    fn targets(&self) -> [&str; 2] {
        [&self.session, &self.descriptor]
    }
    fn capabilities(&self) -> [&str; 4] {
        [
            &self.session_owner_capability,
            &self.session_control_capability,
            &self.descriptor_owner_capability,
            &self.descriptor_control_capability,
        ]
    }
}

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct SessionFamily {
    pub name: String,
    /// A named, retained application bundle is selected at execution. No
    /// caller-provided raw app ID is accepted by the public tool.
    pub application_family: String,
    pub kind: String,
    pub profile: BirthProfile,
    pub namespace: SessionNamespace,
    pub max_births: u16,
    pub max_result_bytes: usize,
}

#[derive(Clone)]
struct FamilyRanges {
    name: String,
    targets: Vec<(u64, u64)>,
    capabilities: Vec<(u64, u64)>,
}

fn family_name(name: &str) -> Result<()> {
    if name.is_empty()
        || name.len() > 32
        || !name
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || byte == b'-')
    {
        return Err(
            "application birth family name must be 1..32 ASCII letters, digits or '-'".into(),
        );
    }
    Ok(())
}

fn range(start: &str, count: u16) -> Result<(u64, u64)> {
    crate::decimal(start, "application birth namespace start")?;
    let first = start
        .parse::<u64>()
        .map_err(|_| "application birth namespace start exceeds u64")?;
    let last = first
        .checked_add(u64::from(count - 1))
        .ok_or("application birth namespace overflows u64")?;
    Ok((first, last))
}

fn in_range(value: &str, range: (u64, u64)) -> bool {
    value
        .parse::<u64>()
        .is_ok_and(|id| range.0 <= id && id <= range.1)
}

fn overlaps(a: (u64, u64), b: (u64, u64)) -> bool {
    a.0 <= b.1 && b.0 <= a.1
}

fn validate_profile(profile: &BirthProfile) -> Result<()> {
    if !profile.genesis.is_object() || !profile.template.is_object() {
        return Err("application birth genesis and template must be objects".into());
    }
    let size = serde_json::to_vec(&[&profile.genesis, &profile.template])
        .map_err(|e| e.to_string())?
        .len();
    if size > MAX_SOURCE_TEMPLATE_BYTES {
        return Err("application birth source template exceeds bound".into());
    }
    for (value, label) in [
        (&profile.factory_target, "factoryTarget"),
        (
            &profile.factory_observe_capability,
            "factoryObserveCapability",
        ),
        (&profile.payer_account, "payerAccount"),
        (&profile.payer_capability, "payerCapability"),
        (&profile.payer_observe_capability, "payerObserveCapability"),
        (&profile.tariff_base, "tariffBase"),
        (&profile.tariff_per_birth, "tariffPerBirth"),
    ] {
        crate::decimal(value, label)?;
    }
    if profile.tariff_base == "0" {
        return Err("application birth tariffBase must be positive".into());
    }
    Ok(())
}

/// This is only a reserve preflight bound. Lean derives and checks the fee.
pub(super) fn planned_charge(profile: &BirthProfile, resource_count: u64) -> Result<String> {
    let base = profile
        .tariff_base
        .parse::<u64>()
        .map_err(|_| "application birth tariffBase exceeds u64")?;
    let per_birth = profile
        .tariff_per_birth
        .parse::<u64>()
        .map_err(|_| "application birth tariffPerBirth exceeds u64")?;
    base.checked_add(
        per_birth
            .checked_mul(resource_count)
            .ok_or("application birth tariff exceeds u64")?,
    )
    .map(|charge| charge.to_string())
    .ok_or("application birth tariff exceeds u64".into())
}

fn own_ranges(
    name: &str,
    count: u16,
    targets: &[&str],
    capabilities: &[&str],
) -> Result<FamilyRanges> {
    family_name(name)?;
    if count == 0 || count > MAX_BIRTHS {
        return Err(format!("{name} maxBirths must be 1..{MAX_BIRTHS}"));
    }
    let targets = targets
        .iter()
        .map(|start| range(start, count))
        .collect::<Result<Vec<_>>>()?;
    let capabilities = capabilities
        .iter()
        .map(|start| range(start, count))
        .collect::<Result<Vec<_>>>()?;
    Ok(FamilyRanges {
        name: name.to_owned(),
        targets,
        capabilities,
    })
}

/// Reject every overlap before any allowance is reserved. Target and
/// capability identities have separate namespaces, but every range in one
/// namespace is compared with every configured family and fixed peer ID.
/// `shared_application_families` comes from validated operator references;
/// it allows a session namespace without pretending the external app was
/// locally born.
pub(super) fn validate_families(
    applications: &[ApplicationFamily],
    sessions: &[SessionFamily],
    shared_application_families: &[&str],
    content: &[AllowedBirthFamily],
    reads: &[AllowedResourceRead],
    publications: &[PublicationGrant],
    peer_ids: (&[&str], &[&str]),
) -> Result<()> {
    if applications.len() > MAX_FAMILIES || sessions.len() > MAX_FAMILIES {
        return Err(
            "at most eight application and eight session families may be configured".into(),
        );
    }
    let mut families = Vec::new();
    let mut fixed_targets = peer_ids
        .0
        .iter()
        .map(|s| (*s).to_owned())
        .collect::<Vec<_>>();
    let mut fixed_capabilities = peer_ids
        .1
        .iter()
        .map(|s| (*s).to_owned())
        .collect::<Vec<_>>();
    fixed_targets.extend(reads.iter().map(|read| read.target.clone()));
    fixed_targets.extend(publications.iter().map(|grant| grant.target.clone()));
    fixed_capabilities.extend(reads.iter().map(|read| read.observe_capability.clone()));
    fixed_capabilities.extend(
        publications
            .iter()
            .flat_map(|grant| [grant.capability.clone(), grant.observe_capability.clone()]),
    );
    for family in content {
        families.push(own_ranges(
            &family.name,
            family.max_births,
            &[&family.target_start],
            &[
                &family.owner_capability_start,
                &family.control_capability_start,
            ],
        )?);
        fixed_targets.extend([family.factory_target.clone(), family.payer_account.clone()]);
        fixed_capabilities.extend([
            family.factory_observe_capability.clone(),
            family.payer_capability.clone(),
            family.payer_observe_capability.clone(),
        ]);
    }
    for family in applications {
        validate_profile(&family.profile)?;
        if family.max_result_bytes == 0 || family.max_result_bytes > MAX_RESULT_BYTES {
            return Err(format!("{} maxResultBytes exceeds bound", family.name));
        }
        planned_charge(&family.profile, 3)?;
        families.push(own_ranges(
            &family.name,
            family.max_births,
            &family.namespace.targets(),
            &family.namespace.capabilities(),
        )?);
        fixed_targets.extend([
            family.profile.factory_target.clone(),
            family.profile.payer_account.clone(),
        ]);
        fixed_capabilities.extend([
            family.profile.factory_observe_capability.clone(),
            family.profile.payer_capability.clone(),
            family.profile.payer_observe_capability.clone(),
        ]);
    }
    for family in sessions {
        validate_profile(&family.profile)?;
        if family.max_result_bytes == 0 || family.max_result_bytes > MAX_RESULT_BYTES {
            return Err(format!("{} maxResultBytes exceeds bound", family.name));
        }
        if !matches!(family.kind.as_str(), "web" | "api") {
            return Err(format!("{} session kind must be web or api", family.name));
        }
        if !applications
            .iter()
            .any(|app| app.name == family.application_family)
            && !shared_application_families
                .iter()
                .any(|name| *name == family.application_family)
        {
            return Err(format!(
                "{} has no local or registered shared application family",
                family.name
            ));
        }
        planned_charge(&family.profile, 2)?;
        families.push(own_ranges(
            &family.name,
            family.max_births,
            &family.namespace.targets(),
            &family.namespace.capabilities(),
        )?);
        fixed_targets.extend([
            family.profile.factory_target.clone(),
            family.profile.payer_account.clone(),
        ]);
        fixed_capabilities.extend([
            family.profile.factory_observe_capability.clone(),
            family.profile.payer_capability.clone(),
            family.profile.payer_observe_capability.clone(),
        ]);
    }
    for (index, family) in families.iter().enumerate() {
        if families[..index]
            .iter()
            .any(|prior| prior.name == family.name)
            || reads.iter().any(|read| read.name == family.name)
        {
            return Err(format!("{} family name is not unique", family.name));
        }
        for (label, ranges, fixed) in [
            ("target", &family.targets, &fixed_targets),
            ("capability", &family.capabilities, &fixed_capabilities),
        ] {
            for (position, candidate) in ranges.iter().enumerate() {
                if fixed.iter().any(|id| in_range(id, *candidate))
                    || ranges[..position]
                        .iter()
                        .any(|prior| overlaps(*prior, *candidate))
                    || families[..index].iter().any(|prior| {
                        let other = if label == "target" {
                            &prior.targets
                        } else {
                            &prior.capabilities
                        };
                        other.iter().any(|range| overlaps(*range, *candidate))
                    })
                {
                    return Err(format!(
                        "{} {label} namespace overlaps configured authority",
                        family.name
                    ));
                }
            }
        }
    }
    Ok(())
}

fn id_at(start: &str, ordinal: u16) -> Result<String> {
    crate::decimal(start, "application birth namespace start")?;
    start
        .parse::<u64>()
        .ok()
        .and_then(|first| first.checked_add(u64::from(ordinal)))
        .map(|value| value.to_string())
        .ok_or("application birth namespace exceeds u64".into())
}

fn member(
    name: String,
    target: String,
    owner: String,
    control: String,
    max: usize,
) -> BornResource {
    BornResource {
        name,
        kind: "object".into(),
        target,
        owner_capability: owner,
        control_capability: control,
        max_result_bytes: max,
    }
}

struct SourceShape {
    outer_field: &'static str,
    birth_field: &'static str,
    birth: Value,
}

pub(super) struct BirthIndex {
    pub nonce: u64,
    pub ordinal: u16,
}

fn source_context(
    profile: &BirthProfile,
    tool: &ToolTask,
    parent_task: &str,
    nonce: u64,
    tool_view: &Value,
    parent_view: &Value,
    shape: SourceShape,
) -> Result<Value> {
    let tool_peer = resource_tools::signed_grain_peer(
        tool_view,
        &tool.task,
        &tool.capability,
        &tool.query_capability,
    )?;
    let parent_peer = resource_tools::signed_grain_peer(
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
        .ok_or("signed tool height absent")?;
    crate::decimal(height, "signed tool height")?;
    if parent_view.get("height").and_then(Value::as_str) != Some(height)
        || parent_view.get("worldRoot") != tool_view.get("worldRoot")
    {
        return Err("tool and parent observations have different signed height or image".into());
    }
    let grain_birth = json!({
        "tariff":{"base":profile.tariff_base,"perBirth":profile.tariff_per_birth},
        (shape.birth_field):shape.birth,"authorityRoot":authority_root,"tool":tool_peer,"parent":parent_peer
    });
    let source = json!({
        "subject":tool.subject,"nonce":nonce.to_string(),(shape.outer_field):grain_birth,
        "grants":[
            {"kind":"object","target":profile.factory_target,
                "capability":profile.factory_observe_capability},
            {"kind":"account","target":profile.payer_account,
                "capability":profile.payer_observe_capability},
            {"kind":"object","target":tool.task,"capability":tool.query_capability},
            {"kind":"object","target":parent_task,
                "capability":tool.parent_observe_capability}
        ]
    });
    if serde_json::to_vec(&source)
        .map_err(|e| e.to_string())?
        .len()
        > resource_tools::MAX_BIRTH_SOURCE_BYTES
    {
        return Err("application birth intent exceeds source bound".into());
    }
    Ok(source)
}

fn birth_body(profile: &BirthProfile, tool: &ToolTask, nonce: u64, height: &str) -> Value {
    json!({
        "genesis":profile.genesis,"template":profile.template,
        "height":height,"creator":tool.subject,"nonce":nonce.to_string(),
        "sourceCapabilities":[profile.payer_capability],"funding":[],
        "feePayer":profile.payer_account
    })
}

/// Construct only the operator-pinned selector/source input. Op30 must
/// rederive the complete descriptor against the verifier-opened authority.
pub(super) fn plan_application_birth(
    family: &ApplicationFamily,
    tool: &ToolTask,
    parent_task: &str,
    nonce: u64,
    ordinal: u16,
    tool_view: &Value,
    parent_view: &Value,
) -> Result<(Value, Vec<BornResource>)> {
    if ordinal >= family.max_births {
        return Err("application family ordinal is exhausted".into());
    }
    let n = &family.namespace;
    let ids = n
        .targets()
        .map(|start| id_at(start, ordinal))
        .into_iter()
        .collect::<Result<Vec<_>>>()?;
    let caps = n
        .capabilities()
        .map(|start| id_at(start, ordinal))
        .into_iter()
        .collect::<Result<Vec<_>>>()?;
    let height = tool_view
        .get("height")
        .and_then(Value::as_str)
        .ok_or("signed tool height absent")?;
    let mut body = birth_body(&family.profile, tool, nonce, height);
    body["application"] = json!({
        "app":ids[0],"packageManifest":ids[1],"snapshotManifest":ids[2],
        "owner":tool.subject,
        "appOwnerCapability":caps[0],"appControlCapability":caps[1],
        "packageOwnerCapability":caps[2],"packageControlCapability":caps[3],
        "snapshotOwnerCapability":caps[4],"snapshotControlCapability":caps[5]
    });
    let born = vec![
        member(
            format!("{}-{ordinal}-app", family.name),
            ids[0].clone(),
            caps[0].clone(),
            caps[1].clone(),
            family.max_result_bytes,
        ),
        member(
            format!("{}-{ordinal}-package", family.name),
            ids[1].clone(),
            caps[2].clone(),
            caps[3].clone(),
            family.max_result_bytes,
        ),
        member(
            format!("{}-{ordinal}-snapshot", family.name),
            ids[2].clone(),
            caps[4].clone(),
            caps[5].clone(),
            family.max_result_bytes,
        ),
    ];
    let source = source_context(
        &family.profile,
        tool,
        parent_task,
        nonce,
        tool_view,
        parent_view,
        SourceShape {
            outer_field: "applicationGrainBirth",
            birth_field: "applicationBirth",
            birth: body,
        },
    )?;
    Ok((source, born))
}

/// `app_target` must come from a verified, confirmed application bundle and a
/// fresh signed current app read by the controller; this helper cannot grant
/// that authority or accept a public raw app ID.
pub(super) fn plan_session_birth(
    family: &SessionFamily,
    tool: &ToolTask,
    parent_task: &str,
    app_target: &str,
    index: BirthIndex,
    tool_view: &Value,
    parent_view: &Value,
) -> Result<(Value, Vec<BornResource>)> {
    let BirthIndex { nonce, ordinal } = index;
    if ordinal >= family.max_births {
        return Err("session family ordinal is exhausted".into());
    }
    crate::decimal(app_target, "verified application target")?;
    let n = &family.namespace;
    let ids = n
        .targets()
        .map(|start| id_at(start, ordinal))
        .into_iter()
        .collect::<Result<Vec<_>>>()?;
    if ids.iter().any(|id| id == app_target) {
        return Err("session target overlaps verified application".into());
    }
    let caps = n
        .capabilities()
        .map(|start| id_at(start, ordinal))
        .into_iter()
        .collect::<Result<Vec<_>>>()?;
    let height = tool_view
        .get("height")
        .and_then(Value::as_str)
        .ok_or("signed tool height absent")?;
    let mut body = birth_body(&family.profile, tool, nonce, height);
    body["session"] = json!({
        "app":app_target,"session":ids[0],"descriptor":ids[1],
        "participant":tool.subject,"kind":family.kind,
        "sessionOwnerCapability":caps[0],"sessionControlCapability":caps[1],
        "descriptorOwnerCapability":caps[2],"descriptorControlCapability":caps[3]
    });
    let born = vec![
        member(
            format!("{}-{ordinal}-session", family.name),
            ids[0].clone(),
            caps[0].clone(),
            caps[1].clone(),
            family.max_result_bytes,
        ),
        member(
            format!("{}-{ordinal}-descriptor", family.name),
            ids[1].clone(),
            caps[2].clone(),
            caps[3].clone(),
            family.max_result_bytes,
        ),
    ];
    let source = source_context(
        &family.profile,
        tool,
        parent_task,
        nonce,
        tool_view,
        parent_view,
        SourceShape {
            outer_field: "applicationSessionGrainBirth",
            birth_field: "applicationSessionBirth",
            birth: body,
        },
    )?;
    Ok((source, born))
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn profile() -> BirthProfile {
        BirthProfile {
            genesis: json!({}),
            template: json!({}),
            factory_target: "10".into(),
            factory_observe_capability: "20".into(),
            payer_account: "11".into(),
            payer_capability: "21".into(),
            payer_observe_capability: "22".into(),
            tariff_base: "5".into(),
            tariff_per_birth: "2".into(),
        }
    }

    fn app() -> ApplicationFamily {
        ApplicationFamily {
            name: "office".into(),
            profile: profile(),
            max_births: 2,
            max_result_bytes: 1024,
            namespace: ApplicationNamespace {
                app: "100".into(),
                package_manifest: "200".into(),
                snapshot_manifest: "300".into(),
                app_owner_capability: "1000".into(),
                app_control_capability: "1100".into(),
                package_owner_capability: "1200".into(),
                package_control_capability: "1300".into(),
                snapshot_owner_capability: "1400".into(),
                snapshot_control_capability: "1500".into(),
            },
        }
    }

    fn session() -> SessionFamily {
        SessionFamily {
            name: "office-web".into(),
            application_family: "office".into(),
            kind: "web".into(),
            profile: profile(),
            max_births: 2,
            max_result_bytes: 1024,
            namespace: SessionNamespace {
                session: "400".into(),
                descriptor: "500".into(),
                session_owner_capability: "1600".into(),
                session_control_capability: "1700".into(),
                descriptor_owner_capability: "1800".into(),
                descriptor_control_capability: "1900".into(),
            },
        }
    }

    fn check(applications: &[ApplicationFamily], sessions: &[SessionFamily]) -> Result<()> {
        validate_families(applications, sessions, &[], &[], &[], &[], (&["1"], &["2"]))
    }

    #[test]
    fn session_family_accepts_only_registered_external_application_family() {
        validate_families(
            &[],
            &[session()],
            &["office"],
            &[],
            &[],
            &[],
            (&["1"], &["2"]),
        )
        .unwrap();
        assert!(validate_families(
            &[],
            &[session()],
            &["other"],
            &[],
            &[],
            &[],
            (&["1"], &["2"])
        )
        .is_err());
    }

    #[test]
    fn all_five_targets_and_ten_grants_are_reserved() {
        check(&[app()], &[session()]).unwrap();
        let mut changed = session();
        changed.namespace.descriptor = "301".into();
        assert!(check(&[app()], &[changed]).is_err());
        let mut changed = session();
        changed.namespace.descriptor_control_capability = "1501".into();
        assert!(check(&[app()], &[changed]).is_err());
        let mut changed = app();
        changed.namespace.package_manifest = "100".into();
        assert!(check(&[changed], &[session()]).is_err());
    }

    #[test]
    fn fixed_peers_and_tariff_overflow_are_rejected() {
        let mut changed = app();
        changed.profile.factory_target = "100".into();
        assert!(check(&[changed], &[]).is_err());
        let mut changed = app();
        changed.profile.tariff_per_birth = u64::MAX.to_string();
        assert!(check(&[changed], &[]).is_err());
        assert_eq!(planned_charge(&profile(), 3).unwrap(), "11");
        assert_eq!(planned_charge(&profile(), 2).unwrap(), "9");
    }

    #[test]
    fn app_and_session_sources_bind_signed_peers_and_complete_members() {
        let tool = ToolTask {
            task: "1".into(),
            subject: "3".into(),
            capability: "4".into(),
            query_capability: "5".into(),
            custody_key: "/unused".into(),
            parent_capability: "6".into(),
            parent_observe_capability: "7".into(),
            reserve: "20".into(),
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
            agent_api_host_sha256: None,
            lifetime_api_host_sha256: None,
            current_birth_host_sha256: None,
        };
        let view = json!({"targetRoot":"41","authorityRoot":"42","height":"9",
            "worldRoot":"8","grain":{"generation":"1","status":"1",
            "remaining":"20","reserved":"11"}});
        let (source, members) =
            plan_application_birth(&app(), &tool, "2", 77, 1, &view, &view).unwrap();
        assert_eq!(members.len(), 3);
        assert_eq!(members[0].target, "101");
        assert_eq!(members[2].control_capability, "1501");
        assert_eq!(
            source["applicationGrainBirth"]["applicationBirth"]["application"]["app"],
            "101"
        );
        assert_eq!(source["applicationGrainBirth"]["authorityRoot"], "42");
        assert_eq!(source["grants"].as_array().unwrap().len(), 4);
        let (session_source, session_members) = plan_session_birth(
            &session(),
            &tool,
            "2",
            "101",
            BirthIndex {
                nonce: 78,
                ordinal: 1,
            },
            &view,
            &view,
        )
        .unwrap();
        assert_eq!(session_members.len(), 2);
        assert_eq!(
            session_source["applicationSessionGrainBirth"]["applicationSessionBirth"]["session"]
                ["app"],
            "101"
        );
        let mut changed = view.clone();
        changed["authorityRoot"] = json!("43");
        assert!(plan_application_birth(&app(), &tool, "2", 77, 1, &view, &changed).is_err());
    }
}
