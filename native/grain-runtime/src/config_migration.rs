//! Explicit, recoverable controller configuration publication. This never
//! authorizes a new grain, key, grant, provider payment, or resource operation.
//! A prepared publication makes the old process read-only until restart.
use crate::quiescence::{ResidentGuard, Status};
use crate::*;
use minidregg_compatible_upgrade_custody as custody;

const LIMIT: usize = 32 * 1024 * 1024;
const FORMAT: &str = "mini-controller-config-migration-v1";

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Request {
    #[serde(rename = "type")]
    kind: String,
    expected_config_sha256: String,
    expected_binding_sha256: String,
    target_config: PathBuf,
    target_config_sha256: String,
    resident_state: Option<PathBuf>,
    compatible_admission: Option<AdmissionPin>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    mini_admission: Option<AdmissionPin>,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct AdmissionPin {
    path: PathBuf,
    sha256: String,
}
#[derive(Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum Role {
    Config,
    Journal,
    Workspace,
}
impl Role {
    fn name(self) -> &'static str {
        match self {
            Self::Config => "config",
            Self::Journal => "journal",
            Self::Workspace => "workspace",
        }
    }
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Change {
    role: Role,
    path: PathBuf,
    before_sha256: String,
    after_sha256: String,
}
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Transaction {
    protocol: String,
    operation_id: u64,
    config_path: PathBuf,
    state_dir: PathBuf,
    request: Request,
    changed_fields: Vec<String>,
    resident_sha256: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    resident_requests_sha256: Option<String>,
    quiescence_sha256: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    owner_rotation_sha256: Option<String>,
    changes: Vec<Change>,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Pointer {
    protocol: String,
    transaction: PathBuf,
    manifest_sha256: String,
    phase: Phase,
    activated_pid: Option<u32>,
}
#[derive(Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
enum Phase {
    Prepared,
    Published,
    Activated,
}

fn digest(bytes: &[u8]) -> Result<String> {
    sha256_bytes(bytes)
}
fn value_digest(value: &Value) -> Result<String> {
    digest(&serde_json::to_vec(value).map_err(|e| e.to_string())?)
}
fn hex(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}
fn private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let meta = fs::symlink_metadata(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
        || meta.nlink() != 1
    {
        return Err(format!(
            "{} is not an owned private regular file",
            path.display()
        ));
    }
    bounded_regular_file(path, limit)
}
fn directory(path: &Path) -> Result<()> {
    match fs::symlink_metadata(path) {
        Ok(m) if m.is_dir() && m.uid() == unsafe { libc::geteuid() } && m.mode() & 0o077 == 0 => {
            Ok(())
        }
        Ok(_) => Err("migration directory custody refused".into()),
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            let mut b = fs::DirBuilder::new();
            b.mode(0o700);
            b.create(path).map_err(|e| e.to_string())?;
            sync_parent(path)
        }
        Err(e) => Err(e.to_string()),
    }
}
fn sync_parent(path: &Path) -> Result<()> {
    File::open(path.parent().ok_or("path parent absent")?)
        .and_then(|f| f.sync_all())
        .map_err(|e| e.to_string())
}
fn pointer_path(state: &Path) -> PathBuf {
    state.join("config-migration.json")
}
fn read_pointer(state: &Path) -> Result<Option<Pointer>> {
    let path = pointer_path(state);
    match fs::symlink_metadata(&path) {
        Ok(_) => {}
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(error.to_string()),
    }
    let p: Pointer = serde_json::from_slice(&private(&path, 65536)?).map_err(|e| e.to_string())?;
    if p.protocol != FORMAT
        || !hex(&p.manifest_sha256)
        || p.transaction.parent() != Some(state.join("config-migrations").as_path())
    {
        return Err("migration pointer identity/layout refused".into());
    }
    Ok(Some(p))
}

/// Only the source-owned current pointer is replaced. A crash-retained staging
/// file is reusable only when its exact bytes match this publication.
pub(crate) fn publish_bytes(path: &Path, bytes: &[u8], tag: &str) -> Result<()> {
    let name = path
        .file_name()
        .and_then(|s| s.to_str())
        .ok_or("publication filename absent")?;
    let temp = path.with_file_name(format!(".{name}.migration-{tag}.tmp"));
    if temp.try_exists().map_err(|e| e.to_string())? {
        if private(&temp, LIMIT)? != bytes {
            return Err("migration staging bytes differ; retained for inspection".into());
        }
    } else {
        write_new(&temp, bytes)?;
    }
    fs::rename(&temp, path).map_err(|e| format!("migration publication: {e}"))?;
    sync_parent(path)
}
fn publish_pointer(state: &Path, p: &Pointer) -> Result<()> {
    let bytes = serde_json::to_vec_pretty(p).map_err(|e| e.to_string())?;
    publish_bytes(&pointer_path(state), &bytes, &digest(&bytes)?[..16])
}

fn differences(a: &Value, b: &Value, prefix: &str, out: &mut Vec<String>) {
    if a == b {
        return;
    }
    if let (Some(a), Some(b)) = (a.as_object(), b.as_object()) {
        let keys: std::collections::BTreeSet<_> = a.keys().chain(b.keys()).collect();
        for key in keys {
            differences(
                a.get(key).unwrap_or(&Value::Null),
                b.get(key).unwrap_or(&Value::Null),
                &format!("{prefix}/{key}"),
                out,
            )
        }
    } else {
        out.push(prefix.to_owned())
    }
}
fn source_profile_pin(
    raw: &Value,
    config_path: &Path,
    old_bytes: &[u8],
    binding: &Value,
    admission: &custody::Admission,
) -> Result<()> {
    // Analogous to root-admitted SPK profiles. A compatible kernel transition
    // alone is not permission to select an arbitrary Hermes controller profile.
    let pins = raw
        .get("hermesProfiles")
        .and_then(Value::as_array)
        .ok_or("root admission has no captured Hermes profile")?;
    let wanted_config = digest(old_bytes)?;
    let wanted_binding = value_digest(binding)?;
    let matches = pins
        .iter()
        .filter(|p| {
            p.get("path").and_then(Value::as_str) == config_path.to_str()
                && p.get("sha256").and_then(Value::as_str) == Some(wanted_config.as_str())
                && p.get("bindingSha256").and_then(Value::as_str) == Some(wanted_binding.as_str())
                && p.get("hostConfigSha256").and_then(Value::as_str)
                    == Some(admission.source.config_sha256.as_str())
        })
        .count();
    if matches != 1 {
        return Err("root admission does not uniquely bind this prior Hermes config, journal binding and Host config".into());
    }
    Ok(())
}

fn admitted_client(
    old: &Config,
    new: &Config,
    source: &Value,
    target: &Value,
    current: bool,
) -> Result<()> {
    let (source_mini, _) = custody::image(source, "mini").map_err(|e| e.to_string())?;
    let (target_mini, target_hash) = custody::image(target, "mini").map_err(|e| e.to_string())?;
    if old.mini != source_mini || new.mini != target_mini {
        return Err(
            "Mini client transition differs from exact root-admitted source and target images"
                .into(),
        );
    }
    if current {
        custody::root_pin(&target_mini, &target_hash).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// A root-attested client image update, not a compatible kernel upgrade.
/// The already bound Host stack may be operator-owned; exact content pins keep
/// it unchanged without claiming the stronger full-kernel custody contract.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct MiniAdmission {
    protocol: String,
    controller_config: PathBuf,
    controller_config_sha256: String,
    binding_sha256: String,
    source_mini: AdmissionPin,
    target_mini: AdmissionPin,
    host: AdmissionPin,
    host_config: AdmissionPin,
    host_socket: Option<PathBuf>,
}
fn mini_coordinates(
    old: &Config,
    new: &Config,
    old_bytes: &[u8],
    binding: &Value,
    config_path: &Path,
    admission: &MiniAdmission,
) -> Result<()> {
    let hashes = [
        &admission.controller_config_sha256,
        &admission.binding_sha256,
        &admission.source_mini.sha256,
        &admission.target_mini.sha256,
        &admission.host.sha256,
        &admission.host_config.sha256,
    ];
    let paths = [
        &admission.controller_config,
        &admission.source_mini.path,
        &admission.target_mini.path,
        &admission.host.path,
        &admission.host_config.path,
    ];
    if admission.protocol != "mini-controller-client-upgrade-v1"
        || !hashes.iter().all(|h| hex(h))
        || !paths.iter().all(|p| p.is_absolute())
        || admission.controller_config != config_path
        || admission.controller_config_sha256 != digest(old_bytes)?
        || admission.binding_sha256 != value_digest(binding)?
        || old.mini != admission.source_mini.path
        || new.mini != admission.target_mini.path
        || old.mini == new.mini
        || old.host != admission.host.path
        || new.host != old.host
        || old.host_config != admission.host_config.path
        || new.host_config != old.host_config
        || old.host_socket != admission.host_socket
        || new.host_socket != old.host_socket
    {
        return Err("Mini-only admission differs from exact bound controller/client/unchanged Host coordinates".into());
    }
    Ok(())
}
fn admitted_mini(
    old: &Config,
    new: &Config,
    old_bytes: &[u8],
    binding: &Value,
    config_path: &Path,
    pin: &AdmissionPin,
    current: bool,
) -> Result<()> {
    let raw = custody::root_bytes(&pin.path, 65536).map_err(|e| e.to_string())?;
    if !hex(&pin.sha256) || digest(&raw)? != pin.sha256 {
        return Err("Mini-only admission hash changed".into());
    }
    let admission: MiniAdmission = serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
    mini_coordinates(old, new, old_bytes, binding, config_path, &admission)?;
    if current {
        custody::root_pin(&admission.target_mini.path, &admission.target_mini.sha256)
            .map_err(|e| e.to_string())?;
        // Existing operator-owned images/config are not silently promoted to
        // root custody. Their exact admitted bytes must still be present.
        for image in [
            &admission.source_mini,
            &admission.host,
            &admission.host_config,
        ] {
            if sha256_file(&image.path)? != image.sha256 {
                return Err(
                    "Mini-only admission's existing source image/Host stack changed".into(),
                );
            }
        }
    }
    Ok(())
}

fn admitted_transport(
    old: &Config,
    new: &Config,
    old_bytes: &[u8],
    binding: &Value,
    config_path: &Path,
    pin: &AdmissionPin,
    current: bool,
) -> Result<()> {
    let raw = custody::root_bytes(&pin.path, 4 * 1024 * 1024).map_err(|e| e.to_string())?;
    if !hex(&pin.sha256) || custody::sha(&raw) != pin.sha256 {
        return Err("compatible admission hash changed".into());
    }
    let admission = if current {
        custody::load(&pin.path)
    } else {
        custody::load_evidence(&pin.path)
    }
    .map_err(|e| e.to_string())?;
    let raw: Value = serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
    source_profile_pin(&raw, config_path, old_bytes, binding, &admission)?;
    admitted_client(
        old,
        new,
        &admission.source.manifest,
        &admission.target.manifest,
        current,
    )?;
    let (source_host, source_hash) =
        custody::image(&admission.source.manifest, "host").map_err(|e| e.to_string())?;
    let (target_host, target_hash) =
        custody::image(&admission.target.manifest, "host").map_err(|e| e.to_string())?;
    if old.host != source_host
        || new.host != target_host
        || new.host_config != admission.target.config_path
    {
        return Err(
            "controller Host/config transition differs from admitted source and target".into(),
        );
    }
    // Stable config paths may already contain target bytes; the old digest is
    // captured in hermesProfiles, never inferred from the changed live file.
    if old.host_config != admission.source.config_path
        && old.host_config != admission.target.config_path
    {
        return Err("prior Host config path is outside admitted Store config lineage".into());
    }
    if old.host_socket != new.host_socket {
        if old.host_socket != admission.public_socket
            || new.host_socket != admission.management_socket
            || new.host_socket.is_none()
        {
            return Err(
                "Host socket change lacks exact admitted public-to-management topology".into(),
            );
        }
    }
    if source_hash != target_hash {
        if let Some(tool) = &old.tool_task {
            if tool.agent_api_host_sha256.is_some()
                || tool.lifetime_api_host_sha256.is_some()
                || tool.current_birth_host_sha256.is_some()
            {
                return Err("qualified feature Host image changed; separate source feature qualification is required".into());
            }
        }
    }
    Ok(())
}

const OWNER_KEY_FIELD: &str = "/providerTask/onBehalfOf/publicKey";

/// Historical observation, deliberately not a CurrentOwnerProof. Recovery must
/// query native authority again rather than turning this archive into a proof.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct OwnerRotation {
    protocol: String,
    subject: String,
    old_public_key: String,
    new_public_key: String,
    epoch: String,
    owner: Value,
    grant: Value,
}
fn owner_pair<'a>(old: &'a Config, new: &'a Config) -> Result<(&'a OnBehalfOf, &'a OnBehalfOf)> {
    let before = old
        .provider_task
        .as_ref()
        .and_then(|t| t.on_behalf_of.as_ref())
        .ok_or("owner rotation requires an existing member owner")?;
    let after = new
        .provider_task
        .as_ref()
        .and_then(|t| t.on_behalf_of.as_ref())
        .ok_or("owner rotation cannot remove the member owner")?;
    if before.subject != after.subject || before.public_key == after.public_key {
        return Err(
            "owner rotation must preserve the subject and change only its current public key"
                .into(),
        );
    }
    credentials::Owner::new(&before.subject, &before.public_key)?;
    credentials::Owner::new(&after.subject, &after.public_key)?;
    Ok((before, after))
}
fn owner_rotation_shape(old: &Config, new: &Config, fields: &[String]) -> Result<bool> {
    if !fields.iter().any(|p| p == OWNER_KEY_FIELD) {
        return Ok(false);
    }
    if fields.len() != 1 {
        return Err("owner rotation is a separate typed transition; other configuration changes must be published separately".into());
    }
    owner_pair(old, new)?;
    Ok(true)
}
impl OwnerRotation {
    fn validate(&self, old: &Config, new: &Config) -> Result<()> {
        let (before, after) = owner_pair(old, new)?;
        let task = new.provider_task.as_ref().ok_or("provider task absent")?;
        let grant = credentials::Grant::from_json(&self.grant["grant"])?;
        let height = self.grant["height"]
            .as_str()
            .ok_or("owner grant height absent")?
            .parse::<u64>()
            .map_err(|_| "owner grant height invalid")?;
        if self.protocol != "mini-controller-owner-rotation-observation-v1"
            || self.subject != before.subject
            || self.old_public_key != before.public_key
            || self.new_public_key != after.public_key
            || self.epoch.is_empty()
            || !self.epoch.bytes().all(|b| b.is_ascii_digit())
            || (self.epoch != "0" && self.epoch.starts_with('0'))
            || self.owner["type"] != "native-owner-observation-v1"
            || self.owner["subject"] != self.subject
            || self.owner["publicKey"] != self.new_public_key
            || self.owner["keyEpoch"] != self.epoch
            || self.owner["response"]["type"] != "subject-key-status-v1"
            || self.owner["response"]["subject"] != self.subject
            || self.owner["response"]["publicKey"] != self.new_public_key
            || self.owner["response"]["keyEpoch"] != self.epoch
            || self.owner["response"]["isCurrent"] != true
            || self.owner["response"]["currentRevoked"] != false
            || self.grant["type"] != "member-provider-grant-observation-v1"
            || self.grant["subject"] != self.subject
            || self.grant["publicKey"] != self.new_public_key
            || self.grant["model"] != task.model
            || self.grant["height"] != height.to_string()
            || task
                .provider
                .as_ref()
                .is_some_and(|p| self.grant["provider"] != *p)
            || self.grant["source"]["task"] != task.task
            || self.grant["source"]["height"] != self.grant["height"]
            || grant.runner != task.subject
            || grant.model.as_deref() != Some(task.model.as_str())
            || grant.owner_epoch.as_deref() != Some(self.epoch.as_str())
            || grant.per_call < u64::from(task.max_output_tokens)
            || grant.not_after < height
        {
            return Err("owner rotation archive does not bind the exact same-subject key and existing model/epoch grant".into());
        }
        Ok(())
    }
}
fn observe_owner_rotation(
    old: &Config,
    new: &Config,
    fields: &[String],
) -> Result<Option<OwnerRotation>> {
    if !owner_rotation_shape(old, new, fields)? {
        return Ok(None);
    }
    let (before, after) = owner_pair(old, new)?;
    let proof = crate::provider_owner::observe(new, &after.subject, &after.public_key)?;
    let grant = crate::provider_owner::grant_evidence(new, &proof)?;
    let record = OwnerRotation {
        protocol: "mini-controller-owner-rotation-observation-v1".into(),
        subject: before.subject.clone(),
        old_public_key: before.public_key.clone(),
        new_public_key: after.public_key.clone(),
        epoch: proof.epoch().into(),
        owner: proof.evidence(),
        grant,
    };
    record.validate(old, new)?;
    Ok(Some(record))
}
fn retained_owner_rotation(dir: &Path, t: &Transaction, old: &Config, new: &Config) -> Result<()> {
    let needed = owner_rotation_shape(old, new, &t.changed_fields)?;
    match (&t.owner_rotation_sha256, needed) {
        (None, false) => Ok(()),
        (Some(expected), true) => {
            let bytes = private(&dir.join("owner-rotation.json"), LIMIT)?;
            if !hex(expected) || digest(&bytes)? != *expected {
                return Err("owner rotation evidence hash changed".into());
            }
            let observation: OwnerRotation =
                serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
            observation.validate(old, new)
        }
        _ => Err(
            "owner rotation requires its own exact archived native owner and grant observations"
                .into(),
        ),
    }
}

fn permitted_diff(
    old: &Config,
    new: &Config,
    old_bytes: &[u8],
    binding: &Value,
    path: &Path,
    admission: Option<&AdmissionPin>,
    mini_admission: Option<&AdmissionPin>,
    current: bool,
) -> Result<Vec<String>> {
    let a = serde_json::to_value(old).map_err(|e| e.to_string())?;
    let b = serde_json::to_value(new).map_err(|e| e.to_string())?;
    let mut changed = Vec::new();
    differences(&a, &b, "", &mut changed);
    if changed.is_empty() {
        return Err("configuration migration has no changed fields".into());
    }
    let transport = [
        "/mini",
        "/toolTask/room/mini",
        "/host",
        "/hostConfig",
        "/hostSocket",
        "/toolTask/room/host",
        "/toolTask/room/hostConfig",
        "/toolTask/room/socket",
    ];
    owner_rotation_shape(old, new, &changed)?;
    let needs_admission = changed.iter().any(|p| transport.contains(&p.as_str()));
    for p in &changed {
        if ![
            "/providerTask/contextWindowTokens",
            "/providerTask/maxIterations",
            "/providerTask/maxRequestBytes",
            OWNER_KEY_FIELD,
        ]
        .contains(&p.as_str())
            && !transport.contains(&p.as_str())
        {
            return Err(format!("unsupported configuration diff {p}; requires its own typed compatibility or source-authorization evidence"));
        }
    }
    if changed.iter().any(|p| {
        p == "/providerTask/contextWindowTokens"
            || p == "/providerTask/maxIterations"
            || p == "/providerTask/maxRequestBytes"
    }) {
        let task = new
            .provider_task
            .as_ref()
            .ok_or("provider task identity cannot be added or removed")?;
        if changed
            .iter()
            .any(|p| p == "/providerTask/contextWindowTokens")
            && task.context_window_tokens.is_none()
        {
            return Err(
                "context metadata migration requires an explicit contextWindowTokens value".into(),
            );
        }
        if task.context_window_tokens.is_some_and(|window| {
            window < task.max_input_tokens.saturating_add(task.max_output_tokens)
                || window > 2_097_152
        }) {
            return Err("context metadata does not fit unchanged request token bounds".into());
        }
        if changed.iter().any(|p| p == "/providerTask/maxIterations")
            && task.max_iterations.is_none()
        {
            return Err(
                "prompt throttle migration requires an explicit maxIterations value".into(),
            );
        }
        provider_max_iterations(task.max_iterations)?;
        if !(1..=1_048_576).contains(&task.max_request_bytes) {
            return Err("request byte ceiling is outside source bounds".into());
        }
    }
    if admission.is_some() && mini_admission.is_some() {
        return Err("choose exactly one Mini-only or full compatible admission".into());
    }
    if needs_admission {
        if let Some(pin) = mini_admission {
            if changed.iter().any(|p| {
                transport.contains(&p.as_str()) && p != "/mini" && p != "/toolTask/room/mini"
            }) {
                return Err(
                    "Mini-only admission cannot authorize Host/config/socket transport changes"
                        .into(),
                );
            }
            admitted_mini(old, new, old_bytes, binding, path, pin, current)?;
        } else {
            admitted_transport(
                old,
                new,
                old_bytes,
                binding,
                path,
                admission
                    .ok_or("Host transport change requires captured root compatible admission")?,
                current,
            )?;
        }
        if let Some(room) = new.tool_task.as_ref().and_then(|t| t.room.as_ref()) {
            if room.host != new.host
                || room.host_config != new.host_config
                || Some(&room.socket) != new.host_socket.as_ref()
                || room.mini != new.mini
            {
                return Err(
                    "room transport must remain exactly pinned to controller transport".into(),
                );
            }
        }
    } else if admission.is_some() || mini_admission.is_some() {
        return Err("operational-only migration must not borrow unrelated Host admission".into());
    }
    Ok(changed)
}

fn workspace_after(old: &Config, new: &Config, before: &[u8]) -> Result<Vec<u8>> {
    let tool = old
        .tool_task
        .as_ref()
        .ok_or("workspace has no delegated tool")?;
    let mut value: Value = serde_json::from_slice(before).map_err(|e| e.to_string())?;
    if value["type"] != "minidregg-participant-workspace-v1"
        || value["subject"] != tool.subject
        || value["key"].as_str().map(Path::new) != Some(tool.custody_key.as_path())
        || value["host"].as_str().map(Path::new) != Some(old.host.as_path())
        || value["config"].as_str().map(Path::new) != Some(old.host_config.as_path())
        || value["socket"].as_str().map(Path::new) != old.host_socket.as_deref()
    {
        return Err("prior delegated workspace custody differs from controller".into());
    }
    value["host"] = json!(new.host);
    value["config"] = json!(new.host_config);
    value["socket"] = json!(new.host_socket);
    serde_json::to_vec_pretty(&value).map_err(|e| e.to_string())
}

fn blob(dir: &Path, role: Role, after: bool) -> PathBuf {
    dir.join(format!(
        "{}-{}.json",
        role.name(),
        if after { "after" } else { "before" }
    ))
}
fn retained_blob(dir: &Path, change: &Change, after: bool) -> Result<Vec<u8>> {
    let bytes = private(&blob(dir, change.role, after), LIMIT)?;
    if digest(&bytes)?
        != if after {
            change.after_sha256.clone()
        } else {
            change.before_sha256.clone()
        }
    {
        return Err("retained migration blob hash changed".into());
    }
    Ok(bytes)
}
fn retain_change(
    dir: &Path,
    role: Role,
    path: PathBuf,
    before: Vec<u8>,
    after: Vec<u8>,
) -> Result<Change> {
    write_new(&blob(dir, role, false), &before)?;
    write_new(&blob(dir, role, true), &after)?;
    Ok(Change {
        role,
        path,
        before_sha256: digest(&before)?,
        after_sha256: digest(&after)?,
    })
}
fn apply_changes(dir: &Path, transaction: &Transaction) -> Result<()> {
    // Check the entire receiving vector before replacing its first member.
    for change in &transaction.changes {
        let hash = digest(&private(&change.path, LIMIT)?)?;
        if hash != change.before_sha256 && hash != change.after_sha256 {
            return Err(format!(
                "{} differs from both exact migration states",
                change.path.display()
            ));
        }
        retained_blob(dir, change, true)?;
    }
    for change in &transaction.changes {
        let current = digest(&private(&change.path, LIMIT)?)?;
        if current != change.before_sha256 && current != change.after_sha256 {
            return Err(
                "receiving member changed during publication; retained for recovery".into(),
            );
        }
        if current != change.after_sha256 {
            let bytes = retained_blob(dir, change, true)?;
            publish_bytes(
                &change.path,
                &bytes,
                &format!("{}-{}", transaction.operation_id, change.role.name()),
            )?;
        }
    }
    Ok(())
}

fn decode_config(bytes: &[u8]) -> Result<Config> {
    serde_json::from_slice(bytes).map_err(|e| format!("controller config: {e}"))
}
fn read_request(path: &Path) -> Result<Request> {
    decode_request(&private(path, 65536)?)
}
fn decode_request(bytes: &[u8]) -> Result<Request> {
    let r: Request =
        serde_json::from_slice(bytes).map_err(|e| format!("migration request: {e}"))?;
    if r.kind != FORMAT
        || ![
            &r.expected_config_sha256,
            &r.expected_binding_sha256,
            &r.target_config_sha256,
        ]
        .iter()
        .all(|v| hex(v))
        || !r.target_config.is_absolute()
    {
        return Err("migration request type/hash/path refused".into());
    }
    Ok(r)
}
fn target(r: &Request) -> Result<(Vec<u8>, Config)> {
    let bytes = private(&r.target_config, 262144)?;
    if digest(&bytes)? != r.target_config_sha256 {
        return Err("target configuration hash differs".into());
    }
    let c = decode_config(&bytes)?;
    Ok((bytes, c))
}
fn checked_request(
    old: &Config,
    path: &Path,
    binding: &Value,
    r: &Request,
) -> Result<(Vec<u8>, Vec<u8>, Config, Vec<String>)> {
    let before = private(path, 262144)?;
    if digest(&before)? != r.expected_config_sha256
        || value_digest(binding)? != r.expected_binding_sha256
        || serde_json::to_value(decode_config(&before)?).map_err(|e| e.to_string())?
            != serde_json::to_value(old).map_err(|e| e.to_string())?
        || *binding != json!({"config":old,"configPath":path})
    {
        return Err("exact source configuration/journal binding changed".into());
    }
    let (after, new) = target(r)?;
    let fields = permitted_diff(
        old,
        &new,
        &before,
        binding,
        path,
        r.compatible_admission.as_ref(),
        r.mini_admission.as_ref(),
        true,
    )?;
    let prospective = if old.host != new.host
        || old.host_config != new.host_config
        || old.host_socket != new.host_socket
    {
        old.tool_task
            .as_ref()
            .and_then(|tool| tool.resource_workspace.as_ref())
            .map(|root| workspace_after(old, &new, &private(&root.join("workspace.json"), LIMIT)?))
            .transpose()?
    } else {
        None
    };
    validate_with_workspace(&new, prospective.as_deref())?;
    Ok((before, after, new, fields))
}

/// Called under controller.lock before constructing the stopped, query-only
/// Runtime. It admits target transport, never an ordinary serve bypass.
pub(crate) fn check_stopped_open(
    old: &Config,
    path: &Path,
    journal: &Journal,
    request: &Path,
) -> Result<()> {
    checked_request(old, path, &journal.binding, &read_request(request)?)?;
    Ok(())
}

fn validate_transaction(
    dir: &Path,
    p: &Pointer,
    current: bool,
) -> Result<(Transaction, Config, Config)> {
    let bytes = private(&dir.join("transaction.json"), LIMIT)?;
    if digest(&bytes)? != p.manifest_sha256 {
        return Err("migration manifest changed".into());
    }
    let t: Transaction = serde_json::from_slice(&bytes).map_err(|e| e.to_string())?;
    if t.protocol != FORMAT
        || t.request.kind != FORMAT
        || dir.parent() != Some(t.state_dir.join("config-migrations").as_path())
        || t.changes.len() < 2
        || t.changes.len() > 3
    {
        return Err("migration transaction format/layout refused".into());
    }
    if let Some(hash)=&t.resident_requests_sha256 {
        if t.request.resident_state.is_none() || !hex(hash)
            || digest(&private(&dir.join("resident-requests-before.json"),LIMIT)?)?!=*hash {
            return Err("resident request checkpoint identity changed".into());
        }
    }
    let get = |role| -> Result<&Change> {
        let rows: Vec<_> = t.changes.iter().filter(|c| c.role == role).collect();
        if rows.len() != 1 {
            return Err("migration role missing or repeated".into());
        }
        Ok(rows[0])
    };
    let cc = get(Role::Config)?;
    let jc = get(Role::Journal)?;
    let before = retained_blob(dir, cc, false)?;
    let after = retained_blob(dir, cc, true)?;
    let old = decode_config(&before)?;
    let new = decode_config(&after)?;
    let before_j: Value =
        serde_json::from_slice(&retained_blob(dir, jc, false)?).map_err(|e| e.to_string())?;
    let after_j: Value =
        serde_json::from_slice(&retained_blob(dir, jc, true)?).map_err(|e| e.to_string())?;
    let typed_before: Journal =
        serde_json::from_value(before_j.clone()).map_err(|e| e.to_string())?;
    let _: Journal = serde_json::from_value(after_j.clone()).map_err(|e| e.to_string())?;
    if cc.path != t.config_path
        || jc.path != t.state_dir.join("journal.json")
        || old.state_dir != t.state_dir
        || new.state_dir != t.state_dir
        || cc.before_sha256 != t.request.expected_config_sha256
        || cc.after_sha256 != t.request.target_config_sha256
        || before_j["binding"] != json!({"config":old,"configPath":t.config_path})
        || value_digest(&before_j["binding"])? != t.request.expected_binding_sha256
    {
        return Err("migration exact source coordinates/binding refused".into());
    }
    let mut expected_j = before_j.clone();
    expected_j["binding"] = json!({"config":new,"configPath":t.config_path});
    if expected_j != after_j {
        return Err("migration modifies journal beyond exact configuration binding".into());
    }
    let fields = permitted_diff(
        &old,
        &new,
        &before,
        &before_j["binding"],
        &t.config_path,
        t.request.compatible_admission.as_ref(),
        t.request.mini_admission.as_ref(),
        current,
    )?;
    if fields != t.changed_fields {
        return Err("migration field decision changed".into());
    }
    retained_owner_rotation(dir, &t, &old, &new)?;
    let transport = old.host != new.host
        || old.host_config != new.host_config
        || old.host_socket != new.host_socket;
    let workspace = old
        .tool_task
        .as_ref()
        .and_then(|tool| tool.resource_workspace.as_ref())
        .filter(|_| transport);
    if let Some(root) = workspace {
        let c = get(Role::Workspace)?;
        if c.path != root.join("workspace.json")
            || retained_blob(dir, c, true)?
                != workspace_after(&old, &new, &retained_blob(dir, c, false)?)?
        {
            return Err("migration workspace is not exact derived transport successor".into());
        }
    } else if t.changes.iter().any(|c| c.role == Role::Workspace) {
        return Err("unrelated workspace mutation refused".into());
    }
    if current {
        let prospective = t
            .changes
            .iter()
            .find(|c| c.role == Role::Workspace)
            .map(|change| retained_blob(dir, change, true))
            .transpose()?;
        validate_with_workspace(&new, prospective.as_deref())?;
    }
    let qbytes = private(&dir.join("quiescence.json"), LIMIT)?;
    if digest(&qbytes)? != t.quiescence_sha256 {
        return Err("migration boundary evidence changed".into());
    }
    let q: Value = serde_json::from_slice(&qbytes).map_err(|e| e.to_string())?;
    if q["closedCheckpoint"] != true
        || q["bindingSha256"] != t.request.expected_binding_sha256
        || q["journalSha256"]
            != digest(&serde_json::to_vec(&typed_before).map_err(|e| e.to_string())?)?
        || q["retained"] != json!([])
        || q["active"] != json!([])
        || q["sessionIntegrityErrors"] != json!([])
    {
        return Err("migration lacks exact closed source checkpoint".into());
    }
    Ok((t, old, new))
}

/// A publication is an explicit restart boundary. This is also checked by
/// Runtime::save as a backstop; event dispatch must reject before any effect.
pub(crate) fn ensure_process_current(state: &Path) -> Result<()> {
    if let Some(p) = read_pointer(state)? {
        if p.phase != Phase::Activated || p.activated_pid != Some(std::process::id()) {
            return Err(
                "configuration migration requires controller restart before any further work"
                    .into(),
            );
        }
    }
    Ok(())
}
/// Resident already holds its own flock here. It must re-read Config after
/// that lock before calling this and before any Mini operation.
pub(crate) fn ensure_resident_current(config: &Config) -> Result<()> {
    if let Some(p) = read_pointer(&config.state_dir)? {
        if p.phase != Phase::Activated {
            return Err("controller configuration migration is not activated".into());
        }
        let (_, _, new) = validate_transaction(&p.transaction, &p, false)?;
        if serde_json::to_value(config).map_err(|e| e.to_string())?
            != serde_json::to_value(new).map_err(|e| e.to_string())?
        {
            return Err("resident loaded obsolete controller configuration".into());
        }
    }
    Ok(())
}

pub(crate) struct Startup {
    pointer: Pointer,
    resident: Option<ResidentGuard>,
}
/// Must run under controller.lock, before ordinary cross-file validate().
/// Recovery accepts only an exact old/new receiving vector, never arbitrary
/// journal edits. The original resident lock spans recovery and activation.
pub(crate) fn recover_startup(config: &Config, path: &Path) -> Result<Option<Startup>> {
    let Some(mut p) = read_pointer(&config.state_dir)? else {
        return Ok(None);
    };
    let (t, old, new) = validate_transaction(&p.transaction, &p, p.phase != Phase::Activated)?;
    if t.config_path != path || t.state_dir != config.state_dir {
        return Err("startup migration coordinates changed".into());
    }
    if p.phase == Phase::Activated {
        if digest(&private(path, 262144)?)? != t.request.target_config_sha256 {
            return Err("activated configuration changed outside typed migration".into());
        }
        return Ok(Some(Startup {
            pointer: p,
            resident: None,
        }));
    }
    prove_prior_run_stopped(&old.task)?;
    let guard = ResidentGuard::acquire(&old, t.request.resident_state.as_deref())?;
    let actual = if t.request.resident_state.is_some() {
        Some(digest(guard.bytes()?)?)
    } else {
        None
    };
    if actual != t.resident_sha256
        || guard.request_bytes().map(digest).transpose()?!=t.resident_requests_sha256 {
        return Err("resident changed after migration checkpoint".into());
    }
    guard.assert_unchanged()?;
    recover_receiving_with(
        &p.transaction,
        &t,
        &old,
        &new,
        observe_owner_rotation,
        || {
            prove_prior_run_stopped(&old.task)?;
            guard.assert_unchanged()
        },
    )?;
    guard.assert_unchanged()?;
    p.phase = Phase::Published;
    p.activated_pid = None;
    publish_pointer(&new.state_dir, &p)?;
    Ok(Some(Startup {
        pointer: p,
        resident: Some(guard),
    }))
}

/// Ordering boundary shared by real recovery and fault-injection receiving
/// checks. The production caller always supplies the fresh native observer;
/// archived observations are validated separately and never supplied here.
fn recover_receiving_with(
    dir: &Path,
    t: &Transaction,
    old: &Config,
    new: &Config,
    refresh: impl FnOnce(&Config, &Config, &[String]) -> Result<Option<OwnerRotation>>,
    stopped: impl FnOnce() -> Result<()>,
) -> Result<()> {
    let observation = refresh(old, new, &t.changed_fields)?;
    if owner_rotation_shape(old, new, &t.changed_fields)? != observation.is_some() {
        return Err("fresh owner rotation observation missing or unrelated".into());
    }
    if let Some(observation) = observation {
        observation.validate(old, new)?;
        let nonce = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_err(|_| "owner recovery clock unavailable")?
            .as_nanos();
        write_new(
            &dir.join(format!("owner-reobserved-{nonce}.json")),
            &serde_json::to_vec_pretty(&observation).map_err(|e| e.to_string())?,
        )?;
        File::open(dir)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
    }
    // All read-only clients exited. Reconfirm physical exclusion before writes.
    stopped()?;
    apply_changes(dir, t)
}

pub(crate) fn activate_startup(state: &Path, startup: Option<Startup>) -> Result<()> {
    if let Some(mut start) = startup {
        if let Some(guard) = &start.resident {
            guard.assert_unchanged()?
        }
        start.pointer.phase = Phase::Activated;
        start.pointer.activated_pid = Some(std::process::id());
        publish_pointer(state, &start.pointer)?;
    }
    Ok(())
}

impl Runtime {
    pub(crate) fn migrate_config(&mut self, request_path: &Path, stopped: bool) -> Result<Value> {
        ensure_process_current(&self.config.state_dir)?;
        let r = read_request(request_path)?;
        if let Some(receipt) =
            completed_receipt(&self.config, &self.config_path, &self.journal, &r)?
        {
            return Ok(receipt);
        }
        let (before, after, new, fields) =
            checked_request(&self.config, &self.config_path, &self.journal.binding, &r)?;
        let old = self.config.clone();
        // Read-only native owner/grant queries complete before final physical
        // and signed quiescence inspection. No key or grant is created here.
        let owner_rotation = observe_owner_rotation(&old, &new, &fields)?;
        // Stopped mode has no server or worker entrypoint. Only the exact
        // admitted target transport is used for fresh signed observations;
        // query counters remain durably bound to the old configuration.
        if stopped {
            self.config = new.clone();
        }
        let inspected = (|| -> Result<(ResidentGuard, Status, u64)> {
            let guard = ResidentGuard::acquire(&self.config, r.resident_state.as_deref())?;
            let id = self.next_id()?;
            let status = self.inspect_quiescence_locked(&guard)?;
            if !status.closed_checkpoint {
                return Err(format!(
                    "migration requires closed checkpoint: {}",
                    serde_json::to_string(&status).map_err(|e| e.to_string())?
                ));
            }
            guard.assert_unchanged()?;
            Ok((guard, status, id))
        })();
        self.config = old.clone();
        let (guard, status, id) = inspected?;
        if digest(&private(&self.config_path, 262144)?)? != r.expected_config_sha256 {
            return Err("configuration changed during inspection".into());
        }
        let journal_path = old.state_dir.join("journal.json");
        let journal_before = private(&journal_path, LIMIT)?;
        let before_j: Value = serde_json::from_slice(&journal_before).map_err(|e| e.to_string())?;
        if before_j != serde_json::to_value(&self.journal).map_err(|e| e.to_string())? {
            return Err("journal changed outside controller during inspection".into());
        }
        let mut journal_after = self.journal.clone();
        journal_after.binding = json!({"config":new,"configPath":self.config_path});
        let root = old.state_dir.join("config-migrations");
        directory(&root)?;
        let dir = root.join(format!("migration-{id:016}"));
        directory(&dir)?;
        if let Some(previous) = read_pointer(&old.state_dir)? {
            write_new(
                &dir.join("previous-selection.json"),
                &serde_json::to_vec_pretty(&previous).map_err(|e| e.to_string())?,
            )?;
        }
        let mut changes = vec![
            retain_change(&dir, Role::Config, self.config_path.clone(), before, after)?,
            retain_change(
                &dir,
                Role::Journal,
                journal_path,
                journal_before,
                serde_json::to_vec_pretty(&journal_after).map_err(|e| e.to_string())?,
            )?,
        ];
        if old.host != new.host
            || old.host_config != new.host_config
            || old.host_socket != new.host_socket
        {
            if let Some(root) = old
                .tool_task
                .as_ref()
                .and_then(|t| t.resource_workspace.as_ref())
            {
                let path = root.join("workspace.json");
                let before = private(&path, LIMIT)?;
                let after = workspace_after(&old, &new, &before)?;
                changes.push(retain_change(&dir, Role::Workspace, path, before, after)?);
            }
        }
        let qbytes = serde_json::to_vec_pretty(&status).map_err(|e| e.to_string())?;
        write_new(&dir.join("quiescence.json"), &qbytes)?;
        let resident_sha256 = if r.resident_state.is_some() {
            let bytes = guard.bytes()?;
            write_new(&dir.join("resident-before.json"), bytes)?;
            Some(digest(bytes)?)
        } else {
            None
        };
        let resident_requests_sha256 = guard.request_bytes().map(|bytes|->Result<String> {
            write_new(&dir.join("resident-requests-before.json"),bytes)?;
            digest(bytes)
        }).transpose()?;
        let owner_rotation_sha256 = owner_rotation
            .map(|observation| -> Result<String> {
                let bytes = serde_json::to_vec_pretty(&observation).map_err(|e| e.to_string())?;
                write_new(&dir.join("owner-rotation.json"), &bytes)?;
                digest(&bytes)
            })
            .transpose()?;
        let t = Transaction {
            protocol: FORMAT.into(),
            operation_id: id,
            config_path: self.config_path.clone(),
            state_dir: old.state_dir.clone(),
            request: r,
            changed_fields: fields,
            resident_sha256,
            resident_requests_sha256,
            quiescence_sha256: digest(&qbytes)?,
            owner_rotation_sha256,
            changes,
        };
        let bytes = serde_json::to_vec_pretty(&t).map_err(|e| e.to_string())?;
        write_new(&dir.join("transaction.json"), &bytes)?;
        File::open(&dir)
            .and_then(|f| f.sync_all())
            .map_err(|e| e.to_string())?;
        let mut p = Pointer {
            protocol: FORMAT.into(),
            transaction: dir.clone(),
            manifest_sha256: digest(&bytes)?,
            phase: Phase::Prepared,
            activated_pid: None,
        };
        validate_transaction(&dir, &p, true)?;
        guard.assert_unchanged()?;
        publish_pointer(&old.state_dir, &p)?; // No old-process save/effect after this durable barrier.
        apply_changes(&dir, &t)?;
        guard.assert_unchanged()?;
        p.phase = Phase::Published;
        publish_pointer(&old.state_dir, &p)?;
        Ok(
            json!({"type":FORMAT,"phase":"published","archive":dir,"operationId":id,"restartRequired":true,"fullResumeReady":false,"changedFields":t.changed_fields}),
        )
    }
}

pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let value=match args {
        [mode,socket,request] if mode=="active"=>{
            let request=Path::new(request);if !request.is_absolute(){return Err("request path must be absolute".into())}
            let response=control::admin_call(Path::new(socket),&format!("config migrate {}",request.to_str().ok_or("request path UTF-8")?))?;
            serde_json::from_str::<Value>(&response).map_err(|_|response)?
        }
        [mode,config,request] if mode=="stopped"=>{
            let path=PathBuf::from(config);let config=decode_config(&private(&path,262144)?)?;
            let mode=if matching_publication(&config,&path,&read_request(Path::new(request))?)?{None}else{Some(Path::new(request))};
            let mut runtime=Runtime::open_mode(config,path,mode)?;
            runtime.migrate_config(Path::new(request),true)?
        }
        _=>return Err("usage: grain-runtime config-migrate active ADMIN_SOCKET REQUEST | config-migrate stopped CONTROLLER_CONFIG REQUEST".into()),
    };
    if value["type"] != FORMAT {
        return Err("unexpected configuration migration response".into());
    }
    println!("{value}");
    Ok(())
}

fn matching_publication(config: &Config, path: &Path, r: &Request) -> Result<bool> {
    let Some(p) = read_pointer(&config.state_dir)? else {
        return Ok(false);
    };
    let (t, _, _) = validate_transaction(&p.transaction, &p, p.phase != Phase::Activated)?;
    Ok(t.config_path == path
        && serde_json::to_value(&t.request).map_err(|e| e.to_string())?
            == serde_json::to_value(r).map_err(|e| e.to_string())?)
}
fn completed_receipt(
    config: &Config,
    path: &Path,
    journal: &Journal,
    r: &Request,
) -> Result<Option<Value>> {
    if !matching_publication(config, path, r)? {
        return Ok(None);
    }
    let p = read_pointer(&config.state_dir)?.ok_or("publication disappeared")?;
    let (t, _, new) = validate_transaction(&p.transaction, &p, false)?;
    if p.phase != Phase::Activated || journal.binding != json!({"config":new,"configPath":path}) {
        return Err(
            "retained publication requires ordinary startup recovery before receipt".into(),
        );
    }
    Ok(Some(
        json!({"type":FORMAT,"phase":"activated","archive":p.transaction,"operationId":t.operation_id,
        "restartRequired":false,"fullResumeReady":false,"changedFields":t.changed_fields,"recoveredReceipt":true}),
    ))
}

/// Pure current-config scope description: no Runtime, key read, lock or network.
pub(crate) fn scope_config(path: &Path) -> Result<(Vec<u8>, Config)> {
    if !custody::canonical(path) {
        return Err("scope config path must be canonical absolute".into());
    }
    let bytes = private(path, 262144)?;
    let config = decode_config(&bytes)?;
    validate(&config)?;
    Ok((bytes, config))
}
fn scope_lock(config: &Config) -> Result<File> {
    let path = config.state_dir.join("controller.lock");
    let meta = fs::symlink_metadata(&path).map_err(|e| format!("existing controller lock: {e}"))?;
    if !meta.file_type().is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
        || meta.nlink() != 1
    {
        return Err("scope inspection needs existing private owned controller lock".into());
    }
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)
        .map_err(|e| format!("scope controller lock: {e}"))?;
    let opened = file.metadata().map_err(|e| e.to_string())?;
    if opened.dev() != meta.dev()
        || opened.ino() != meta.ino()
        || unsafe { libc::flock(file.as_raw_fd(), libc::LOCK_EX | libc::LOCK_NB) } != 0
    {
        return Err("scope inspection requires stopped exclusive controller custody".into());
    }
    Ok(file)
}
/// Root orchestrator runs this as the service UID after stopping the controller,
/// outside its old mount namespace. Scope staging is not migration permission:
/// the same-unit stopped receiver repeats native authority and closed proof.
pub(crate) fn scope_preflight(path: &Path, request_path: &Path) -> Result<Value> {
    if !custody::canonical(request_path) {
        return Err("scope request path must be canonical absolute".into());
    }
    let (initial, old) = scope_config(path)?;
    let _lock = scope_lock(&old)?;
    if private(path, 262144)? != initial {
        return Err("scope config changed acquiring custody".into());
    }
    session_failure::ensure_publication_known(&old.state_dir)?;
    if read_pointer(&old.state_dir)?.is_some_and(|p| p.phase != Phase::Activated) {
        return Err("scope preflight found pending publication; recover identical migration before requesting receipt".into());
    }
    let request_bytes = private(request_path, 65536)?;
    let r = decode_request(&request_bytes)?;
    let journal_path = old.state_dir.join("journal.json");
    let journal_bytes = private(&journal_path, LIMIT)?;
    let journal: Journal = serde_json::from_slice(&journal_bytes).map_err(|e| e.to_string())?;
    let (before, after, new, fields) = checked_request(&old, path, &journal.binding, &r)?;
    if !owner_rotation_shape(&old, &new, &fields)? {
        return Err("credential scope staging currently supports only exact same-subject owner-key migration".into());
    }
    let guard = ResidentGuard::acquire(&old, r.resident_state.as_deref())?;
    let source = crate::controller_write_scopes::describe_config(path, &before, &old)?;
    let target = crate::controller_write_scopes::describe_config(path, &after, &new)?;
    let observation =
        observe_owner_rotation(&old, &new, &fields)?.ok_or("owner observation missing")?;
    if observation.grant["tableSha256"] != target["providerTableSha256"]
        || crate::controller_write_scopes::describe_config(path, &before, &old)? != source
        || crate::controller_write_scopes::describe_config(path, &after, &new)? != target
        || private(path, 262144)? != before
        || private(&journal_path, LIMIT)? != journal_bytes
        || private(request_path, 65536)? != request_bytes
        || private(&r.target_config, 262144)? != after
    {
        return Err(
            "scope request/config/journal/provider selection changed during native observation"
                .into(),
        );
    }
    guard.assert_unchanged()?;
    Ok(
        json!({"type":"mini-controller-scope-preflight-v1","requestPath":request_path,
        "requestSha256":digest(&request_bytes)?,"source":source,"target":target,
        "sourceJournalSha256":digest(&journal_bytes)?,"changedFields":fields,"quiescenceRequired":true,
        "ownerEpoch":observation.epoch,"ownerObservationSha256":digest(&serde_json::to_vec(&observation).map_err(|e|e.to_string())?)?}),
    )
}
/// Consume the actual retained typed publication; never accept a caller-supplied
/// success label or infer migration from changed config bytes. This is read-only.
pub(crate) fn scope_receipt(path: &Path, request_path: &Path) -> Result<Value> {
    if !custody::canonical(request_path) {
        return Err("scope request path must be canonical absolute".into());
    }
    let (bytes, config) = scope_config(path)?;
    let _lock = scope_lock(&config)?;
    let request_bytes = private(request_path, 65536)?;
    let r = decode_request(&request_bytes)?;
    let p = read_pointer(&config.state_dir)?
        .ok_or("no source migration publication for scope receipt")?;
    if p.phase == Phase::Prepared {
        return Err(
            "scope publication requires exact migration recovery before finalization".into(),
        );
    }
    let (t, old, new) = validate_transaction(&p.transaction, &p, false)?;
    if t.config_path != path
        || serde_json::to_value(&t.request).map_err(|e| e.to_string())?
            != serde_json::to_value(&r).map_err(|e| e.to_string())?
        || !owner_rotation_shape(&old, &new, &t.changed_fields)?
        || digest(&bytes)? != r.target_config_sha256
        || serde_json::to_value(&config).map_err(|e| e.to_string())?
            != serde_json::to_value(&new).map_err(|e| e.to_string())?
    {
        return Err("scope receipt differs from exact owner migration publication".into());
    }
    let journal_path = config.state_dir.join("journal.json");
    let journal_bytes = private(&journal_path, LIMIT)?;
    let journal: Journal = serde_json::from_slice(&journal_bytes).map_err(|e| e.to_string())?;
    if journal.binding != json!({"config":new,"configPath":path}) {
        return Err("scope receipt journal has not received target binding".into());
    }
    for change in &t.changes {
        if change.role == Role::Journal && p.phase == Phase::Activated {
            continue;
        }
        if digest(&private(&change.path, LIMIT)?)? != change.after_sha256 {
            return Err("scope receipt publication vector is not fully received".into());
        }
    }
    let target = crate::controller_write_scopes::describe_config(path, &bytes, &new)?;
    if private(path, 262144)? != bytes
        || private(request_path, 65536)? != request_bytes
        || private(&journal_path, LIMIT)? != journal_bytes
    {
        return Err("scope receipt state changed during inspection".into());
    }
    Ok(
        json!({"type":"mini-controller-scope-receipt-v1","requestPath":request_path,
        "requestSha256":digest(&request_bytes)?,"archive":p.transaction,
        "transactionSha256":p.manifest_sha256,"phase":p.phase,"operationId":t.operation_id,"target":target}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    fn config() -> Config {
        serde_json::from_value(json!({"mini":"/bin/mini","host":"/bin/host","hostConfig":"/etc/mini/config.json",
            "hostSocket":"/run/mini.sock","controlSocket":"/run/controller.sock","custodyKey":"/private/key",
            "stateDir":"/private/state","cwd":"/private/work","task":"7001","subject":"7","capability":"75","queryCapability":"75","commands":[],
            "providerTask":{"task":"7004","subject":"9","capability":"101","queryCapability":"101","custodyKey":"/private/provider.key",
                "parentCapability":"75","parentObserveCapability":"75","reserve":"7000","maxInputTokens":16384,"maxOutputTokens":2048,
                "contextWindowTokens":262144,"model":"pinned-model","providers":"/etc/mini/providers.json","credentialBroker":"/etc/mini/keys-client.json",
                "gatewayBind":"127.0.0.1:18762","maxRequestBytes":12000,"maxResponseBytes":524288,
                "timeoutSeconds":180,"maxIterations":1}})).unwrap()
    }
    fn fields(old: &Config, new: &Config) -> Result<Vec<String>> {
        let path = Path::new("/private/controller.json");
        permitted_diff(
            old,
            new,
            &serde_json::to_vec(old).unwrap(),
            &json!({"config":old,"configPath":path}),
            path,
            None,
            None,
            true,
        )
    }
    #[test]
    fn explicit_operational_throttles_preserve_native_caps() {
        let old = config();
        let mut new = old.clone();
        let task = new.provider_task.as_mut().unwrap();
        task.max_iterations = Some(3);
        task.max_request_bytes = 32768;
        task.context_window_tokens = Some(131072);
        assert_eq!(fields(&old, &new).unwrap().len(), 3);
        assert_eq!(
            new.provider_task.as_ref().unwrap().reserve,
            old.provider_task.as_ref().unwrap().reserve
        );
        new.provider_task.as_mut().unwrap().max_input_tokens += 1;
        assert!(fields(&old, &new).is_err());
    }
    #[test]
    fn identity_budget_model_and_state_moves_need_other_typed_evidence() {
        let old = config();
        for field in ["subject", "capability", "stateDir", "custodyKey", "mini"] {
            let mut v = serde_json::to_value(&old).unwrap();
            v[field] = json!("changed");
            assert!(
                fields(&old, &serde_json::from_value(v).unwrap()).is_err(),
                "{field}"
            );
        }
        for field in ["reserve", "model", "providers", "gatewayBind"] {
            let mut v = serde_json::to_value(&old).unwrap();
            v["providerTask"][field] = json!("changed");
            assert!(
                fields(&old, &serde_json::from_value(v).unwrap()).is_err(),
                "{field}"
            );
        }
    }
    #[test]
    fn transport_cannot_borrow_operational_authority() {
        let old = config();
        let mut new = old.clone();
        new.host = "/bin/other-host".into();
        assert!(fields(&old, &new)
            .unwrap_err()
            .contains("root compatible admission"));
    }
    #[test]
    fn defaults_and_out_of_bounds_are_not_silent_expansion() {
        let old = config();
        let mut new = old.clone();
        new.provider_task.as_mut().unwrap().max_iterations = None;
        assert!(fields(&old, &new).is_err());
        new.provider_task.as_mut().unwrap().max_iterations = Some(7);
        assert!(fields(&old, &new).is_err());
        let mut new = old.clone();
        new.provider_task.as_mut().unwrap().context_window_tokens = Some(100);
        assert!(fields(&old, &new).is_err());
        let mut new = old.clone();
        new.provider_task.as_mut().unwrap().max_request_bytes = 1_048_577;
        assert!(fields(&old, &new).is_err());
    }
    fn fixture() -> (PathBuf, Transaction) {
        let root = std::env::temp_dir().join(format!(
            "migration-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        directory(&root).unwrap();
        let mut changes = Vec::new();
        for role in [Role::Config, Role::Journal, Role::Workspace] {
            let path = root.join(format!("live-{}", role.name()));
            write_new(&path, b"old").unwrap();
            changes
                .push(retain_change(&root, role, path, b"old".to_vec(), b"new".to_vec()).unwrap());
        }
        let t = Transaction {
            protocol: FORMAT.into(),
            operation_id: 1,
            config_path: root.join("config"),
            state_dir: root.clone(),
            request: Request {
                kind: FORMAT.into(),
                expected_config_sha256: "a".repeat(64),
                expected_binding_sha256: "b".repeat(64),
                target_config: root.join("target"),
                target_config_sha256: "c".repeat(64),
                resident_state: None,
                compatible_admission: None,
                mini_admission: None,
            },
            changed_fields: vec![],
            resident_sha256: None,
            resident_requests_sha256: None,
            quiescence_sha256: "d".repeat(64),
            owner_rotation_sha256: None,
            changes,
        };
        (root, t)
    }
    #[test]
    fn every_interrupted_receiving_vector_finishes_exactly() {
        for mask in 0..8 {
            let (root, t) = fixture();
            for (i, c) in t.changes.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    publish_bytes(&c.path, b"new", "crash").unwrap();
                }
            }
            apply_changes(&root, &t).unwrap();
            apply_changes(&root, &t).unwrap();
            for c in &t.changes {
                assert_eq!(private(&c.path, LIMIT).unwrap(), b"new");
            }
            fs::remove_dir_all(root).unwrap();
        }
    }
    #[test]
    fn unknown_member_refuses_before_any_other_replacement() {
        let (root, t) = fixture();
        publish_bytes(&t.changes[2].path, b"unknown", "foreign").unwrap();
        assert!(apply_changes(&root, &t).is_err());
        assert_eq!(private(&t.changes[0].path, LIMIT).unwrap(), b"old");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn exact_retained_temp_recovers_but_changed_temp_stays_visible() {
        let (root, t) = fixture();
        let path = &t.changes[0].path;
        let temp = path.with_file_name(format!(
            ".{}.migration-retry.tmp",
            path.file_name().unwrap().to_str().unwrap()
        ));
        write_new(&temp, b"new").unwrap();
        publish_bytes(path, b"new", "retry").unwrap();
        assert!(!temp.exists());
        write_new(&temp, b"unknown").unwrap();
        assert!(publish_bytes(path, b"new", "retry").is_err());
        assert_eq!(private(&temp, LIMIT).unwrap(), b"unknown");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn publication_barrier_freezes_old_process_and_resident() {
        let (root, _) = fixture();
        let archive = root.join("config-migrations");
        directory(&archive).unwrap();
        let p = Pointer {
            protocol: FORMAT.into(),
            transaction: archive.join("one"),
            manifest_sha256: "a".repeat(64),
            phase: Phase::Published,
            activated_pid: None,
        };
        publish_pointer(&root, &p).unwrap();
        assert!(ensure_process_current(&root).is_err());
        let mut c = config();
        c.state_dir = root.clone();
        assert!(ensure_resident_current(&c).is_err());
        let mut p = p;
        p.phase = Phase::Activated;
        p.activated_pid = Some(std::process::id());
        publish_pointer(&root, &p).unwrap();
        assert!(ensure_process_current(&root).is_ok());
        fs::remove_dir_all(root).unwrap();
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn invalid_prospective_socket_profile_leaves_all_files_and_selection_untouched() {
        let (root, _) = fixture();
        let mut old = config();
        old.state_dir = root.clone();
        old.control_socket = root.join("controller.sock");
        old.policy_control_capability = Some("75".into());
        old.dispatch_task = Some(serde_json::from_value(json!({
            "task":"7005","subject":"10","capability":"102","queryCapability":"102",
            "custodyKey":"/private/dispatch.key","parentCapability":"75","parentObserveCapability":"75",
            "reserve":"5","charge":"1","socketPath":root.join("dispatch.sock"),"hostUid":unsafe{libc::geteuid()},
            "operatorSocket":old.host_socket
        })).unwrap());
        let path = root.join("controller.json");
        let before = serde_json::to_vec_pretty(&old).unwrap();
        write_new(&path, &before).unwrap();
        let binding = json!({"config":old,"configPath":path});
        let journal = serde_json::to_vec_pretty(&Journal::fresh(binding.clone())).unwrap();
        write_new(&root.join("journal.json"), &journal).unwrap();
        let mut target = old.clone();
        target.provider_task.as_mut().unwrap().max_iterations = Some(3);
        let target_bytes = serde_json::to_vec_pretty(&target).unwrap();
        let target_path = root.join("target.json");
        write_new(&target_path, &target_bytes).unwrap();
        let request = Request {
            kind: FORMAT.into(),
            expected_config_sha256: digest(&before).unwrap(),
            expected_binding_sha256: value_digest(&binding).unwrap(),
            target_config: target_path,
            target_config_sha256: digest(&target_bytes).unwrap(),
            resident_state: None,
            compatible_admission: None,
            mini_admission: None,
        };
        let error = checked_request(&old, &path, &binding, &request)
            .err()
            .unwrap();
        assert!(error.contains("operatorSocket must be distinct"), "{error}");
        assert_eq!(private(&path, LIMIT).unwrap(), before);
        assert_eq!(private(&root.join("journal.json"), LIMIT).unwrap(), journal);
        assert!(!pointer_path(&root).exists());
        assert!(!root.join("config-migrations").exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn client_upgrade_requires_both_exact_admitted_manifest_paths() {
        let old = config();
        let mut new = old.clone();
        new.mini = "/bin/mini-v2".into();
        let source = json!({"mini":old.mini,"sha256":{"mini":"a".repeat(64)}});
        let target = json!({"mini":new.mini,"sha256":{"mini":"b".repeat(64)}});
        admitted_client(&old, &new, &source, &target, false).unwrap();
        new.mini = "/arbitrary/mini".into();
        assert!(admitted_client(&old, &new, &source, &target, false).is_err());
        assert!(admitted_client(&old, &old, &json!({}), &target, false).is_err());
        assert!(fields(&old, &new)
            .unwrap_err()
            .contains("root compatible admission"));
    }

    fn mini_fixture() -> (Config, Config, Vec<u8>, Value, MiniAdmission) {
        let old = config();
        let mut new = old.clone();
        new.mini = "/root-custody/mini-next".into();
        let bytes = serde_json::to_vec(&old).unwrap();
        let binding = json!({"config":old,"configPath":"/private/controller.json"});
        let admission = MiniAdmission {
            protocol: "mini-controller-client-upgrade-v1".into(),
            controller_config: "/private/controller.json".into(),
            controller_config_sha256: digest(&bytes).unwrap(),
            binding_sha256: value_digest(&binding).unwrap(),
            source_mini: AdmissionPin {
                path: old.mini.clone(),
                sha256: "a".repeat(64),
            },
            target_mini: AdmissionPin {
                path: new.mini.clone(),
                sha256: "b".repeat(64),
            },
            host: AdmissionPin {
                path: old.host.clone(),
                sha256: "c".repeat(64),
            },
            host_config: AdmissionPin {
                path: old.host_config.clone(),
                sha256: "d".repeat(64),
            },
            host_socket: old.host_socket.clone(),
        };
        (old, new, bytes, binding, admission)
    }
    #[test]
    fn mini_only_coordinates_preserve_exact_host_and_profile() {
        let (old, mut new, bytes, binding, mut a) = mini_fixture();
        let path = Path::new("/private/controller.json");
        mini_coordinates(&old, &new, &bytes, &binding, path, &a).unwrap();
        new.host_socket = Some("/other/socket".into());
        assert!(mini_coordinates(&old, &new, &bytes, &binding, path, &a).is_err());
        new.host_socket = old.host_socket.clone();
        a.binding_sha256 = "e".repeat(64);
        assert!(mini_coordinates(&old, &new, &bytes, &binding, path, &a).is_err());
    }
    #[test]
    fn mini_only_refuses_transport_authority_and_mixed_admissions_before_loading() {
        let (old, mut new, bytes, binding, _) = mini_fixture();
        let path = Path::new("/private/controller.json");
        let absent = AdmissionPin {
            path: "/absent/admission".into(),
            sha256: "a".repeat(64),
        };
        new.host = "/other/host".into();
        assert!(permitted_diff(
            &old,
            &new,
            &bytes,
            &binding,
            path,
            None,
            Some(&absent),
            true
        )
        .unwrap_err()
        .contains("cannot authorize Host"));
        new.host = old.host.clone();
        new.subject = "88".into();
        assert!(permitted_diff(
            &old,
            &new,
            &bytes,
            &binding,
            path,
            None,
            Some(&absent),
            true
        )
        .unwrap_err()
        .contains("unsupported configuration diff"));
        new.subject = old.subject.clone();
        assert!(permitted_diff(
            &old,
            &new,
            &bytes,
            &binding,
            path,
            Some(&absent),
            Some(&absent),
            true
        )
        .unwrap_err()
        .contains("exactly one"));
    }
    #[test]
    fn mini_only_requires_root_custody_even_for_exact_coordinates() {
        let (old, new, bytes, binding, a) = mini_fixture();
        let (root, _) = fixture();
        let path = root.join("operator-admission.json");
        let raw = serde_json::to_vec(&a).unwrap();
        write_new(&path, &raw).unwrap();
        let pin = AdmissionPin {
            path,
            sha256: digest(&raw).unwrap(),
        };
        assert!(admitted_mini(
            &old,
            &new,
            &bytes,
            &binding,
            Path::new("/private/controller.json"),
            &pin,
            true
        )
        .is_err());
        fs::remove_dir_all(root).unwrap();
    }

    fn rotating_owner() -> (Config, Config, OwnerRotation) {
        let mut old = config();
        old.provider_task.as_mut().unwrap().on_behalf_of = Some(OnBehalfOf {
            subject: "20".into(),
            public_key: "a".repeat(64),
        });
        let mut new = old.clone();
        new.provider_task
            .as_mut()
            .unwrap()
            .on_behalf_of
            .as_mut()
            .unwrap()
            .public_key = "b".repeat(64);
        let observation = OwnerRotation {
            protocol: "mini-controller-owner-rotation-observation-v1".into(),
            subject: "20".into(),
            old_public_key: "a".repeat(64),
            new_public_key: "b".repeat(64),
            epoch: "3".into(),
            owner: json!({"type":"native-owner-observation-v1","subject":"20","publicKey":"b".repeat(64),"keyEpoch":"3",
                "response":{"type":"subject-key-status-v1","subject":"20","publicKey":"b".repeat(64),"keyEpoch":"3","isCurrent":true,"currentRevoked":false}}),
            grant: json!({"type":"member-provider-grant-observation-v1","subject":"20","publicKey":"b".repeat(64),
                "model":"pinned-model","provider":"member","height":"15","source":{"task":"7004","height":"15"},
                "grant":{"runner":"9","perCall":"2048","perDay":"10","notAfter":"20","model":"pinned-model","ownerEpoch":"3"}}),
        };
        (old, new, observation)
    }
    #[test]
    fn owner_rotation_is_exact_same_subject_key_only() {
        let (old, mut new, _) = rotating_owner();
        assert_eq!(
            fields(&old, &new).unwrap(),
            vec![OWNER_KEY_FIELD.to_string()]
        );
        new.provider_task.as_mut().unwrap().max_iterations = Some(3);
        assert!(fields(&old, &new)
            .unwrap_err()
            .contains("separate typed transition"));
        new.provider_task.as_mut().unwrap().max_iterations = Some(1);
        new.provider_task
            .as_mut()
            .unwrap()
            .on_behalf_of
            .as_mut()
            .unwrap()
            .subject = "21".into();
        assert!(fields(&old, &new).is_err());
        new.provider_task.as_mut().unwrap().on_behalf_of = None;
        assert!(fields(&old, &new).is_err());
    }
    #[test]
    fn owner_archive_binds_current_epoch_model_runner_and_existing_ceiling() {
        let (old, new, mut observation) = rotating_owner();
        observation.validate(&old, &new).unwrap();
        observation.grant["grant"]["ownerEpoch"] = json!("2");
        assert!(observation.validate(&old, &new).is_err());
        observation.grant["grant"]["ownerEpoch"] = json!("3");
        observation.grant["grant"]["perCall"] = json!("2047");
        assert!(observation.validate(&old, &new).is_err());
        observation.grant["grant"]["perCall"] = json!("2048");
        observation.grant["grant"]["notAfter"] = json!("14");
        assert!(observation.validate(&old, &new).is_err());
    }
    #[test]
    fn owner_rotation_requires_exact_archive_and_old_transactions_remain_valid() {
        let (root, mut transaction) = fixture();
        let (old, new, observation) = rotating_owner();
        transaction.changed_fields = vec![OWNER_KEY_FIELD.into()];
        assert!(retained_owner_rotation(&root, &transaction, &old, &new).is_err());
        let bytes = serde_json::to_vec(&observation).unwrap();
        write_new(&root.join("owner-rotation.json"), &bytes).unwrap();
        transaction.owner_rotation_sha256 = Some(digest(&bytes).unwrap());
        retained_owner_rotation(&root, &transaction, &old, &new).unwrap();
        transaction.owner_rotation_sha256 = Some("f".repeat(64));
        assert!(retained_owner_rotation(&root, &transaction, &old, &new).is_err());
        let mut raw = serde_json::to_value(&transaction).unwrap();
        raw.as_object_mut().unwrap().remove("ownerRotationSha256");
        let old_format: Transaction = serde_json::from_value(raw).unwrap();
        assert!(old_format.owner_rotation_sha256.is_none());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn revoked_owner_blocks_partial_recovery_before_any_receiving_write() {
        let (root, mut t) = fixture();
        let (old, new, observation) = rotating_owner();
        t.changed_fields = vec![OWNER_KEY_FIELD.into()];
        let archive = serde_json::to_vec(&observation).unwrap();
        write_new(&root.join("owner-rotation.json"), &archive).unwrap();
        t.owner_rotation_sha256 = Some(digest(&archive).unwrap());
        retained_owner_rotation(&root, &t, &old, &new).unwrap();
        // One member was already published before a crash. A valid historical
        // observation cannot authorize completing the remaining members now.
        publish_bytes(&t.changes[0].path, b"new", "partial").unwrap();
        let pointer = root.join("config-migration.json");
        write_new(&pointer, b"retained-pointer").unwrap();
        let before: Vec<_> = t
            .changes
            .iter()
            .map(|c| fs::read(&c.path).unwrap())
            .collect();
        let error = recover_receiving_with(
            &root,
            &t,
            &old,
            &new,
            |_, _, _| Err("native current owner revoked".into()),
            || panic!("physical publication gate must not run after refused authority"),
        )
        .unwrap_err();
        assert!(error.contains("revoked"));
        assert_eq!(fs::read(&pointer).unwrap(), b"retained-pointer");
        for (change, expected) in t.changes.iter().zip(before) {
            assert_eq!(fs::read(&change.path).unwrap(), expected);
        }
        // Fresh observation still cannot publish before the physical fence.
        assert!(recover_receiving_with(
            &root,
            &t,
            &old,
            &new,
            |_, _, _| Ok(Some(observation)),
            || Err("sender still active".into())
        )
        .is_err());
        assert_eq!(fs::read(&t.changes[1].path).unwrap(), b"old");
        let (_, _, fresh) = rotating_owner();
        recover_receiving_with(&root, &t, &old, &new, |_, _, _| Ok(Some(fresh)), || Ok(()))
            .unwrap();
        for c in &t.changes {
            assert_eq!(fs::read(&c.path).unwrap(), b"new");
        }
        assert_eq!(fs::read(&pointer).unwrap(), b"retained-pointer");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn scope_staging_requires_stopped_custody_without_changing_the_lock() {
        let (root, _) = fixture();
        let mut cfg = config();
        cfg.state_dir = root.clone();
        let path = root.join("controller.lock");
        write_new(&path, b"retained-lock").unwrap();
        let first = scope_lock(&cfg).unwrap();
        assert!(scope_lock(&cfg).unwrap_err().contains("stopped exclusive"));
        assert_eq!(fs::read(&path).unwrap(), b"retained-lock");
        // Parallel tests spawn digest children. Explicit unlock avoids briefly
        // retaining this open-file-description in another thread's fork child.
        assert_eq!(unsafe { libc::flock(first.as_raw_fd(), libc::LOCK_UN) }, 0);
        drop(first);
        scope_lock(&cfg).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn scope_preflight_refuses_changed_request_binding_before_native_observation() {
        let (root, mut tx) = fixture();
        let (mut old, _, _) = rotating_owner();
        old.state_dir = root.clone();
        old.control_socket = root.join("control.sock");
        old.policy_control_capability = Some("76".into());
        old.commands = vec![serde_json::from_value(json!({"name":"hermes-acp","program":"/private/launcher/bwrap",
            "args":["--workspace","/private/work","--runtime-root","/private/runtime","--network","none","--","/agent/hermes-acp"],
            "systemdScope":true,"wallTimeSeconds":180,"reserve":"3","charge":"1"})).unwrap()];
        validate(&old).expect("complete managed provider fixture must pass ordinary validation");
        let config_path = root.join("controller.json");
        let raw = serde_json::to_vec(&old).unwrap();
        write_new(&config_path, &raw).unwrap();
        write_new(&root.join("controller.lock"), b"").unwrap();
        let journal = serde_json::to_vec(&Journal::fresh(
            json!({"config":old,"configPath":config_path}),
        ))
        .unwrap();
        write_new(&root.join("journal.json"), &journal).unwrap();
        let mut new = old.clone();
        new.provider_task
            .as_mut()
            .unwrap()
            .on_behalf_of
            .as_mut()
            .unwrap()
            .public_key = "b".repeat(64);
        let target_raw = serde_json::to_vec(&new).unwrap();
        write_new(&tx.request.target_config, &target_raw).unwrap();
        tx.request.expected_config_sha256 = digest(&raw).unwrap();
        tx.request.expected_binding_sha256 = "f".repeat(64);
        tx.request.target_config_sha256 = digest(&target_raw).unwrap();
        let request_path = root.join("request.json");
        write_new(&request_path, &serde_json::to_vec(&tx.request).unwrap()).unwrap();
        let error = scope_preflight(&config_path, &request_path).unwrap_err();
        assert!(
            error.contains("exact source configuration/journal binding"),
            "{error}"
        );
        assert_eq!(fs::read(&config_path).unwrap(), raw);
        assert_eq!(fs::read(root.join("journal.json")).unwrap(), journal);
        assert!(!root.join("config-migration.json").exists());
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn public_scope_binding_uses_eventual_receiving_path() {
        let mut cfg = config();
        cfg.provider_task = None;
        let raw = serde_json::to_vec(&cfg).unwrap();
        let path = Path::new("/private/live/controller.json");
        let scope = crate::controller_write_scopes::describe_config(path, &raw, &cfg).unwrap();
        assert_eq!(
            scope["bindingSha256"],
            value_digest(&json!({"config":cfg,"configPath":path})).unwrap()
        );
        assert_eq!(scope["configSha256"], digest(&raw).unwrap());
        assert_eq!(scope["type"], "mini-controller-write-scopes-v2");
        assert!(scope.get("credentialWriteDirectories").is_none() && scope["credentialBroker"].is_null());
    }
    #[test]
    fn scope_request_hash_and_validation_share_one_snapshot() {
        let (root, t) = fixture();
        let captured = serde_json::to_vec(&t.request).unwrap();
        let mut changed = t.request.clone();
        changed.expected_binding_sha256 = "e".repeat(64);
        let path = root.join("request-snapshot.json");
        write_new(&path, &serde_json::to_vec(&changed).unwrap()).unwrap();
        let decoded = decode_request(&captured).unwrap();
        assert_eq!(
            decoded.expected_binding_sha256,
            t.request.expected_binding_sha256
        );
        assert_ne!(
            decoded.expected_binding_sha256,
            read_request(&path).unwrap().expected_binding_sha256
        );
        assert!(decode_request(b"{}").is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
