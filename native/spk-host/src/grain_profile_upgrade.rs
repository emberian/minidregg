//! Local root admission of a compatible image/config transition. This is not
//! a portable history proof. Immutable profiles retain the complete old custody;
//! the only changes are explicitly pinned image/config fields and the stable
//! genesis config hash used by the legacy Store directory convention.
use super::*;
use crate::dispatch_author::FixedAuthoring;
use std::os::fd::AsRawFd;

use minidregg_compatible_upgrade_custody::{
    self as custody, canonical, image, root_ancestors, root_bytes, root_pin, sha,
};

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Selection {
    protocol: String,
    path: PathBuf,
    sha256: String,
    admission_path: PathBuf,
    admission_sha256: String,
}

fn stable_sha(profile: &HostProfile) -> &str {
    profile
        .genesis_config_sha256
        .as_deref()
        .unwrap_or(&profile.mini_config_sha256)
}
fn store(profile: &HostProfile) -> io::Result<&str> {
    let hash = stable_sha(profile);
    if !hex64(hash) {
        return Err(invalid("invalid genesis config hash"));
    }
    Ok(&hash[..16])
}
fn profile_layout(path: &Path, profile: &HostProfile) -> io::Result<()> {
    let store = store(profile)?;
    if !canonical(path)
        || profile.protocol != "mini-spk-grain-host-v2"
        || profile.state_root != profile.grains_root.join(store).join("host")
    {
        return Err(invalid("profile Store identity/layout refused"));
    }
    if !lifecycle_selector::decimal(&profile.management_subject)
        || !lifecycle_selector::decimal(&profile.management_key_epoch)
        || !hex64(&profile.management_public_key_hex)
        || !lifecycle_selector::decimal(&profile.completion_semantics)
        || ![
            &profile.state_root,
            &profile.mini_host,
            &profile.mini_config,
            &profile.mini_operator_socket,
            &profile.management_seed,
            &profile.completion_custodian_seed,
            &profile.bwrap,
            &profile.spk_host,
            &profile.grains_root,
        ]
        .iter()
        .all(|p| canonical(p))
    {
        return Err(invalid("profile custody coordinates refused"));
    }
    if let Some(seconds) = profile.ws_authority_lease_seconds {
        crate::web_socket::StreamLease::begin(Duration::from_secs(seconds))?;
    }
    root_ancestors(&profile.grains_root)?;
    let root = fs::symlink_metadata(&profile.grains_root)?;
    if !root.is_dir() || root.uid() != 0 || root.mode() & 0o022 != 0 {
        return Err(invalid("grains root custody refused"));
    }
    private_store_dirs(&profile.grains_root.join(store), &profile.state_root)?;
    Ok(())
}

// The root broker owns grains_root, but InitStore deliberately gives both
// the Store directory and host directory to the operator with mode 0700.
fn private_store_dirs(store_dir: &Path, state_root: &Path) -> io::Result<()> {
    private_dir(store_dir)?;
    private_dir(state_root)
}

pub(super) fn lock(state_root: &Path, exclusive: bool) -> io::Result<File> {
    private_dir(state_root)?;
    let path = state_root.join(".profile-selection.lock");
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.nlink() != 1
        || meta.mode() & 0o777 != 0o600
    {
        return Err(invalid("profile selection lock custody refused"));
    }
    if unsafe {
        libc::flock(
            file.as_raw_fd(),
            (if exclusive {
                libc::LOCK_EX
            } else {
                libc::LOCK_SH
            }) | libc::LOCK_NB,
        )
    } != 0
    {
        return Err(io::Error::last_os_error());
    }
    Ok(file)
}

pub(super) fn selected_path(state_root: &Path) -> io::Result<PathBuf> {
    selected_snapshot(state_root).map(|(path, _)| path)
}
fn selected_snapshot(state_root: &Path) -> io::Result<(PathBuf, Vec<u8>)> {
    let pointer = state_root.join("active-profile.json");
    if !exists(&pointer)? {
        let path = state_root.join("grain-host.json");
        let bytes = read_private(&path, MAX_JSON)?;
        let profile: HostProfile = serde_json::from_slice(&bytes)?;
        profile_layout(&path, &profile)?;
        if profile.state_root != state_root || profile.genesis_config_sha256.is_some() {
            return Err(invalid("baseline profile cannot override Store identity"));
        }
        return Ok((path, bytes));
    }
    let selection: Selection = serde_json::from_slice(&read_private(&pointer, MAX_JSON)?)?;
    if selection.protocol != "mini-spk-active-profile-v1" || !hex64(&selection.sha256) {
        return Err(invalid("active profile pointer refused"));
    }
    let bytes = read_private(&selection.path, MAX_JSON)?;
    if sha(&bytes) != selection.sha256 {
        return Err(invalid("selected profile hash differs"));
    }
    let profile: HostProfile = serde_json::from_slice(&bytes)?;
    if profile.state_root != state_root {
        return Err(invalid("selected profile names another Store"));
    }
    validate_successor(&selection, &profile)?;
    Ok((selection.path, bytes))
}

pub(super) fn validate_selected(path: &Path, profile: &HostProfile) -> io::Result<()> {
    profile_layout(path, profile)?;
    let (selected, bytes) = selected_snapshot(&profile.state_root)?;
    if selected != path || serde_json::from_slice::<HostProfile>(&bytes)? != *profile {
        return Err(invalid("profile is not the selected Store profile"));
    }
    if path == profile.state_root.join("grain-host.json") && profile.genesis_config_sha256.is_some()
    {
        return Err(invalid(
            "genesis compatibility field requires authenticated successor",
        ));
    }
    Ok(())
}

fn derive(
    old: &HostProfile,
    old_path: &Path,
    old_bytes: &[u8],
    admission_path: &Path,
    current: bool,
) -> io::Result<(HostProfile, PathBuf)> {
    let admission = if current {
        custody::load(admission_path)?
    } else {
        custody::load_evidence(admission_path)?
    };
    profile_layout(old_path, old)?;
    if old_path == old.state_root.join("grain-host.json") && old.genesis_config_sha256.is_some() {
        return Err(invalid(
            "canonical legacy profile cannot override genesis identity",
        ));
    }
    let identity_sha = sha(&read_private(
        &old.state_root.join("host-identity.json"),
        MAX_JSON,
    )?);
    if !admission.spk_profiles.iter().any(|p| {
        p.path == old_path
            && p.sha256 == sha(old_bytes)
            && p.store == store(old).unwrap_or("")
            && p.host_identity_sha256 == identity_sha
    }) {
        return Err(invalid("original grain profile is not root-admitted"));
    }
    let (_, old_host_sha) = image(&admission.source.manifest, "host")?;
    let (_, old_spk_sha) = image(&admission.source.manifest, "spkHost")?;
    if old.mini_host_sha256 != old_host_sha
        || old.spk_host_sha256 != old_spk_sha
        || old.mini_config_sha256 != admission.source.config_sha256
    {
        return Err(invalid(
            "old profile image/config pins differ from source admission",
        ));
    }
    let (host_path, host_sha) = image(&admission.target.manifest, "host")?;
    let (spk_path, spk_sha) = image(&admission.target.manifest, "spkHost")?;
    if current {
        root_pin(&spk_path, &spk_sha)?;
    }
    root_pin(&old.bwrap, &old.bwrap_sha256)?;
    let mut next = old.clone();
    next.genesis_config_sha256 = Some(stable_sha(old).to_owned());
    next.mini_host = host_path;
    next.mini_host_sha256 = host_sha;
    next.spk_host = spk_path;
    next.spk_host_sha256 = spk_sha;
    next.mini_config = admission.target.config_path;
    next.mini_config_sha256 = admission.target.config_sha256;
    if let Some(management_socket) = admission.management_socket {
        next.mini_operator_socket = management_socket;
    }
    let transaction = admission
        .transaction
        .file_name()
        .and_then(|n| n.to_str())
        .filter(|n| {
            !n.is_empty()
                && n.len() <= 128
                && n.bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'-' || b == b'_')
        })
        .ok_or_else(|| invalid("upgrade transaction name refused"))?;
    let path = old
        .state_root
        .join("upgrades")
        .join(transaction)
        .join("grain-host.json");
    Ok((next, path))
}

fn validate_successor(selection: &Selection, actual: &HostProfile) -> io::Result<()> {
    validate_lineage(selection, actual, 0)
}
fn validate_lineage(selection: &Selection, actual: &HostProfile, depth: usize) -> io::Result<()> {
    if selection.protocol != "mini-spk-active-profile-v1" {
        return Err(invalid("profile lineage selection protocol refused"));
    }
    if depth >= 32 {
        return Err(invalid("profile upgrade lineage exceeds bound"));
    }
    if sha(&root_bytes(&selection.admission_path, 4 * 1024 * 1024)?) != selection.admission_sha256 {
        return Err(invalid("admission hash differs"));
    }
    let admission = custody::load_evidence(&selection.admission_path)?;
    let mut matched = false;
    for pin in &admission.spk_profiles {
        if pin.store != store(actual)? {
            continue;
        }
        let bytes = read_private(&pin.path, MAX_JSON)?;
        if sha(&bytes) != pin.sha256 {
            return Err(invalid("retained original profile changed"));
        }
        let old: HostProfile = serde_json::from_slice(&bytes)?;
        let (expected, path) = derive(&old, &pin.path, &bytes, &selection.admission_path, false)?;
        if path == selection.path && expected == *actual {
            if pin.path != old.state_root.join("grain-host.json") {
                let record = pin
                    .path
                    .parent()
                    .ok_or_else(|| invalid("prior profile parent"))?
                    .join("active-profile.json");
                let prior: Selection = serde_json::from_slice(&read_private(&record, MAX_JSON)?)?;
                if prior.path != pin.path || prior.sha256 != sha(&bytes) {
                    return Err(invalid("prior profile selection differs"));
                }
                validate_lineage(&prior, &old, depth + 1)?;
            }
            matched = true;
            break;
        }
    }
    if !matched {
        return Err(invalid("successor differs from typed admitted transition"));
    }
    let parent = selection
        .path
        .parent()
        .ok_or_else(|| invalid("successor parent"))?;
    private_dir(&actual.state_root.join("upgrades"))?;
    private_dir(parent)?;
    Ok(())
}

fn stopped(state_root: &Path) -> io::Result<()> {
    let apps = state_root.join("apps");
    if !exists(&apps)? {
        return Ok(());
    }
    private_dir(&apps)?;
    for entry in fs::read_dir(apps)? {
        let entry = entry?;
        let app = entry.file_name().to_string_lossy().into_owned();
        if !broker::decimal(&app) {
            return Err(invalid("unexpected application directory"));
        }
        private_dir(&entry.path())?;
        for run in scan_runs(&entry.path())? {
            if !matches!(run.state, RunState::Stopped) {
                return Err(unresolved(format!(
                    "app {app} generation {} is not a completed STOP",
                    run.generation
                )));
            }
            let unit = broker::resident_unit(&app, &run.generation.to_string());
            let output = Command::new("/usr/bin/systemctl")
                .args([
                    "--system",
                    "show",
                    &unit,
                    "--property=ActiveState",
                    "--property=MainPID",
                    "--property=ControlPID",
                    "--property=ControlGroup",
                ])
                .stdin(Stdio::null())
                .output()?;
            let properties = String::from_utf8(output.stdout)
                .map_err(|_| invalid("unit properties are not UTF-8"))?;
            if !output.status.success()
                || !properties
                    .lines()
                    .any(|l| matches!(l, "ActiveState=inactive" | "ActiveState=failed"))
                || !properties.lines().any(|l| l == "MainPID=0")
                || !properties.lines().any(|l| l == "ControlPID=0")
            {
                return Err(unresolved(format!(
                    "app {app} generation {} resident is not stopped",
                    run.generation
                )));
            }
            let cgroup = properties
                .lines()
                .find_map(|l| l.strip_prefix("ControlGroup="))
                .ok_or_else(|| invalid("unit cgroup absent"))?;
            if !cgroup.is_empty() {
                if !canonical(Path::new(cgroup)) {
                    return Err(invalid("unit cgroup path refused"));
                }
                let events = Path::new("/sys/fs/cgroup")
                    .join(cgroup.trim_start_matches('/'))
                    .join("cgroup.events");
                if !fs::read_to_string(events)?
                    .lines()
                    .any(|l| l == "populated 0")
                {
                    return Err(unresolved("resident cgroup still populated"));
                }
            }
        }
    }
    Ok(())
}

pub(super) fn rebind(old_path: &Path, admission_path: &Path) -> io::Result<Value> {
    if unsafe { libc::geteuid() } == 0 {
        return Err(invalid("profile rebind runs as Store operator"));
    }
    let old_bytes = read_private(old_path, MAX_JSON)?;
    let old: HostProfile = serde_json::from_slice(&old_bytes)?;
    profile_layout(old_path, &old)?;
    let _lock = lock(&old.state_root, true)?;
    let (next, next_path) = derive(&old, old_path, &old_bytes, admission_path, true)?;
    let selected = selected_path(&old.state_root)?;
    if selected != old_path && selected != next_path {
        return Err(invalid("another upgrade profile is already selected"));
    }
    stopped(&old.state_root)?;
    private_directory(&old.state_root.join("upgrades"))?;
    private_directory(
        next_path
            .parent()
            .ok_or_else(|| invalid("successor parent"))?,
    )?;
    let next_bytes = serde_json::to_vec_pretty(&next)?;
    derived_file(&next_path, &next_bytes)?;
    let selection = Selection {
        protocol: "mini-spk-active-profile-v1".into(),
        path: next_path.clone(),
        sha256: sha(&next_bytes),
        admission_path: admission_path.into(),
        admission_sha256: sha(&root_bytes(admission_path, 4 * 1024 * 1024)?),
    };
    validate_successor(&selection, &next)?;
    let pointer = old.state_root.join("active-profile.json");
    let staging = next_path.parent().unwrap().join("active-profile.json");
    derived_file(&staging, &serde_json::to_vec_pretty(&selection)?)?;
    // Keep an immutable selection record and replace only the small live pointer.
    let temp = old
        .state_root
        .join(format!(".active-profile-{}.tmp", std::process::id()));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(libc::O_NOFOLLOW)
        .open(&temp)?;
    file.write_all(&serde_json::to_vec_pretty(&selection)?)?;
    file.sync_all()?;
    fs::rename(&temp, &pointer)?;
    File::open(&old.state_root)?.sync_all()?;
    Ok(
        json!({"protocol":"mini-spk-profile-rebind-v1","store":store(&next)?,"previousProfile":old_path,
        "profile":next_path,"profileSha256":selection.sha256,"admission":admission_path,"activeProfile":pointer}),
    )
}

pub(super) fn session_intents(host: &Host, app: &str) -> io::Result<Value> {
    if !broker::decimal(app) {
        return Err(invalid("app is not canonical"));
    }
    let app_dir = host.app_dir(app);
    private_dir(&app_dir)?;
    let mut intents = Vec::new();
    for mut route in routes(&app_dir, app)? {
        let custody_path = PathBuf::from(
            route
                .get("dispatchCustody")
                .and_then(Value::as_str)
                .ok_or_else(|| invalid("route custody absent"))?,
        );
        let directory = custody_path
            .parent()
            .ok_or_else(|| invalid("route directory absent"))?;
        private_dir(directory)?;
        let policy = crate::http_entrance::CustodianPolicy::load(directory)?;
        let custody = read_json(&custody_path)?;
        let fixed: FixedAuthoring = serde_json::from_value(custody.clone())?;
        fixed.validate()?;
        let kind = match policy.fixed_session_kind {
            crate::http_entrance::EntranceKind::Browser => "web",
            crate::http_entrance::EntranceKind::Api => "api",
        };
        if policy.fixed_app != fixed.app
            || policy.fixed_subject != fixed.subject
            || policy.fixed_session != fixed.session
            || policy.fixed_ticket != fixed.ticket_resource
            || kind != fixed.session_kind
        {
            return Err(invalid("route entrance and fixed custody differ"));
        }
        let custody_sha256 = file_sha256(&custody_path)?;
        let custodian_sha256 = file_sha256(&directory.join("custodian.json"))?;
        let route_fields = route
            .as_object_mut()
            .ok_or_else(|| invalid("retained route is not an object"))?;
        route_fields.insert("dispatchCustodySha256".into(), json!(custody_sha256));
        route_fields.insert("custodianSha256".into(), json!(custodian_sha256));
        intents.push(
            json!({"route":route,"custody":custody,"custodySha256":custody_sha256,
            "enrollmentRole":null}),
        );
    }
    Ok(
        json!({"protocol":"mini-spk-session-intents-v1","store":host.store,"app":app,"intents":intents}),
    )
}

/// Discovery performs no Host invocation and writes no profile or lock file.
pub(super) fn current_profile(baseline: &Path) -> io::Result<Value> {
    let old: HostProfile = serde_json::from_slice(&read_private(baseline, MAX_JSON)?)?;
    profile_layout(baseline, &old)?;
    if baseline != old.state_root.join("grain-host.json") || old.genesis_config_sha256.is_some() {
        return Err(invalid(
            "current-profile requires the retained canonical baseline",
        ));
    }
    let (path, bytes) = selected_snapshot(&old.state_root)?;
    Ok(
        json!({"protocol":"mini-spk-current-profile-v1","store":store(&old)?,"profile":path,"profileSha256":sha(&bytes)}),
    )
}

pub(super) fn runtime_status(path: &Path) -> io::Result<Value> {
    let profile: HostProfile = serde_json::from_slice(&read_private(path, MAX_JSON)?)?;
    let _lock = lock(&profile.state_root, false)?;
    validate_selected(path, &profile)?;
    broker::call(&Request::RuntimeStatus {
        store: store(&profile)?.into(),
    })
}

pub(super) fn require_ready_runtime(profile: &HostProfile) -> io::Result<()> {
    let value = broker::call(&Request::RuntimeStatus {
        store: store(profile)?.into(),
    })?;
    if value.get("protocol").and_then(Value::as_str) != Some("mini-spk-runtime-status-v1")
        || value.get("brokerProtocol").and_then(Value::as_str) != Some("mini-spk-broker-runtime-v1")
        || value.get("store").and_then(Value::as_str) != Some(store(profile)?)
        || !matches!(
            value.get("state").and_then(Value::as_str),
            Some("baseline" | "ready")
        )
        || value.get("spkHost").and_then(Value::as_str) != profile.spk_host.to_str()
        || value.get("spkHostSha256").and_then(Value::as_str) != Some(&profile.spk_host_sha256)
    {
        return Err(invalid(
            "broker runtime is not ready for selected profile; adopt runtime before START",
        ));
    }
    Ok(())
}

pub(super) fn adopt_runtime(path: &Path, admission: &Path) -> io::Result<Value> {
    if unsafe { libc::geteuid() } == 0 {
        return Err(invalid("grain runtime adoption runs as Store operator"));
    }
    let profile: HostProfile = serde_json::from_slice(&read_private(path, MAX_JSON)?)?;
    let _lock = lock(&profile.state_root, true)?;
    validate_selected(path, &profile)?;
    let expected = custody::load(admission)?;
    let (target_path, target_sha) = image(&expected.target.manifest, "spkHost")?;
    if profile.spk_host != target_path
        || profile.spk_host_sha256 != target_sha
        || profile.mini_config != expected.target.config_path
        || profile.mini_config_sha256 != expected.target.config_sha256
    {
        return Err(invalid(
            "selected profile differs from admitted target runtime",
        ));
    }
    let reply = broker::call(&Request::AdoptRuntime {
        store: store(&profile)?.into(),
        admission: admission.into(),
    })?;
    if reply.get("protocol").and_then(Value::as_str) != Some("mini-spk-runtime-adoption-v1")
        || reply.get("brokerProtocol").and_then(Value::as_str) != Some("mini-spk-broker-runtime-v1")
        || reply.get("store").and_then(Value::as_str) != Some(store(&profile)?)
        || reply.get("state").and_then(Value::as_str) != Some("ready")
        || reply.get("spkHost").and_then(Value::as_str) != profile.spk_host.to_str()
        || reply.get("spkHostSha256").and_then(Value::as_str) != Some(&profile.spk_host_sha256)
        || reply.get("admission").and_then(Value::as_str) != admission.to_str()
        || reply.get("admissionSha256").and_then(Value::as_str)
            != Some(&sha(&root_bytes(admission, 4 * 1024 * 1024)?))
    {
        return Err(invalid(
            "broker runtime adoption reply differs from request",
        ));
    }
    Ok(reply)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn canonical_paths_reject_traversal_and_aliases() {
        for path in ["relative", "/a/../b", "/a/./b", "/a//b", "/a/b/"] {
            assert!(!canonical(Path::new(path)), "{path}");
        }
        assert!(canonical(Path::new(
            "/var/lib/mini/upgrades/tx/compatible-admission.json"
        )));
    }
    #[test]
    fn active_selection_is_closed_schema() {
        let v = json!({"protocol":"mini-spk-active-profile-v1","path":"/a","sha256":"a", "admissionPath":"/b","admissionSha256":"b","override":true});
        assert!(serde_json::from_value::<Selection>(v).is_err());
    }
    #[test]
    fn selected_profile_tampering_refuses_before_loading_or_executing() {
        let mut nonce = [0u8; 8];
        File::open("/dev/urandom")
            .unwrap()
            .read_exact(&mut nonce)
            .unwrap();
        let root = std::env::temp_dir().join(format!(
            "grain-profile-test-{}-{}",
            std::process::id(),
            u64::from_le_bytes(nonce)
        ));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let profile = root.join("successor.json");
        derived_file(&profile, b"{}").unwrap();
        let selection = Selection {
            protocol: "mini-spk-active-profile-v1".into(),
            path: profile,
            sha256: "0".repeat(64),
            admission_path: PathBuf::from("/not-read"),
            admission_sha256: "0".repeat(64),
        };
        derived_file(
            &root.join("active-profile.json"),
            &serde_json::to_vec(&selection).unwrap(),
        )
        .unwrap();
        let error = selected_path(&root).unwrap_err();
        assert_eq!(error.to_string(), "selected profile hash differs");
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn profile_switch_excludes_readers_but_ordinary_commands_coexist() {
        let root =
            std::env::temp_dir().join(format!("grain-profile-lock-test-{}", std::process::id()));
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        let first = lock(&root, false).unwrap();
        let second = lock(&root, false).unwrap();
        assert!(lock(&root, true).is_err());
        drop(first);
        drop(second);
        let writer = lock(&root, true).unwrap();
        assert!(lock(&root, false).is_err());
        drop(writer);
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn broker_operator_owned_store_and_host_are_accepted_but_not_writable_or_symlinked() {
        let root =
            std::env::temp_dir().join(format!("grain-profile-store-test-{}", std::process::id()));
        let store = root.join("0123456789abcdef");
        let host = store.join("host");
        DirBuilder::new().mode(0o700).create(&root).unwrap();
        DirBuilder::new().mode(0o700).create(&store).unwrap();
        DirBuilder::new().mode(0o700).create(&host).unwrap();
        assert!(private_store_dirs(&store, &host).is_ok());
        fs::set_permissions(&store, fs::Permissions::from_mode(0o770)).unwrap();
        assert!(private_store_dirs(&store, &host).is_err());
        fs::set_permissions(&store, fs::Permissions::from_mode(0o700)).unwrap();
        let alias = store.join("alias");
        std::os::unix::fs::symlink(&host, &alias).unwrap();
        assert!(private_store_dirs(&store, &alias).is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
