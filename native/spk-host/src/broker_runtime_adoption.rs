//! Per-Store root runtime adoption. The broker's baseline and other Stores
//! retain their existing images. A pending record fences START until all exact
//! supervisor instances are rendered and systemd acknowledges daemon-reload.
use super::*;
use minidregg_compatible_upgrade_custody as custody;
use std::collections::BTreeSet;

const RUNTIME_PROTOCOL: &str = "mini-spk-broker-runtime-v1";
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(super) struct RuntimePin {
    pub(super) spk_host: PathBuf,
    pub(super) spk_host_sha256: String,
}
#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Adoption {
    protocol: String,
    store: String,
    state: String,
    admission: PathBuf,
    admission_sha256: String,
    source_profile: PathBuf,
    source_profile_sha256: String,
    runtime: RuntimePin,
    apps: Vec<String>,
}

impl Broker {
    fn runtime_path(&self, store: &str) -> PathBuf {
        self.broker_dir()
            .join("runtimes")
            .join(format!("{store}.json"))
    }
    fn adoption(&self, store: &str) -> io::Result<Option<Adoption>> {
        if !store_key(store) {
            return Err(invalid("runtime Store refused"));
        }
        match read_private_root(&self.runtime_path(store), MAX_CONFIG) {
            Ok(bytes) => {
                let record: Adoption = serde_json::from_slice(&bytes)?;
                if record.protocol != RUNTIME_PROTOCOL
                    || record.store != store
                    || !matches!(record.state.as_str(), "pending" | "ready")
                    || record.apps.iter().any(|app| !decimal(app))
                    || record.apps.iter().collect::<BTreeSet<_>>().len() != record.apps.len()
                {
                    return Err(invalid("runtime adoption record refused"));
                }
                let bytes = custody::root_bytes(&record.admission, 4 * 1024 * 1024)?;
                if custody::sha(&bytes) != record.admission_sha256 {
                    return Err(invalid("runtime admission changed"));
                }
                let admission = custody::load_evidence(&record.admission)?;
                let (path, sha) = custody::image(&admission.target.manifest, "spkHost")?;
                if record.runtime.spk_host != path
                    || record.runtime.spk_host_sha256 != sha
                    || !admission.spk_profiles.iter().any(|p| {
                        p.store == store
                            && p.path == record.source_profile
                            && p.sha256 == record.source_profile_sha256
                    })
                {
                    return Err(invalid("runtime adoption differs from root admission"));
                }
                Ok(Some(record))
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
            Err(e) => Err(e),
        }
    }
    pub(super) fn adoption_exists(&self, store: &str) -> io::Result<bool> {
        Ok(self.adoption(store)?.is_some())
    }
    pub(super) fn require_not_pending(&self, store: &str) -> io::Result<()> {
        if self
            .adoption(store)?
            .is_some_and(|record| record.state == "pending")
        {
            return Err(invalid(
                "Store runtime adoption is pending; retry adopt-runtime",
            ));
        }
        Ok(())
    }
    pub(super) fn runtime_for(&self, store: &str) -> io::Result<RuntimePin> {
        let pin = match self.adoption(store)? {
            Some(record) if record.state == "ready" => record.runtime,
            Some(_) => {
                return Err(invalid(
                    "Store runtime adoption is pending; retry adopt-runtime",
                ))
            }
            None => RuntimePin {
                spk_host: self.config.spk_host.clone(),
                spk_host_sha256: self.config.spk_host_sha256.clone(),
            },
        };
        custody::root_pin(&pin.spk_host, &pin.spk_host_sha256)?;
        unit_argument(&pin.spk_host)?;
        Ok(pin)
    }
    pub(super) fn runtime_status(&self, store: &str) -> io::Result<Value> {
        let record = self.adoption(store)?;
        let pin = record
            .as_ref()
            .map(|r| r.runtime.clone())
            .unwrap_or(RuntimePin {
                spk_host: self.config.spk_host.clone(),
                spk_host_sha256: self.config.spk_host_sha256.clone(),
            });
        custody::root_pin(&pin.spk_host, &pin.spk_host_sha256)?;
        Ok(
            json!({"protocol":"mini-spk-runtime-status-v1", "brokerProtocol":RUNTIME_PROTOCOL,"store":store,
            "state":record.as_ref().map(|r|r.state.as_str()).unwrap_or("baseline"),
            "spkHost":pin.spk_host,"spkHostSha256":pin.spk_host_sha256,
            "admission":record.as_ref().map(|r|&r.admission),"admissionSha256":record.as_ref().map(|r|&r.admission_sha256)}),
        )
    }
    fn store_apps(&self, store: &str) -> io::Result<BTreeSet<String>> {
        let mut apps = BTreeSet::new();
        for entry in fs::read_dir(self.broker_dir().join("placements"))? {
            let entry = entry?;
            let placement: Placement =
                serde_json::from_slice(&read_private_root(&entry.path(), MAX_CONFIG)?)?;
            if placement.store == store {
                Self::check_coordinates(store, &placement.app)?;
                apps.insert(placement.app);
            }
        }
        Ok(apps)
    }
    fn operator_bytes(&self, path: &Path) -> io::Result<Vec<u8>> {
        let relative = path
            .strip_prefix(self.root())
            .map_err(|_| invalid("profile outside broker grains root"))?;
        let parts: Vec<&str> = relative
            .components()
            .map(|c| {
                c.as_os_str()
                    .to_str()
                    .ok_or_else(|| invalid("profile path encoding"))
            })
            .collect::<io::Result<_>>()?;
        let mut file = open_operator_file(self.root(), &parts, self.operator_uid)?;
        let meta = file.metadata()?;
        if meta.mode() & 0o777 != 0o600
            || meta.nlink() != 1
            || meta.len() == 0
            || meta.len() > MAX_CONFIG
        {
            return Err(invalid(
                "operator evidence must be private bounded single-link file",
            ));
        }
        let mut bytes = Vec::new();
        Read::by_ref(&mut file)
            .take(MAX_CONFIG + 1)
            .read_to_end(&mut bytes)?;
        if bytes.len() as u64 != meta.len() {
            return Err(invalid("operator evidence changed while reading"));
        }
        Ok(bytes)
    }
    fn source_pin(
        &self,
        store: &str,
        admission: &custody::Admission,
    ) -> io::Result<(PathBuf, String)> {
        let matches: Vec<_> = admission
            .spk_profiles
            .iter()
            .filter(|p| p.store == store)
            .collect();
        if matches.len() != 1 {
            return Err(invalid(
                "root admission must uniquely identify this Store profile",
            ));
        }
        let pin = matches[0];
        let bytes = self.operator_bytes(&pin.path)?;
        if custody::sha(&bytes) != pin.sha256 {
            return Err(invalid("root-admitted source profile changed"));
        }
        let profile: Value = serde_json::from_slice(&bytes)?;
        let state_root = self.root().join(store).join("host");
        let (_, source_spk_sha) = custody::image(&admission.source.manifest, "spkHost")?;
        if profile.get("stateRoot").and_then(Value::as_str) != state_root.to_str()
            || profile.get("grainsRoot").and_then(Value::as_str) != self.root().to_str()
            || profile.get("spkHostSha256").and_then(Value::as_str) != Some(&source_spk_sha)
            || profile.get("miniConfigSha256").and_then(Value::as_str)
                != Some(&admission.source.config_sha256)
            || custody::sha(&self.operator_bytes(&state_root.join("host-identity.json"))?)
                != pin.host_identity_sha256
        {
            return Err(invalid(
                "admitted source profile Store/runtime identity differs",
            ));
        }
        Ok((pin.path.clone(), pin.sha256.clone()))
    }
    fn store_quiescent(&self, store: &str, apps: &BTreeSet<String>) -> io::Result<()> {
        // Read retained generations without trusting directory traversal through
        // operator-owned symlinks. Every attempted generation must have STOP evidence.
        let mut checked_units = BTreeSet::new();
        for app in apps {
            let app_dir = self.root().join(store).join("host/apps").join(app);
            for entry in fs::read_dir(&app_dir)? {
                let entry = entry?;
                let name = entry.file_name().to_string_lossy().into_owned();
                let Some(generation) = name.strip_prefix('g').filter(|g| decimal(g)) else {
                    continue;
                };
                self.operator_bytes(&entry.path().join("resident.json"))?;
                self.operator_bytes(&entry.path().join("start-completed-v3.json"))
                    .map_err(|_| invalid("runtime adoption refuses incomplete START"))?;
                let mut completion = entry.path().join("stop-completion");
                let mut stopped = false;
                for _ in 0..8 {
                    match self.operator_bytes(&completion.join("receipt-anchor.json")) {
                        Ok(_) => {
                            stopped = true;
                            break;
                        }
                        Err(e) if e.kind() == io::ErrorKind::NotFound => {
                            completion = completion.join("replan")
                        }
                        Err(e) => return Err(e),
                    }
                }
                if !stopped {
                    return Err(invalid("runtime adoption requires completed STOP"));
                }
                let unit = resident_unit(app, generation);
                unit_quiescent(&unit)?;
                checked_units.insert(unit);
            }
            unit_quiescent(&supervisor_unit(&self.config.unit_prefix, store, app))?;
        }
        // Also fence installed units whose retained operator journal disappeared.
        for entry in fs::read_dir(self.broker_dir().join("units"))? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            if self.unit_store(&name)?.as_deref() == Some(store) {
                let (app, _) = Self::check_resident_unit_name(&name)?;
                if !apps.contains(&app) || !checked_units.contains(&name) {
                    return Err(invalid("runtime Store has an unexplained installed unit"));
                }
                unit_quiescent(&name)?;
            }
        }
        Ok(())
    }
    pub(super) fn render_store_supervisor(
        &self,
        store: &str,
        app: &str,
        pin: &RuntimePin,
    ) -> io::Result<String> {
        let unit = supervisor_unit(&self.config.unit_prefix, store, app);
        let path = Path::new(RUNTIME_UNITS).join(&unit);
        let text = supervisor_text(&self.config, self.operator_gid, store, app, pin)?;
        match fs::symlink_metadata(&path) {
            Ok(meta) => {
                if !meta.is_file()
                    || meta.uid() != 0
                    || meta.mode() & 0o022 != 0
                    || !fs::read_to_string(&path)?.starts_with(&format!(
                        "# rendered by mini-spk-broker store={store} app={app}\n"
                    ))
                {
                    return Err(invalid(
                        "supervisor instance exists outside broker ownership",
                    ));
                }
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => return Err(e),
        }
        write_root_text(&path, &text, 0o644, true)?;
        Ok(unit)
    }
    pub(super) fn render_adopted_supervisors(&self) -> io::Result<()> {
        for entry in fs::read_dir(self.broker_dir().join("runtimes"))? {
            let name = entry?.file_name().to_string_lossy().into_owned();
            let store = name
                .strip_suffix(".json")
                .ok_or_else(|| invalid("runtime record name refused"))?;
            if let Some(record) = self.adoption(store)? {
                if record.state == "ready" {
                    let pin = self.runtime_for(store)?;
                    for app in self.store_apps(store)? {
                        self.render_store_supervisor(store, &app, &pin)?;
                    }
                }
            }
        }
        Ok(())
    }
    pub(super) fn adopt_runtime(&self, store: &str, path: &Path) -> io::Result<Value> {
        if !store_key(store) {
            return Err(invalid("runtime Store refused"));
        }
        let admission = custody::load(path)?;
        let (source_profile, source_profile_sha256) = self.source_pin(store, &admission)?;
        let (spk_host, spk_host_sha256) = custody::image(&admission.target.manifest, "spkHost")?;
        custody::root_pin(&spk_host, &spk_host_sha256)?;
        unit_argument(&spk_host)?;
        let old = self.adoption(store)?;
        let apps = self.store_apps(store)?;
        let retained_apps = old
            .as_ref()
            .filter(|r| r.admission == path)
            .map(|r| r.apps.clone())
            .unwrap_or_else(|| apps.iter().cloned().collect());
        let record = Adoption {
            protocol: RUNTIME_PROTOCOL.into(),
            store: store.into(),
            state: "pending".into(),
            admission: path.into(),
            admission_sha256: custody::sha(&custody::root_bytes(path, 4 * 1024 * 1024)?),
            source_profile,
            source_profile_sha256,
            apps: retained_apps,
            runtime: RuntimePin {
                spk_host,
                spk_host_sha256,
            },
        };
        let (_, source_sha) = custody::image(&admission.source.manifest, "spkHost")?;
        let retry = classify_adoption(
            old.as_ref(),
            &record,
            &self.config.spk_host_sha256,
            &source_sha,
        )?;
        if retry != Retry::AlreadyReady {
            require_frozen_apps(&record, &apps)?;
            self.store_quiescent(store, &apps)?;
            complete_adoption(
                &record,
                |record| {
                    write_root_text(
                        &self.runtime_path(store),
                        &serde_json::to_string_pretty(record)?,
                        0o600,
                        true,
                    )
                    .map(|_| ())
                },
                || {
                    for app in &record.apps {
                        self.render_store_supervisor(store, app, &record.runtime)?;
                    }
                    Ok(())
                },
                || systemctl(&["daemon-reload"]).map(|_| ()),
            )?;
        }
        Ok(
            json!({"protocol":"mini-spk-runtime-adoption-v1","brokerProtocol":RUNTIME_PROTOCOL,"store":store,"state":"ready",
            "spkHost":record.runtime.spk_host,"spkHostSha256":record.runtime.spk_host_sha256,
            "admission":record.admission,"admissionSha256":record.admission_sha256,
            "supervisors":record.apps.iter().map(|app|supervisor_unit(&self.config.unit_prefix,store,app)).collect::<Vec<_>>()}),
        )
    }
    pub(super) fn save_unit_runtime(&self, unit: &str, pin: &RuntimePin) -> io::Result<()> {
        write_root_text(
            &self.broker_dir().join("unit-runtimes").join(unit),
            &serde_json::to_string(pin)?,
            0o600,
            false,
        )?;
        Ok(())
    }
    pub(super) fn require_unit_runtime(&self, store: &str, unit: &str) -> io::Result<()> {
        let current = self.runtime_for(store)?;
        let saved = self.broker_dir().join("unit-runtimes").join(unit);
        match read_private_root(&saved, MAX_CONFIG) {
            Ok(bytes) => {
                let pinned: RuntimePin = serde_json::from_slice(&bytes)?;
                if pinned != current {
                    return Err(invalid(
                        "unit belongs to a previous runtime; START a new generation",
                    ));
                }
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound && self.adoption(store)?.is_none() => {}
            Err(e) => return Err(e),
        }
        Ok(())
    }
}

#[derive(Debug, PartialEq, Eq)]
enum Retry {
    New,
    Pending,
    AlreadyReady,
}
fn classify_adoption(
    old: Option<&Adoption>,
    next: &Adoption,
    baseline_sha: &str,
    source_sha: &str,
) -> io::Result<Retry> {
    if old.is_some_and(|prior| prior.store != next.store) {
        return Err(invalid("runtime transition cannot cross Store identity"));
    }
    match old {
        Some(prior) if prior.admission == next.admission => {
            let mut expected = next.clone();
            expected.state = prior.state.clone();
            if *prior != expected {
                return Err(invalid(
                    "same admission cannot change runtime adoption pins",
                ));
            }
            Ok(if prior.state == "ready" {
                Retry::AlreadyReady
            } else {
                Retry::Pending
            })
        }
        Some(prior) if prior.state == "pending" => {
            Err(invalid("another runtime adoption is pending"))
        }
        Some(prior) if prior.runtime.spk_host_sha256 != source_sha => {
            Err(invalid("upgrade source is not currently adopted runtime"))
        }
        None if baseline_sha != source_sha => {
            Err(invalid("upgrade source is not broker baseline runtime"))
        }
        _ => Ok(Retry::New),
    }
}
fn unit_argument(path: &Path) -> io::Result<&str> {
    let text = path.to_str().ok_or_else(|| invalid("unit path encoding"))?;
    if !custody::canonical(path)
        || !text
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"/_-.".contains(&b))
    {
        return Err(invalid("unit path contains systemd syntax"));
    }
    Ok(text)
}
fn supervisor_text(
    config: &BrokerConfig,
    gid: u32,
    store: &str,
    app: &str,
    pin: &RuntimePin,
) -> io::Result<String> {
    Broker::check_coordinates(store, app)?;
    let spk = unit_argument(&pin.spk_host)?;
    let root = unit_argument(&config.grains_root)?;
    Ok(format!("# rendered by mini-spk-broker store={store} app={app}\n[Unit]\nDescription=Mini SPK grain supervisor {store}-{app}\n\
        StartLimitIntervalSec=1800\nStartLimitBurst=3\n\n[Service]\nType=exec\nUser={user}\nGroup={gid}\nSlice={prefix}-grains.slice\n\
        ExecStart={spk} grain supervise-instance {root} {store}-{app}\nRestart=on-failure\nRestartSec=30\nRestartPreventExitStatus=3\n\
        NoNewPrivileges=yes\nUMask=0077\nPrivateTmp=yes\n",user=config.operator_user,prefix=config.unit_prefix))
}
fn quiescent_cgroup(text: &str) -> io::Result<Option<&str>> {
    if !text
        .lines()
        .any(|l| matches!(l, "ActiveState=inactive" | "ActiveState=failed"))
        || !text.lines().any(|l| l == "MainPID=0")
        || !text.lines().any(|l| l == "ControlPID=0")
        || !text.lines().any(|l| l == "Job=")
    {
        return Err(invalid(
            "runtime adoption refuses active unit or pending job",
        ));
    }
    let cgroup = text
        .lines()
        .find_map(|l| l.strip_prefix("ControlGroup="))
        .ok_or_else(|| invalid("unit cgroup absent"))?;
    if cgroup.is_empty() {
        Ok(None)
    } else if custody::canonical(Path::new(cgroup)) {
        Ok(Some(cgroup))
    } else {
        Err(invalid("unit cgroup path refused"))
    }
}
fn unit_quiescent(unit: &str) -> io::Result<()> {
    let text = systemctl(&[
        "show",
        unit,
        "--property=ActiveState",
        "--property=MainPID",
        "--property=ControlPID",
        "--property=ControlGroup",
        "--property=Job",
    ])?;
    if let Some(cgroup) = quiescent_cgroup(&text)? {
        let events = Path::new("/sys/fs/cgroup")
            .join(cgroup.trim_start_matches('/'))
            .join("cgroup.events");
        if !fs::read_to_string(events)?
            .lines()
            .any(|l| l == "populated 0")
        {
            return Err(invalid("runtime adoption refuses populated cgroup"));
        }
    }
    Ok(())
}
fn require_frozen_apps(record: &Adoption, apps: &BTreeSet<String>) -> io::Result<()> {
    if record.apps.iter().cloned().collect::<BTreeSet<_>>() != *apps {
        return Err(invalid(
            "Store app set changed during pending runtime adoption",
        ));
    }
    Ok(())
}

pub(super) fn check_install_pin(
    requested: Option<&str>,
    actual: &str,
    adopted: bool,
) -> io::Result<()> {
    if requested.is_some_and(|sha| sha != actual) || (adopted && requested.is_none()) {
        return Err(invalid(
            "InstallUnit runtime pin differs or is missing for an adopted Store",
        ));
    }
    Ok(())
}

fn complete_adoption(
    pending: &Adoption,
    mut persist: impl FnMut(&Adoption) -> io::Result<()>,
    mut render: impl FnMut() -> io::Result<()>,
    mut reload: impl FnMut() -> io::Result<()>,
) -> io::Result<()> {
    persist(pending)?;
    render()?;
    reload()?;
    let mut ready = pending.clone();
    ready.state = "ready".into();
    persist(&ready)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::RefCell, rc::Rc};
    fn record(store: &str, transaction: &str) -> Adoption {
        Adoption {
            protocol: RUNTIME_PROTOCOL.into(),
            store: store.into(),
            state: "pending".into(),
            admission: format!("/var/lib/mini/upgrades/{transaction}/compatible-admission.json")
                .into(),
            admission_sha256: "a".repeat(64),
            source_profile: format!("/var/lib/grains/{store}/host/grain-host.json").into(),
            source_profile_sha256: "b".repeat(64),
            apps: vec!["7".into()],
            runtime: RuntimePin {
                spk_host: "/opt/mini/new/spk-host".into(),
                spk_host_sha256: "c".repeat(64),
            },
        }
    }
    #[test]
    fn interrupted_render_or_reload_never_publishes_ready_and_same_admission_recovers() {
        for fail_render in [true, false] {
            let record = record("0123456789abcdef", "one");
            let states = Rc::new(RefCell::new(Vec::new()));
            let sink = states.clone();
            assert!(complete_adoption(
                &record,
                move |r| {
                    sink.borrow_mut().push(r.state.clone());
                    Ok(())
                },
                || if fail_render {
                    Err(invalid("render failed"))
                } else {
                    Ok(())
                },
                || Err(invalid("reload failed"))
            )
            .is_err());
            assert_eq!(*states.borrow(), ["pending"]);
            assert_eq!(
                classify_adoption(Some(&record), &record, "unused", "unused").unwrap(),
                Retry::Pending
            );
            let sink = states.clone();
            complete_adoption(
                &record,
                move |r| {
                    sink.borrow_mut().push(r.state.clone());
                    Ok(())
                },
                || Ok(()),
                || Ok(()),
            )
            .unwrap();
            assert_eq!(*states.borrow(), ["pending", "pending", "ready"]);
        }
    }
    #[test]
    fn changed_retry_and_concurrent_adoption_refuse_but_ready_retry_is_idempotent() {
        let mut old = record("0123456789abcdef", "one");
        let mut altered = old.clone();
        altered.runtime.spk_host_sha256 = "d".repeat(64);
        assert!(classify_adoption(Some(&old), &altered, "unused", "unused").is_err());
        let next = record("0123456789abcdef", "two");
        let other_store = record("fedcba9876543210", "two");
        assert!(classify_adoption(
            Some(&old),
            &other_store,
            "unused",
            &old.runtime.spk_host_sha256
        )
        .is_err());
        assert!(classify_adoption(Some(&old), &next, "unused", "unused").is_err());
        old.state = "ready".into();
        let original = record("0123456789abcdef", "one");
        assert_eq!(
            classify_adoption(Some(&old), &original, "unused", "unused").unwrap(),
            Retry::AlreadyReady
        );
        assert_eq!(
            classify_adoption(Some(&old), &next, "unused", &old.runtime.spk_host_sha256).unwrap(),
            Retry::New
        );
        assert!(classify_adoption(None, &original, "old", "different").is_err());
    }
    #[test]
    fn queued_jobs_and_uncertain_unit_state_refuse_quiescence() {
        let inactive = "ActiveState=inactive\nMainPID=0\nControlPID=0\nJob=\nControlGroup=\n";
        assert_eq!(quiescent_cgroup(inactive).unwrap(), None);
        for (old, new) in [
            ("Job=", "Job=123 start"),
            ("Job=\n", ""),
            ("MainPID=0", "MainPID=7"),
            ("ControlPID=0", "ControlPID=8"),
            ("ActiveState=inactive", "ActiveState=activating"),
            ("ControlGroup=", "ControlGroup=/system.slice/../escape"),
        ] {
            assert!(quiescent_cgroup(&inactive.replace(old, new)).is_err());
        }
        let supervisor = inactive.replace("inactive", "failed").replace(
            "ControlGroup=",
            "ControlGroup=/system.slice/mini-spk-supervisor@0123456789abcdef-7.service",
        );
        assert_eq!(
            quiescent_cgroup(&supervisor).unwrap(),
            Some("/system.slice/mini-spk-supervisor@0123456789abcdef-7.service")
        );
    }
    #[test]
    fn pending_retry_requires_exact_frozen_app_set() {
        let pending = record("0123456789abcdef", "one");
        assert!(require_frozen_apps(&pending, &BTreeSet::from(["7".into()])).is_ok());
        assert!(require_frozen_apps(&pending, &BTreeSet::from(["7".into(), "8".into()])).is_err());
        assert!(require_frozen_apps(&pending, &BTreeSet::new()).is_err());
    }
    #[test]
    fn legacy_clients_only_keep_baseline_permission_and_rendering_is_store_specific() {
        assert!(check_install_pin(None, "hash", false).is_ok());
        assert!(check_install_pin(None, "hash", true).is_err());
        assert!(check_install_pin(Some("other"), "hash", false).is_err());
        assert!(check_install_pin(Some("hash"), "hash", true).is_ok());
        let config = BrokerConfig {
            protocol: "mini-spk-broker-config-v1".into(),
            grains_root: "/var/lib/grains".into(),
            operator_user: "mini".into(),
            unit_prefix: "mini".into(),
            spk_host: "/old/spk-host".into(),
            spk_host_sha256: "a".repeat(64),
            ingest_helper: "/ingest".into(),
            volume_helper: "/volume".into(),
            app_uids: vec![1000],
        };
        let pin = record("0123456789abcdef", "one").runtime;
        let a = supervisor_text(&config, 1000, "0123456789abcdef", "7", &pin).unwrap();
        let b = supervisor_text(&config, 1000, "fedcba9876543210", "7", &pin).unwrap();
        assert!(a.contains("ExecStart=/opt/mini/new/spk-host grain supervise-instance /var/lib/grains 0123456789abcdef-7"));
        assert!(!b.contains("0123456789abcdef"));
        assert_eq!(config.spk_host, PathBuf::from("/old/spk-host"));
        for bad in ["/new/spk host", "/new/%i", "/new/$X", "/new/../other"] {
            assert!(unit_argument(Path::new(bad)).is_err());
        }
    }
}
