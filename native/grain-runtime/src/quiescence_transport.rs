//! Root-attested management routing for fresh signed quiescence reads only.
//! This does not rebind the controller, reopen ingress, drain the backend, or
//! grant a mutation route. The ordinary query verifier and original binding stay
//! in use. Local query counters/artifacts still advance through their normal path.
use crate::quiescence::{ResidentGuard, Status};
use crate::*;
use minidregg_compatible_upgrade_custody as custody;

const ADMISSION: &str = "mini-controller-query-transport-v1";
const REQUEST: &str = "mini-controller-query-transport-request-v1";

#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Pin {
    path: PathBuf,
    sha256: String,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ControllerPin {
    path: PathBuf,
    sha256: String,
    binding_sha256: String,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Store {
    storage_root: PathBuf,
    expected_seed: String,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Backend {
    process_id: u32,
    host_process_id: u32,
    instance_id: String,
    host_sha256: String,
    config_sha256: String,
}
#[derive(Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Manager {
    System,
    User,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Relay {
    unit: String,
    manager: Manager,
    service_uid: u32,
}
#[derive(Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Admission {
    protocol: String,
    controller_config: ControllerPin,
    mini: Pin,
    host: Pin,
    host_config: Pin,
    profile: Value,
    store: Store,
    public_socket: PathBuf,
    management_socket: PathBuf,
    backend: Backend,
    public_relay: Relay,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    #[serde(rename = "type")]
    kind: String,
    admission: Pin,
    resident_state: Option<PathBuf>,
}

fn hash(value: &impl Serialize) -> Result<String> {
    let value = serde_json::to_value(value).map_err(|e| e.to_string())?;
    sha256_bytes(&serde_json::to_vec(&value).map_err(|e| e.to_string())?)
}
fn hex(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
}
fn private(path: &Path, limit: usize) -> Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|e| format!("quiescence transport {}: {e}", path.display()))?;
    let meta = file.metadata().map_err(|e| e.to_string())?;
    if !meta.is_file()
        || meta.uid() != unsafe { libc::geteuid() }
        || meta.mode() & 0o077 != 0
        || meta.nlink() != 1
        || meta.len() > limit as u64
    {
        return Err("quiescence transport request/config custody refused".into());
    }
    let mut bytes = Vec::new();
    file.take(limit as u64 + 1)
        .read_to_end(&mut bytes)
        .map_err(|e| e.to_string())?;
    if bytes.len() as u64 != meta.len() {
        return Err("quiescence transport file changed while reading".into());
    }
    Ok(bytes)
}
fn canonical_number(value: &Value) -> Option<String> {
    let text = match value {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        _ => return None,
    };
    if decimal(&text, "Store identity").is_ok() {
        Some(text)
    } else {
        None
    }
}
fn coordinates(
    a: &Admission,
    config: &Config,
    path: &Path,
    binding: &Value,
    raw: &[u8],
) -> Result<()> {
    let paths = [
        &a.controller_config.path,
        &a.mini.path,
        &a.host.path,
        &a.host_config.path,
        &a.store.storage_root,
        &a.public_socket,
        &a.management_socket,
    ];
    let digests = [
        &a.controller_config.sha256,
        &a.controller_config.binding_sha256,
        &a.mini.sha256,
        &a.host.sha256,
        &a.host_config.sha256,
        &a.backend.instance_id,
        &a.backend.host_sha256,
        &a.backend.config_sha256,
    ];
    if a.protocol != ADMISSION
        || !paths.iter().all(|p| custody::canonical(p))
        || !digests.iter().all(|h| hex(h))
        || a.controller_config.path != path
        || sha256_bytes(raw)? != a.controller_config.sha256
        || hash(binding)? != a.controller_config.binding_sha256
        || *binding != json!({"config":config,"configPath":path})
    {
        // Parsed config equality below accommodates omitted default fields;
        // the raw digest remains exact, rather than normalizing operator intent.
        return Err("quiescence transport controller/admission coordinates refused".into());
    }
    let parsed: Config = serde_json::from_slice(raw).map_err(|e| e.to_string())?;
    if hash(&parsed)? != hash(config)?
        || config.mini != a.mini.path
        || config.host != a.host.path
        || config.host_config != a.host_config.path
        || config.host_socket.as_ref() != Some(&a.public_socket)
        || a.management_socket == a.public_socket
        || a.management_socket == config.control_socket
        || a.management_socket.with_extension("control") == config.control_socket
        || a.backend.process_id == 0
        || a.backend.host_process_id == 0
        || a.backend.host_sha256 != a.host.sha256
        || a.backend.config_sha256 != a.host_config.sha256
        || a.public_relay.service_uid != unsafe { libc::geteuid() }
    {
        return Err(
            "quiescence transport is not the exact original profile/public-to-management topology"
                .into(),
        );
    }
    decimal(&a.store.expected_seed, "expectedSeed")?;
    if a.public_relay.unit.len() > 256
        || !a.public_relay.unit.ends_with(".service")
        || a.public_relay.unit.starts_with('-')
        || !a
            .public_relay
            .unit
            .bytes()
            .all(|c| c.is_ascii_alphanumeric() || b"-_.@:".contains(&c))
    {
        return Err("quiescence public relay unit refused".into());
    }
    Ok(())
}
fn store_profile(a: &Admission, config: &Value, profile: &Value) -> Result<()> {
    if config["storageRoot"].as_str().map(Path::new) != Some(a.store.storage_root.as_path())
        || canonical_number(&config["expectedSeed"]).as_deref()
            != Some(a.store.expected_seed.as_str())
        || profile != &a.profile
        || profile["runtime"] != "minidregg-native"
        || profile["nativeChecked"] != true
        || canonical_number(&profile["domain"]) != canonical_number(&config["domain"])
        || canonical_number(&profile["domain"]).is_none()
        || canonical_number(&profile["semantics"]).is_none()
    {
        return Err("quiescence management route differs from admitted Store/profile".into());
    }
    Ok(())
}
fn backend_matches(a: &Admission, actual: &Value) -> Result<()> {
    if actual["format"] != "mini-operator-drain-v1"
        || actual["processId"] != a.backend.process_id
        || actual["hostProcessId"] != a.backend.host_process_id
        || actual["instanceId"] != a.backend.instance_id
        || actual["hostSha256"] != a.backend.host_sha256
        || actual["configSha256"] != a.backend.config_sha256
        || actual["phase"] != "serving"
        || actual["admissionClosed"] != false
        || actual["drained"] != false
        || !actual["requestNonce"].as_str().is_some_and(hex)
    {
        return Err(
            "quiescence management backend instance/profile is not the admitted serving process"
                .into(),
        );
    }
    Ok(())
}
fn relay_properties(text: &str) -> Result<BTreeMap<String, String>> {
    let mut fields = BTreeMap::new();
    for line in text.lines() {
        let (name, value) = line
            .split_once('=')
            .ok_or("malformed relay unit property")?;
        if fields.insert(name.to_owned(), value.to_owned()).is_some() {
            return Err("duplicate relay unit property".into());
        }
    }
    let get = |key: &str| fields.get(key).map(String::as_str);
    if get("LoadState") != Some("loaded")
        || !matches!(get("ActiveState"), Some("inactive" | "failed"))
        || get("MainPID") != Some("0")
        || get("ControlPID") != Some("0")
        || get("Job") != Some("")
        || get("TriggeredBy") != Some("")
        || get("ControlGroup").is_none()
    {
        return Err("public relay is active, queued, activatable, unknown, or not stopped".into());
    }
    if let Some(group) = get("ControlGroup").filter(|g| !g.is_empty()) {
        if !custody::canonical(Path::new(group)) {
            return Err("relay cgroup path refused".into());
        }
    }
    Ok(fields)
}
fn command_json(command: &mut Command, label: &str) -> Result<Value> {
    let output = command
        .stdin(Stdio::null())
        .output()
        .map_err(|e| format!("{label}: {e}"))?;
    if !output.status.success() || output.stdout.len() > 262_144 {
        return Err(format!("{label} unavailable or exceeds bound"));
    }
    serde_json::from_slice(&output.stdout).map_err(|e| format!("{label}: {e}"))
}

#[cfg(target_os = "linux")]
fn public_closed(path: &Path) -> Result<()> {
    let bytes = path.to_str().ok_or("public socket path UTF-8")?.as_bytes();
    let mut address: libc::sockaddr_un = unsafe { std::mem::zeroed() };
    if bytes.len() >= address.sun_path.len() || bytes.contains(&0) {
        return Err("public socket path exceeds Unix endpoint bound".into());
    }
    address.sun_family = libc::AF_UNIX as libc::sa_family_t;
    for (target, byte) in address.sun_path.iter_mut().zip(bytes) {
        *target = *byte as libc::c_char;
    }
    // A replacement listener with a full backlog must refuse, never make a
    // supposedly closed-ingress inspection block on connect indefinitely.
    let fd = unsafe {
        libc::socket(
            libc::AF_UNIX,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        )
    };
    if fd < 0 {
        return Err(format!(
            "public endpoint probe: {}",
            io::Error::last_os_error()
        ));
    }
    let result = unsafe {
        libc::connect(
            fd,
            &address as *const _ as *const libc::sockaddr,
            std::mem::size_of_val(&address) as libc::socklen_t,
        )
    };
    let error = io::Error::last_os_error();
    unsafe {
        libc::close(fd);
    }
    if result == 0 {
        return Err("configured public endpoint still accepts connections".into());
    }
    match error.kind() {
        io::ErrorKind::NotFound | io::ErrorKind::ConnectionRefused => Ok(()),
        _ => Err(format!("cannot establish closed public endpoint: {error}")),
    }
}
#[cfg(not(target_os = "linux"))]
fn public_closed(_path: &Path) -> Result<()> {
    Err("management quiescence routing requires the Linux controller supervisor".into())
}

/// Only this module can construct the token consumed by query_as_via. It is
/// useful for the signed resource-query path; mutation APIs never accept it.
pub(crate) struct AuthorizedTransport {
    pin: Pin,
    admission: Admission,
    config_sha256: String,
    before: Value,
}
impl AuthorizedTransport {
    fn load(config: &Config, path: &Path, binding: &Value, pin: Pin) -> Result<Self> {
        let raw = custody::root_bytes(&pin.path, 262_144).map_err(|e| e.to_string())?;
        if !hex(&pin.sha256) || sha256_bytes(&raw)? != pin.sha256 {
            return Err("query topology admission hash changed".into());
        }
        let admission: Admission = serde_json::from_slice(&raw).map_err(|e| e.to_string())?;
        coordinates(&admission, config, path, binding, &private(path, 262_144)?)?;
        let mut token = Self {
            pin,
            admission,
            config_sha256: hash(config)?,
            before: Value::Null,
        };
        token.before = token.recheck(config, path, binding)?;
        Ok(token)
    }
    pub(crate) fn assert_bound(&self, config: &Config, path: &Path, binding: &Value) -> Result<()> {
        if hash(config)? != self.config_sha256
            || path != self.admission.controller_config.path
            || hash(binding)? != self.admission.controller_config.binding_sha256
        {
            return Err("query-only transport token belongs to another controller binding".into());
        }
        Ok(())
    }
    pub(crate) fn socket(&self) -> &Path {
        &self.admission.management_socket
    }
    pub(crate) fn evidence(&self) -> Value {
        json!({"type":ADMISSION,"admission":self.pin,"configuredSocket":self.admission.public_socket,
            "querySocket":self.admission.management_socket,"controllerBindingSha256":self.admission.controller_config.binding_sha256,
            "host":self.admission.host,"hostConfig":self.admission.host_config,"mini":self.admission.mini,
            "store":self.admission.store,"profile":self.admission.profile,"before":self.before,"queryOnly":true})
    }
    fn recheck(&self, config: &Config, path: &Path, binding: &Value) -> Result<Value> {
        self.assert_bound(config, path, binding)?;
        let a = &self.admission;
        let raw = custody::root_bytes(&self.pin.path, 262_144).map_err(|e| e.to_string())?;
        if sha256_bytes(&raw)? != self.pin.sha256 {
            return Err("query topology admission changed during inspection".into());
        }
        coordinates(a, config, path, binding, &private(path, 262_144)?)?;
        // Root attests these existing images/config; operator ownership is not
        // promoted to root custody and file contents must remain exact.
        for pin in [&a.mini, &a.host, &a.host_config] {
            if sha256_file(&pin.path)? != pin.sha256 {
                return Err("admitted query client/Host/config bytes changed".into());
            }
        }
        let host_config: Value =
            serde_json::from_slice(&bounded_regular_file(&a.host_config.path, 4 * 1024 * 1024)?)
                .map_err(|e| e.to_string())?;
        let profile = command_json(
            Command::new(&a.mini.path)
                .arg("profile")
                .arg("--host")
                .arg(&a.host.path)
                .arg("--config")
                .arg(&a.host_config.path),
            "admitted Host profile",
        )?;
        store_profile(a, &host_config, &profile)?;
        let output = Command::new("/usr/bin/systemctl")
            .arg(match a.public_relay.manager {
                Manager::System => "--system",
                Manager::User => "--user",
            })
            .args([
                "show",
                "--property=LoadState,ActiveState,MainPID,ControlPID,Job,ControlGroup,TriggeredBy",
            ])
            .arg(&a.public_relay.unit)
            .stdin(Stdio::null())
            .output()
            .map_err(|e| e.to_string())?;
        if !output.status.success() || output.stdout.len() > 16_384 {
            return Err("public relay stop evidence unavailable".into());
        }
        let fields =
            relay_properties(std::str::from_utf8(&output.stdout).map_err(|e| e.to_string())?)?;
        let group = &fields["ControlGroup"];
        if !group.is_empty() {
            let events = fs::read_to_string(
                Path::new("/sys/fs/cgroup")
                    .join(group.trim_start_matches('/'))
                    .join("cgroup.events"),
            )
            .map_err(|e| format!("public relay cgroup: {e}"))?;
            if !events.lines().any(|l| l == "populated 0") {
                return Err("public relay cgroup is still populated".into());
            }
        }
        // Unit status is insufficient if another listener has replaced the
        // public socket. No bytes or Host operation are sent by this check.
        public_closed(&a.public_socket)?;
        let backend = command_json(
            Command::new(&a.mini.path)
                .arg("operator-status")
                .arg("--socket")
                .arg(&a.management_socket)
                .arg("--host")
                .arg(&a.host.path)
                .arg("--config")
                .arg(&a.host_config.path),
            "management operator status",
        )?;
        backend_matches(a, &backend)?;
        Ok(
            json!({"backend":backend,"publicRelay":a.public_relay,"relayProperties":fields,
            "publicEndpointClosed":true,"backendDrainProved":false}),
        )
    }
}

impl Runtime {
    pub(crate) fn inspect_quiescence_transport(&mut self, request_path: &Path) -> Result<Status> {
        let request: Request =
            serde_json::from_slice(&private(request_path, 65_536)?).map_err(|e| e.to_string())?;
        if request.kind != REQUEST {
            return Err("query transport request type refused".into());
        }
        let transport = AuthorizedTransport::load(
            &self.config,
            &self.config_path,
            &self.journal.binding,
            request.admission,
        )?;
        let guard = ResidentGuard::acquire(&self.config, request.resident_state.as_deref())?;
        let mut status = self.inspect_quiescence_locked_via(&guard, Some(&transport))?;
        let after = transport.recheck(&self.config, &self.config_path, &self.journal.binding)?;
        self.quiescence_stop_proof()?;
        guard.assert_unchanged()?;
        for observation in &mut status.observations {
            observation["transportEvidence"]["after"] = after.clone();
        }
        Ok(status)
    }
}
pub(crate) fn client(args: &[std::ffi::OsString]) -> Result<()> {
    let [socket, request] = args else {
        return Err(
            "usage: grain-runtime quiescence-transport ADMIN_SOCKET PRIVATE_REQUEST".into(),
        );
    };
    let request = Path::new(request);
    if !request.is_absolute() {
        return Err("query transport request path must be absolute".into());
    }
    let response = control::admin_call(
        Path::new(socket),
        &format!(
            "quiescence transport {}",
            request.to_str().ok_or("request path UTF-8")?
        ),
    )?;
    let result: Value = serde_json::from_str(&response).map_err(|_| response)?;
    if result["type"] != "mini-grain-quiescence-v1" {
        return Err("unexpected management quiescence response".into());
    }
    println!("{result}");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn fixture() -> (Config, Vec<u8>, Value, Admission) {
        let raw = br#"{"mini":"/owned/mini","host":"/owned/host","hostConfig":"/owned/host.json","hostSocket":"/run/mini/public.sock","controlSocket":"/owned/state/control.sock","custodyKey":"/owned/key","stateDir":"/owned/state","cwd":"/owned/work","task":"8781","subject":"7","capability":"71","queryCapability":"71","commands":[]}"#.to_vec();
        let config: Config = serde_json::from_slice(&raw).unwrap();
        let path = Path::new("/owned/controller.json");
        let binding = json!({"config":config,"configPath":path});
        let pin = |path: &str, c: &str| Pin {
            path: path.into(),
            sha256: c.repeat(64),
        };
        let a = Admission {
            protocol: ADMISSION.into(),
            controller_config: ControllerPin {
                path: path.into(),
                sha256: sha256_bytes(&raw).unwrap(),
                binding_sha256: hash(&binding).unwrap(),
            },
            mini: pin("/owned/mini", "a"),
            host: pin("/owned/host", "b"),
            host_config: pin("/owned/host.json", "c"),
            profile: json!({"runtime":"minidregg-native","nativeChecked":true,"domain":"8501","semantics":"123"}),
            store: Store {
                storage_root: "/owned/store".into(),
                expected_seed: "456".into(),
            },
            public_socket: "/run/mini/public.sock".into(),
            management_socket: "/owned/socket/private.sock".into(),
            backend: Backend {
                process_id: 100,
                host_process_id: 101,
                instance_id: "d".repeat(64),
                host_sha256: "b".repeat(64),
                config_sha256: "c".repeat(64),
            },
            public_relay: Relay {
                unit: "mini-public-ingress.service".into(),
                manager: Manager::System,
                service_uid: unsafe { libc::geteuid() },
            },
        };
        (config, raw, binding, a)
    }
    #[test]
    fn exact_old_binding_accepts_omitted_config_defaults() {
        let (config, raw, binding, a) = fixture();
        coordinates(
            &a,
            &config,
            Path::new("/owned/controller.json"),
            &binding,
            &raw,
        )
        .unwrap();
        let mut changed = config.clone();
        changed.host_socket = Some(a.management_socket.clone());
        assert!(coordinates(
            &a,
            &changed,
            Path::new("/owned/controller.json"),
            &binding,
            &raw
        )
        .is_err());
        let mut changed = binding.clone();
        changed["config"]["subject"] = json!("8");
        assert!(coordinates(
            &a,
            &config,
            Path::new("/owned/controller.json"),
            &changed,
            &raw
        )
        .is_err());
        let mut changed = raw;
        changed.push(b' ');
        assert!(coordinates(
            &a,
            &config,
            Path::new("/owned/controller.json"),
            &binding,
            &changed
        )
        .is_err());
    }
    #[test]
    fn socket_alias_traversal_and_other_uid_refuse() {
        let (config, raw, binding, a) = fixture();
        for path in [
            a.public_socket.clone(),
            config.control_socket.clone(),
            PathBuf::from("/owned/../socket"),
        ] {
            let mut changed = a.clone();
            changed.management_socket = path;
            assert!(coordinates(
                &changed,
                &config,
                Path::new("/owned/controller.json"),
                &binding,
                &raw
            )
            .is_err());
        }
        let mut changed = a;
        changed.public_relay.service_uid = unsafe { libc::geteuid() }.wrapping_add(1);
        assert!(coordinates(
            &changed,
            &config,
            Path::new("/owned/controller.json"),
            &binding,
            &raw
        )
        .is_err());
    }
    #[test]
    fn exact_store_and_full_profile_are_required() {
        let (_, _, _, a) = fixture();
        let config = json!({"storageRoot":"/owned/store","expectedSeed":456,"domain":8501});
        store_profile(&a, &config, &a.profile).unwrap();
        let mut changed = config.clone();
        changed["expectedSeed"] = json!("0456");
        assert!(store_profile(&a, &changed, &a.profile).is_err());
        let mut changed = config;
        changed["storageRoot"] = json!("/another/store");
        assert!(store_profile(&a, &changed, &a.profile).is_err());
        let mut changed = a.profile.clone();
        changed["semantics"] = json!("124");
        assert!(store_profile(
            &a,
            &json!({"storageRoot":"/owned/store","expectedSeed":456,"domain":8501}),
            &changed
        )
        .is_err());
    }
    #[test]
    fn fresh_backend_instance_cannot_be_replaced_or_drained() {
        let (_, _, _, a) = fixture();
        let status = json!({"format":"mini-operator-drain-v1","processId":100,"hostProcessId":101,"instanceId":"d".repeat(64),
            "hostSha256":"b".repeat(64),"configSha256":"c".repeat(64),"phase":"serving","admissionClosed":false,"drained":false,"requestNonce":"e".repeat(64)});
        backend_matches(&a, &status).unwrap();
        for field in [
            "processId",
            "hostProcessId",
            "instanceId",
            "hostSha256",
            "configSha256",
            "phase",
            "admissionClosed",
            "requestNonce",
        ] {
            let mut changed = status.clone();
            changed[field] = Value::Null;
            assert!(backend_matches(&a, &changed).is_err(), "{field}");
        }
    }
    #[test]
    fn relay_stop_requires_no_pid_job_or_ambiguous_properties() {
        let stopped="LoadState=loaded\nActiveState=inactive\nMainPID=0\nControlPID=0\nJob=\nControlGroup=\nTriggeredBy=\n";
        relay_properties(stopped).unwrap();
        for (from, to) in [
            ("MainPID=0", "MainPID=33"),
            ("ControlPID=0", "ControlPID=4"),
            ("Job=\n", "Job=72\n"),
            ("ActiveState=inactive", "ActiveState=active"),
            ("LoadState=loaded", "LoadState=not-found"),
            ("TriggeredBy=\n", "TriggeredBy=mini-public-ingress.socket\n"),
            ("ControlGroup=\n", "ControlGroup=/a/../b\n"),
        ] {
            assert!(relay_properties(&stopped.replace(from, to)).is_err());
        }
        assert!(relay_properties(&format!("{stopped}MainPID=0\n")).is_err());
    }
    #[test]
    fn admission_schema_refuses_hidden_mutation_or_transport_fields() {
        let (_, _, _, a) = fixture();
        let mut value = serde_json::to_value(a).unwrap();
        value["allowMutations"] = json!(true);
        assert!(serde_json::from_value::<Admission>(value).is_err());
        let bad = json!({"type":REQUEST,"admission":{"path":"/a","sha256":"b".repeat(64)},"residentState":null,"hostSocket":"/other"});
        assert!(serde_json::from_value::<Request>(bad).is_err());
    }
    #[cfg(target_os = "linux")]
    #[test]
    fn public_endpoint_check_refuses_live_listener_and_accepts_only_closed_paths() {
        let path = std::env::temp_dir().join(format!(
            "qt-{}-{}.sock",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        public_closed(&path).unwrap();
        let listener = std::os::unix::net::UnixListener::bind(&path).unwrap();
        assert!(public_closed(&path).is_err());
        drop(listener);
        public_closed(&path).unwrap();
        fs::remove_file(path).unwrap();
    }
    #[test]
    fn operator_owned_topology_never_constructs_authorized_query_token() {
        let (config, _, binding, a) = fixture();
        let path = std::env::temp_dir().join(format!(
            "query-topology-{}-{}.json",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let bytes = serde_json::to_vec(&a).unwrap();
        write_new(&path, &bytes).unwrap();
        let pin = Pin {
            path: path.clone(),
            sha256: sha256_bytes(&bytes).unwrap(),
        };
        assert!(AuthorizedTransport::load(
            &config,
            Path::new("/owned/controller.json"),
            &binding,
            pin
        )
        .is_err());
        fs::remove_file(path).unwrap();
    }
}
