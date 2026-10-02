//! Explicit controller/worker manager selection. A root registration is an
//! operational host admission, not native budget or member authority. User
//! fixtures must opt in; no probe of a second manager can rescue a failed proof.
use crate::*;
use minidregg_compatible_upgrade_custody as custody;
use std::sync::OnceLock;

pub(crate) const PROTOCOL: &str = "mini-controller-manager-v1";
const REGISTRATION_ENV: &str = "MINI_GRAIN_CONTROLLER_REGISTRATION";
const CONTROLLER_ENV: &str = "MINI_GRAIN_CONTROLLER_MANAGER";
const WORKER_ENV: &str = "MINI_GRAIN_WORKER_MANAGER";
const UNIT_ENV: &str = "MINI_GRAIN_CONTROLLER_UNIT";
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub(crate) enum Manager {
    System,
    User,
}
impl Manager {
    pub(crate) fn name(self) -> &'static str {
        match self {
            Self::System => "system",
            Self::User => "user",
        }
    }
    fn flag(self) -> &'static str {
        match self {
            Self::System => "--system",
            Self::User => "--user",
        }
    }
    fn parse(value: &str) -> Result<Self> {
        match value {
            "system" => Ok(Self::System),
            "user" => Ok(Self::User),
            _ => Err("manager must be explicitly system or user".into()),
        }
    }
}
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Registration {
    protocol: String,
    task: String,
    config: PathBuf,
    manager: Manager,
    worker_manager: Manager,
    service_uid: u32,
    resident_config: Option<PathBuf>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Context {
    task: String,
    config: Option<PathBuf>,
    uid: u32,
    pub(crate) controller: Manager,
    pub(crate) worker: Manager,
    registration: Option<(PathBuf, String)>,
}
static BOUND: OnceLock<Context> = OnceLock::new();
fn variable(name: &str) -> Result<Option<String>> {
    std::env::var_os(name)
        .map(|v| v.into_string().map_err(|_| format!("{name} must be UTF-8")))
        .transpose()
}
fn unit(task: &str) -> String {
    format!("mini-grain-controller@{task}.service")
}
fn validate_registration(
    r: &Registration,
    task: &str,
    config: Option<&Path>,
    uid: u32,
) -> Result<()> {
    decimal(task, "controller task")?;
    if r.protocol != "mini-controller-registration-v1"
        || r.task != task
        || !custody::canonical(&r.config)
        || config.is_some_and(|p| p != r.config.as_path())
        || r.service_uid != uid
        || r.worker_manager != Manager::User
        || r.resident_config
            .as_ref()
            .is_some_and(|p| !custody::canonical(p))
    {
        return Err(
            "controller registration task/config/UID/worker-manager binding refused".into(),
        );
    }
    Ok(())
}
/// The producer shares the exact environment names consumed by load() and
/// lifetime_environment(). This projection launches nothing and grants no
/// native budget, grant or room authority.
fn launch_environment(r: &Registration, registration: &Path) -> Value {
    let mut env = serde_json::Map::new();
    env.insert(REGISTRATION_ENV.into(), json!(registration));
    env.insert(CONTROLLER_ENV.into(), json!(r.manager.name()));
    env.insert(WORKER_ENV.into(), json!(r.worker_manager.name()));
    env.insert(UNIT_ENV.into(), json!(unit(&r.task)));
    Value::Object(env)
}
fn projection(r: &Registration, registration: &Path, runtime: &Path) -> Value {
    json!({"protocol":"mini-controller-launch-v1","task":r.task,
        "runtime":runtime,"config":r.config,"residentConfig":r.resident_config,
        "runtimeRegistry":registration,"manager":r.manager,"workerManager":r.worker_manager,
        "serviceUid":r.service_uid,"unit":unit(&r.task),
        "environment":launch_environment(r,registration)})
}
fn require_launchers(config:&Config,controller:Manager,worker:Manager)->Result<()> {
    for spec in config.commands.iter().filter(|spec|spec.systemd_scope) {
        Runtime::prove_launcher_gate(&spec.program)?;
        require_launcher_protocol(controller,worker,&spec.program)?;
    }
    Ok(())
}
pub(crate) fn launch_client(args: &[std::ffi::OsString]) -> Result<()> {
    let [config_path, registration] = args else {
        return Err("usage: grain-runtime controller-launch CONFIG ROOT_REGISTRATION".into());
    };
    let config_path=Path::new(config_path);let registration=Path::new(registration);
    let (bytes,config)=config_migration::scope_config(config_path)?;
    if !custody::canonical(registration)
        || registration.file_name().and_then(|v|v.to_str())!=Some(format!("{}.json",config.task).as_str()) {
        return Err("launch registry must canonically name exactly TASK.json".into());
    }
    let rbytes=custody::root_bytes(registration,65_536).map_err(|e|e.to_string())?;
    let r:Registration=serde_json::from_slice(&rbytes).map_err(|e|e.to_string())?;
    validate_registration(&r,&config.task,Some(config_path),unsafe {libc::geteuid()})?;
    require_launchers(&config,r.manager,r.worker_manager)?;
    let mut result=projection(&r,registration,&std::env::current_exe().map_err(|e|e.to_string())?);
    result["configSha256"]=json!(sha256_bytes(&bytes)?);
    result["registrationSha256"]=json!(sha256_bytes(&rbytes)?);
    result["bindingSha256"]=json!(sha256_bytes(&serde_json::to_vec(&json!({"config":config,"configPath":config_path})).map_err(|e|e.to_string())?)?);
    result["transport"]=json!({"mini":config.mini,"host":config.host,
        "hostConfig":config.host_config,"hostSocket":config.host_socket});
    println!("{result}");Ok(())
}
fn fixture(
    task: &str,
    config: Option<&Path>,
    uid: u32,
    controller: Option<&str>,
    worker: Option<&str>,
    declared_unit: Option<&str>,
) -> Result<Option<Context>> {
    if controller.is_none() && worker.is_none() && declared_unit.is_none() {
        return Ok(None);
    }
    if controller != Some("user")
        || worker != Some("user")
        || declared_unit != Some(unit(task).as_str())
    {
        return Err("unregistered managed fixture requires explicit user controller, user worker, and exact canonical controller unit".into());
    }
    Ok(Some(Context {
        task: task.into(),
        config: config.map(Path::to_path_buf),
        uid,
        controller: Manager::User,
        worker: Manager::User,
        registration: None,
    }))
}
fn load(task: &str, config: Option<&Path>) -> Result<Option<Context>> {
    decimal(task, "controller task")?;
    let explicit = variable(REGISTRATION_ENV)?;
    let path = explicit
        .as_ref()
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(format!("/etc/mini/controllers/{task}.json")));
    if !custody::canonical(&path)
        || path.file_name().and_then(|n| n.to_str()) != Some(format!("{task}.json").as_str())
    {
        return Err("controller registry path must be canonical and name exactly TASK.json".into());
    }
    let uid = unsafe { libc::geteuid() };
    let controller = variable(CONTROLLER_ENV)?;
    let worker = variable(WORKER_ENV)?;
    let declared = variable(UNIT_ENV)?;
    // Unit tests construct many unscoped Runtime fixtures in one process. They
    // must not depend on an unrelated machine's production registry. Explicit
    // test selections still exercise the real strict root/fixture resolver.
    #[cfg(test)]
    if explicit.is_none() && controller.is_none() && worker.is_none() && declared.is_none() {
        return Ok(None);
    }
    match fs::symlink_metadata(&path) {
        Ok(_) => {}
        Err(e) if e.kind() == io::ErrorKind::NotFound && explicit.is_none() => {
            return fixture(
                task,
                config,
                uid,
                controller.as_deref(),
                worker.as_deref(),
                declared.as_deref(),
            )
        }
        Err(e) => return Err(format!("explicit controller registration unavailable: {e}")),
    }
    let bytes = custody::root_bytes(&path, 65536).map_err(|e| e.to_string())?;
    let r: Registration =
        serde_json::from_slice(&bytes).map_err(|e| format!("controller registration: {e}"))?;
    validate_registration(&r, task, config, uid)?;
    if controller
        .as_deref()
        .map(Manager::parse)
        .transpose()?
        .is_some_and(|m| m != r.manager)
        || worker
            .as_deref()
            .map(Manager::parse)
            .transpose()?
            .is_some_and(|m| m != r.worker_manager)
        || declared.as_deref().is_some_and(|u| u != unit(task))
    {
        return Err("controller environment contradicts root manager registration".into());
    }
    Ok(Some(Context {
        task: task.into(),
        config: Some(r.config),
        uid,
        controller: r.manager,
        worker: r.worker_manager,
        registration: Some((path, sha256_bytes(&bytes)?)),
    }))
}
/// Before migration recovery and before any managed worker launch. Unscoped
/// local runtimes may open without a manager, but cannot obtain managed proof.
pub(crate) fn initialize(config: &Config, path: &Path) -> Result<()> {
    let Some(context) = load(&config.task, Some(path))? else {
        return Ok(());
    };
    if let Some(previous) = BOUND.get() {
        if previous != &context {
            return Err("process already bound to another controller manager/config".into());
        }
    } else {
        BOUND
            .set(context)
            .map_err(|_| "controller manager initialized concurrently")?;
    }
    Ok(())
}
pub(crate) fn current(task: &str) -> Result<Context> {
    if let Some(bound) = BOUND.get() {
        if bound.task != task {
            return Err("manager operation names another bound controller".into());
        }
        let current =
            load(task, bound.config.as_deref())?.ok_or("bound manager selection disappeared")?;
        if &current != bound {
            return Err("controller manager registration/UID/config changed; restart after explicit admission required".into());
        }
        Ok(current)
    } else {
        load(task, None)?.ok_or_else(|| {
            "managed proof requires root registration or explicit user fixture selection".into()
        })
    }
}
fn command(manager: Manager, uid: u32) -> Command {
    let mut command = Command::new("/usr/bin/systemctl");
    command
        .arg(manager.flag())
        .arg("--no-pager")
        .env("LC_ALL", "C");
    match manager {
        Manager::User => {
            command
                .env("XDG_RUNTIME_DIR", format!("/run/user/{uid}"))
                .env(
                    "DBUS_SESSION_BUS_ADDRESS",
                    format!("unix:path=/run/user/{uid}/bus"),
                );
        }
        Manager::System => {
            command.env(
                "DBUS_SYSTEM_BUS_ADDRESS",
                "unix:path=/run/dbus/system_bus_socket",
            );
        }
    }
    command
}
pub(crate) fn controller_command(task: &str) -> Result<Command> {
    let context = current(task)?;
    Ok(command(context.controller, context.uid))
}
fn worker_task(unit: &str) -> Result<&str> {
    let (task, operation) = unit
        .strip_prefix("mini-grain-t")
        .and_then(|s| s.split_once("-o"))
        .ok_or("worker unit is not a canonical Mini operation")?;
    decimal(task, "worker controller task")?;
    let number = operation
        .parse::<u64>()
        .map_err(|_| "worker operation ID is invalid")?;
    if number.to_string() != operation {
        return Err("worker operation ID is not canonical".into());
    }
    Ok(task)
}
pub(crate) fn worker_command(unit: &str) -> Result<Command> {
    let context = current(worker_task(unit)?)?;
    Ok(command(context.worker, context.uid))
}
fn incarnation(text: &str, pid: u32) -> Result<String> {
    let mut fields = std::collections::BTreeMap::new();
    for line in text.lines() {
        let (k, v) = line
            .split_once('=')
            .ok_or("invalid controller incarnation property")?;
        if fields.insert(k, v).is_some() {
            return Err("duplicate controller incarnation property".into());
        }
    }
    let invocation = fields
        .get("InvocationID")
        .copied()
        .ok_or("controller InvocationID missing")?;
    if fields.get("MainPID").copied() != Some(pid.to_string().as_str())
        || fields.get("ActiveState").copied() != Some("active")
        || invocation.len() != 32
        || !invocation
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(
            "controller launch requires current active MainPID and exact systemd invocation".into(),
        );
    }
    Ok(invocation.into())
}
/// Populate the gate from a fresh native manager observation, never an inherited
/// unverified PID/InvocationID. The worker monitor binds this exact incarnation.
pub(crate) fn lifetime_environment(task: &str, target: &mut Command) -> Result<()> {
    let context = current(task)?;
    let output = command(context.controller, context.uid)
        .args([
            "show",
            "--property=MainPID,ActiveState,InvocationID",
            &unit(task),
        ])
        .output()
        .map_err(|e| format!("controller lifetime observation: {e}"))?;
    if !output.status.success() || output.stdout.len() > 16384 {
        return Err("controller lifetime observation unavailable".into());
    }
    let invocation = incarnation(
        std::str::from_utf8(&output.stdout).map_err(|e| e.to_string())?,
        std::process::id(),
    )?;
    // Revalidate root admission after the manager query as well.
    if current(task)? != context {
        return Err("controller admission changed during lifetime observation".into());
    }
    target
        .env(CONTROLLER_ENV, context.controller.name())
        .env(WORKER_ENV, context.worker.name())
        .env(UNIT_ENV, unit(task))
        .env("MINI_GRAIN_CONTROLLER_PID", std::process::id().to_string())
        .env("MINI_GRAIN_CONTROLLER_INVOCATION_ID", invocation)
        .env("XDG_RUNTIME_DIR", format!("/run/user/{}", context.uid))
        .env(
            "DBUS_SESSION_BUS_ADDRESS",
            format!("unix:path=/run/user/{}/bus", context.uid),
        );
    if let Some((path, _)) = context.registration {
        target.env(REGISTRATION_ENV, path);
    }
    Ok(())
}
pub(crate) fn gate_environment(unit: &str, action: &str, command: &mut Command) -> Result<()> {
    if action == "init" {
        lifetime_environment(worker_task(unit)?, command)?;
    }
    Ok(())
}
pub(crate) fn verify_launcher(task: &str, program: &Path) -> Result<()> {
    let context = current(task)?;
    require_launcher_protocol(context.controller,context.worker,program)
}
fn require_launcher_protocol(controller:Manager,worker:Manager,program:&Path)->Result<()> {
    if controller != worker {
        let output = Command::new(program)
            .arg("--controller-manager-protocol")
            .output()
            .map_err(|e| format!("cross-manager launcher protocol: {e}"))?;
        if !output.status.success() || output.stdout != format!("{PROTOCOL}\n").as_bytes() {
            return Err(
                "cross-manager worker requires source-owned controller lifetime protocol".into(),
            );
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    fn registration() -> Registration {
        Registration {
            protocol: "mini-controller-registration-v1".into(),
            task: "8781".into(),
            config: "/var/lib/mini/hermes/controller.json".into(),
            manager: Manager::System,
            worker_manager: Manager::User,
            service_uid: 1000,
            resident_config: None,
        }
    }
    #[test]
    fn root_contract_binds_separate_managers_and_exact_identity() {
        let mut r = registration();
        validate_registration(&r, "8781", Some(&r.config), 1000).unwrap();
        assert!(validate_registration(&r, "8782", Some(&r.config), 1000).is_err());
        assert!(validate_registration(&r, "8781", Some(Path::new("/other/config")), 1000).is_err());
        assert!(validate_registration(&r, "8781", Some(&r.config), 1001).is_err());
        r.worker_manager = Manager::System;
        assert!(validate_registration(&r, "8781", Some(&r.config), 1000).is_err());
    }
    #[test]
    fn missing_worker_manager_never_silently_reclassifies_registration() {
        let mut value = serde_json::to_value(registration()).unwrap();
        value.as_object_mut().unwrap().remove("workerManager");
        assert!(serde_json::from_value::<Registration>(value).is_err());
    }
    #[test]
    fn fixtures_are_explicit_user_only_without_manager_fallback() {
        let path = Path::new("/owned/controller.json");
        assert!(fixture("8781", Some(path), 1000, None, None, None)
            .unwrap()
            .is_none());
        assert!(fixture(
            "8781",
            Some(path),
            1000,
            Some("user"),
            Some("user"),
            Some("mini-grain-controller@8781.service")
        )
        .unwrap()
        .is_some());
        for (c, w, u) in [
            ("system", "user", "mini-grain-controller@8781.service"),
            ("user", "system", "mini-grain-controller@8781.service"),
            ("user", "user", "mini-grain-controller@8782.service"),
        ] {
            assert!(fixture("8781", Some(path), 1000, Some(c), Some(w), Some(u)).is_err());
        }
    }
    #[test]
    fn commands_choose_exact_manager_and_uid_bus() {
        let c = command(Manager::User, 123);
        assert_eq!(c.get_args().next().unwrap(), "--user");
        assert!(c.get_envs().any(|(k, v)| k == "DBUS_SESSION_BUS_ADDRESS"
            && v == Some(std::ffi::OsStr::new("unix:path=/run/user/123/bus"))));
        assert_eq!(
            command(Manager::System, 123).get_args().next().unwrap(),
            "--system"
        );
    }
    #[test]
    fn lifetime_identity_refuses_stale_pid_or_invocation() {
        let text = format!(
            "MainPID=42\nActiveState=active\nInvocationID={}\n",
            "a".repeat(32)
        );
        assert!(incarnation(&text, 42).is_ok());
        assert!(incarnation(&text, 43).is_err());
        assert!(incarnation(&text.replace("active", "inactive"), 42).is_err());
        assert!(incarnation(&text.replace(&"a".repeat(32), "absent"), 42).is_err());
        assert!(incarnation(&format!("{text}MainPID=42\n"), 42).is_err());
    }
    #[test]
    fn root_launch_projection_uses_native_consumer_environment_and_exact_identity() {
        let r=registration();let path=Path::new("/etc/mini/controllers/8781.json");
        let v=projection(&r,path,Path::new("/root/archive/grain-runtime"));
        assert_eq!(v["environment"][REGISTRATION_ENV],json!(path));
        assert_eq!(v["environment"][CONTROLLER_ENV],"system");
        assert_eq!(v["environment"][WORKER_ENV],"user");
        assert_eq!(v["environment"][UNIT_ENV],unit("8781"));
        assert!(v["environment"].get("MINI_GRAIN_REGISTRY").is_none());
        assert_eq!(v["serviceUid"],1000);assert_eq!(v["runtimeRegistry"],json!(path));
        assert_eq!(v["config"],json!(r.config));
    }
    #[test]
    fn cross_manager_probe_refuses_old_or_wrong_launcher_without_work() {
        let root=std::env::temp_dir().join(format!("manager-protocol-probe-{}",std::process::id()));
        fs::create_dir_all(&root).unwrap();let launcher=root.join("bwrap");
        fs::write(&launcher,"#!/bin/sh\nexit 64\n").unwrap();fs::set_permissions(&launcher,fs::Permissions::from_mode(0o700)).unwrap();
        assert!(require_launcher_protocol(Manager::System,Manager::User,&launcher).is_err());
        fs::write(&launcher,"#!/bin/sh\nprintf 'wrong-protocol\\n'\n").unwrap();
        assert!(require_launcher_protocol(Manager::System,Manager::User,&launcher).is_err());
        fs::write(&launcher,format!("#!/bin/sh\ntest \"$1\" = --controller-manager-protocol || exit 64\nprintf '{}\\n'\n",PROTOCOL)).unwrap();
        require_launcher_protocol(Manager::System,Manager::User,&launcher).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn complete_launch_preflight_checks_gate_and_manager_for_each_scoped_command() {
        let (root,mut rt)=crate::tests::restart_resolution_fixture("complete-launch-probe");
        let launcher=root.join("bwrap");
        fs::write(&launcher,format!("#!/bin/sh\ntest \"$1\" = --controller-manager-protocol || exit 64\nprintf '{}\\n'\n",PROTOCOL)).unwrap();
        fs::set_permissions(&launcher,fs::Permissions::from_mode(0o700)).unwrap();
        rt.config.commands=vec![serde_json::from_value(json!({"name":"hermes-acp","program":launcher,
            "args":["/agent/hermes-acp"],"reserve":"1","charge":"1","systemdScope":true})).unwrap()];
        assert!(require_launchers(&rt.config,Manager::System,Manager::User).unwrap_err().contains("launch-gate"));
        fs::write(&launcher,format!("#!/bin/sh\ncase \"$1\" in\n--launch-gate-protocol) printf 'mini-grain-launch-gate-v1\\n';;\n--controller-manager-protocol) printf '{}\\n';;\n*) exit 64;;\nesac\n",PROTOCOL)).unwrap();
        require_launchers(&rt.config,Manager::System,Manager::User).unwrap();
        fs::write(&launcher,"#!/bin/sh\nprintf 'mini-grain-launch-gate-v1\\n'\n").unwrap();
        assert!(require_launchers(&rt.config,Manager::System,Manager::User).unwrap_err().contains("controller lifetime"));
        require_launchers(&rt.config,Manager::User,Manager::User).unwrap();
        fs::remove_file(&launcher).unwrap();
        rt.config.commands[0].systemd_scope=false;
        require_launchers(&rt.config,Manager::System,Manager::User).unwrap();
        fs::remove_dir_all(root).unwrap();
    }
    #[test]
    fn worker_names_cannot_choose_unrelated_units() {
        assert_eq!(worker_task("mini-grain-t8781-o7").unwrap(), "8781");
        for name in [
            "other.service",
            "mini-grain-t8781-o07",
            "mini-grain-t8781-o7.service",
            "mini-grain-t8781-o-1",
        ] {
            assert!(worker_task(name).is_err(), "{name}");
        }
    }
}
