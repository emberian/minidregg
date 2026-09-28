//! Durable physical custody for one Mini-authorized application generation.
//!
//! This is not an admission path. A future adapter must construct `VerifiedBegin`
//! only from the native source-owned lifecycle receiver's original-prefix
//! receipt, exact event, and current pending query. In particular, a generic
//! resource transaction or caller JSON is never enough to start an app.

use crate::agent_api_lifetime_reverse_v3::VerifiedSettlementV3;
use crate::rpc_adapter::DispatchFence;
use crate::sandbox::open_protected_directory;
use crate::spawn_gate::{self, BoundedChild, SpawnSpec};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::process::{Output, Stdio};
use std::time::{Duration, Instant};
use std::time::{SystemTime, UNIX_EPOCH};

const VERSION: u32 = 1;
const MAX_RECORD_BYTES: u64 = 16 * 1024;
// Native Host's max frame includes its op34 byte; this file captures only payload.
const MAX_DISPATCH_PERMIT_BYTES: usize = 12_102_759;

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn canonical_native_id(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn deserialize_operation_id<'de, D>(deserializer: D) -> Result<String, D::Error>
where
    D: serde::Deserializer<'de>,
{
    use serde::de::Error as _;
    let value = serde_json::Value::deserialize(deserializer)?;
    let text = match value {
        serde_json::Value::String(value) => value,
        serde_json::Value::Number(value) => value
            .as_u64()
            .ok_or_else(|| D::Error::custom("historical operation ID is not unsigned integer"))?
            .to_string(),
        _ => return Err(D::Error::custom("operation ID is not decimal")),
    };
    if !canonical_native_id(&text) {
        return Err(D::Error::custom("operation ID is not canonical decimal"));
    }
    Ok(text)
}

fn hex64(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}

/// Opaque physical identity derived from a future native verified BEGIN.
/// No public constructor exists: private socket input cannot mint one.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub(crate) struct VerifiedBegin {
    pub app: u64,
    pub generation: u64,
    #[serde(deserialize_with = "deserialize_operation_id")]
    pub operation_id: String,
    pub transaction_id: String,
    pub event_id: String,
    pub package_sha256: String,
    pub image_identity: String,
    pub process_identity: String,
    pub unit: String,
}

impl VerifiedBegin {
    fn validate(&self) -> io::Result<()> {
        if self.generation == 0
            || !canonical_native_id(&self.operation_id)
            || !canonical_native_id(&self.transaction_id)
            || !canonical_native_id(&self.event_id)
            || !hex64(&self.package_sha256)
            || self.image_identity.is_empty()
            || self.image_identity.len() > 512
            || self.process_identity.is_empty()
            || self.process_identity.len() > 512
            || self.unit != format!("mini-spk-a{}-g{}.service", self.app, self.generation)
        {
            return Err(invalid("invalid verified BEGIN identity"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub enum Phase {
    Armed,
    LaunchRequested,
    Entered,
    Running,
    Fenced,
    Stopped,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct Record {
    version: u32,
    identity: VerifiedBegin,
    pub phase: Phase,
    pub child_pid: Option<u32>,
    #[serde(default)]
    invocation_id: Option<String>,
    #[serde(default)]
    control_group: Option<String>,
    /// One physical RPC may be in flight. Historical operation tombstones live
    /// in separate exact files so a long-lived app does not grow this record.
    #[serde(default)]
    dispatch_in_flight: Option<DispatchIdentity>,
}

impl Record {
    pub fn app(&self) -> u64 {
        self.identity.app
    }
    pub fn generation(&self) -> u64 {
        self.identity.generation
    }
    pub fn unit(&self) -> &str {
        &self.identity.unit
    }
    pub fn transaction_id(&self) -> &str {
        &self.identity.transaction_id
    }
    pub fn event_id(&self) -> &str {
        &self.identity.event_id
    }
    pub(crate) fn operation_id(&self) -> &str {
        &self.identity.operation_id
    }
    pub(crate) fn invocation_id(&self) -> Option<&str> {
        self.invocation_id.as_deref()
    }
    pub(crate) fn control_group(&self) -> Option<&str> {
        self.control_group.as_deref()
    }
    pub(crate) fn image_identity(&self) -> &str {
        &self.identity.image_identity
    }
    /// The resident hostd calls this from its own unit before a physical
    /// request. A durable Running row alone is not proof the same manager
    /// invocation and app cgroup are still present.
    pub(crate) fn verify_running_instance(&self) -> io::Result<()> {
        if self.phase != Phase::Running {
            return Err(invalid("app journal is not Running"));
        }
        let current = UnitInstance::current(self.unit())?;
        if self.invocation_id.as_deref() != Some(current.invocation_id.as_str())
            || self.control_group.as_deref() != Some(current.control_group.as_str())
        {
            return Err(invalid("resident app unit invocation drift"));
        }
        let manager = systemd_show(self.unit())?;
        if property(&manager, "ActiveState")? != "active"
            || !matches!(property(&manager, "Job")?, "0" | "")
            || property(&manager, "MainPID")?
                .parse::<u32>()
                .map_err(|_| invalid("invalid app unit MainPID"))?
                != std::process::id()
        {
            return Err(invalid("resident is not active unit MainPID and job-free"));
        }
        let child = self
            .child_pid
            .ok_or_else(|| invalid("Running app PID absent"))?;
        let child_group = fs::read_to_string(format!("/proc/{child}/cgroup"))?;
        if !child_group
            .lines()
            .any(|line| line == format!("0::{}", current.control_group))
        {
            return Err(invalid("app child left exact unit cgroup"));
        }
        Ok(())
    }

    fn validate(&self) -> io::Result<()> {
        if self.version != VERSION {
            return Err(invalid("unsupported hostd journal version"));
        }
        self.identity.validate()?;
        if matches!(self.phase, Phase::Armed | Phase::LaunchRequested) && self.child_pid.is_some() {
            return Err(invalid("prelaunch journal has child PID"));
        }
        if matches!(self.phase, Phase::Armed | Phase::LaunchRequested)
            && (self.invocation_id.is_some() || self.control_group.is_some())
        {
            return Err(invalid("prelaunch journal has unit instance"));
        }
        if self.invocation_id.is_some() != self.control_group.is_some() {
            return Err(invalid("partial unit instance identity"));
        }
        if let (Some(invocation_id), Some(control_group)) =
            (&self.invocation_id, &self.control_group)
        {
            UnitInstance {
                invocation_id: invocation_id.clone(),
                control_group: control_group.clone(),
            }
            .validate(&self.identity.unit)?;
        }
        if matches!(self.phase, Phase::Entered | Phase::Running) && self.invocation_id.is_none() {
            return Err(invalid("entered journal lacks unit instance"));
        }
        if self.phase == Phase::Running && self.child_pid.is_none() {
            return Err(invalid("running journal lacks child PID"));
        }
        if let Some(dispatch) = &self.dispatch_in_flight {
            dispatch.validate()?;
            if !matches!(self.phase, Phase::Running | Phase::Fenced | Phase::Stopped) {
                return Err(invalid("dispatch custody before app Running"));
            }
            if dispatch.app != self.identity.app
                || dispatch.app_generation != self.identity.generation
                || self.invocation_id.as_deref() != Some(dispatch.invocation_id.as_str())
            {
                return Err(invalid(
                    "dispatch custody differs from app execution instance",
                ));
            }
        }
        Ok(())
    }
}

/// Inert coordinates projected from one fresh Mini op34 committed permit and
/// compared against the captured HTTP request. Constructing this data grants
/// no authority; no public socket constructs a journal dispatch from it.
/// The permit bytes themselves remain in a separate private capture; this
/// durable row records their SHA-256 and the exact request/process coordinate.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct DispatchIdentity {
    pub permit_sha256: String,
    pub request_digest: String,
    pub app: u64,
    pub app_generation: u64,
    pub invocation_id: String,
    pub operation_id: String,
    pub session_resource: String,
    pub session_generation: String,
    pub dispatch_transaction: String,
    pub dispatch_event: String,
}

fn canonical_decimal(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && (value == "0" || !value.starts_with('0'))
        && value.bytes().all(|byte| byte.is_ascii_digit())
}

fn canonical_digest_decimal(value: &str) -> bool {
    const MAX_256: &str =
        "115792089237316195423570985008687907853269984665640564039457584007913129639935";
    canonical_decimal(value)
        && (value.len() < MAX_256.len() || (value.len() == MAX_256.len() && value <= MAX_256))
}

impl DispatchIdentity {
    fn validate(&self) -> io::Result<()> {
        if !hex64(&self.permit_sha256)
            || !canonical_digest_decimal(&self.request_digest)
            || !canonical_digest_decimal(&self.dispatch_transaction)
            || !canonical_digest_decimal(&self.dispatch_event)
            || self.app_generation == 0
            || self.invocation_id.len() != 32
            || !self.invocation_id.bytes().all(|b| b.is_ascii_hexdigit())
            || !canonical_decimal(&self.operation_id)
            || !canonical_decimal(&self.session_resource)
            || !canonical_decimal(&self.session_generation)
        {
            return Err(invalid("invalid exact dispatch custody identity"));
        }
        Ok(())
    }

    /// Physical one-shot coordinate, independent of the request payload. Two
    /// sessions may send byte-identical requests; one session may not reuse an
    /// operation ID with changed bytes or a different native receipt.
    fn operation_key(&self) -> String {
        let mut hash = Sha256::new();
        hash.update(b"DREGG/SPK-HOST/DISPATCH-OPERATION/v1");
        hash.update(self.app.to_le_bytes());
        hash.update(self.app_generation.to_le_bytes());
        for part in [
            self.session_resource.as_bytes(),
            self.session_generation.as_bytes(),
            self.operation_id.as_bytes(),
        ] {
            hash.update((part.len() as u16).to_le_bytes());
            hash.update(part);
        }
        format!("{:x}", hash.finalize())
    }
}

fn validate_committed_permit(identity: &DispatchIdentity, permit: &[u8]) -> io::Result<()> {
    if permit.is_empty()
        || permit.len() > MAX_DISPATCH_PERMIT_BYTES
        || format!("{:x}", Sha256::digest(permit)) != identity.permit_sha256
    {
        return Err(invalid("committed permit byte count or SHA-256 mismatch"));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
enum DispatchPhase {
    DeliveryRequested,
    Delivered,
    Uncertain,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
struct DispatchTombstone {
    version: u32,
    identity: DispatchIdentity,
    phase: DispatchPhase,
}

/// Captured by the exact systemd unit process, not caller JSON. Systemd's
/// InvocationID and the unified cgroup path identify this execution instance.
#[derive(Clone, Debug, Eq, PartialEq)]
struct UnitInstance {
    invocation_id: String,
    control_group: String,
}

fn systemd_show(unit: &str) -> io::Result<String> {
    let output = bounded_systemctl(
        &[
            "--system",
            "show",
            unit,
            "--property=Id,LoadState,ActiveState,MainPID,Job,InvocationID,ControlGroup",
            "--no-pager",
        ],
        Duration::from_secs(5),
    )?;
    if !output.status.success() || output.stdout.len() > 8192 {
        return Err(invalid("exact systemd unit inspection unavailable"));
    }
    String::from_utf8(output.stdout).map_err(|_| invalid("systemd unit inspection is not UTF-8"))
}

fn bounded_systemctl(args: &[&str], deadline: Duration) -> io::Result<Output> {
    let mut child = Command::new("/usr/bin/systemctl")
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()?;
    let end = Instant::now() + deadline;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => return child.wait_with_output(),
            Ok(None) => {}
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(error);
            }
        }
        if Instant::now() >= end {
            let _ = child.kill();
            let _ = child.wait();
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "systemd manager response uncertain",
            ));
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

fn property<'a>(output: &'a str, name: &str) -> io::Result<&'a str> {
    let prefix = format!("{name}=");
    let mut matches = output.lines().filter_map(|line| line.strip_prefix(&prefix));
    let value = matches
        .next()
        .ok_or_else(|| invalid("missing systemd property"))?;
    if matches.next().is_some() {
        return Err(invalid("duplicate systemd property"));
    }
    Ok(value)
}

impl UnitInstance {
    fn current(unit: &str) -> io::Result<Self> {
        let invocation_id =
            std::env::var("INVOCATION_ID").map_err(|_| invalid("missing systemd InvocationID"))?;
        let cgroup = fs::read_to_string("/proc/self/cgroup")?;
        let control_group = cgroup
            .lines()
            .find_map(|line| line.strip_prefix("0::"))
            .ok_or_else(|| invalid("missing unified systemd cgroup"))?
            .to_owned();
        let instance = Self {
            invocation_id,
            control_group,
        };
        instance.validate(unit)?;
        let manager = systemd_show(unit)?;
        if property(&manager, "Id")? != unit
            || property(&manager, "LoadState")? != "loaded"
            || property(&manager, "InvocationID")? != instance.invocation_id
            || property(&manager, "ControlGroup")? != instance.control_group
            || property(&manager, "MainPID")?
                .parse::<u32>()
                .map_err(|_| invalid("invalid systemd MainPID"))?
                != std::process::id()
        {
            return Err(invalid(
                "unit process identity differs from systemd manager",
            ));
        }
        Ok(instance)
    }

    fn validate(&self, unit: &str) -> io::Result<()> {
        if self.invocation_id.len() != 32
            || !self
                .invocation_id
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || !self.control_group.starts_with('/')
            || !self.control_group.ends_with(&format!("/{unit}"))
            || self.control_group.contains("//")
            || self
                .control_group
                .split('/')
                .any(|component| component == "..")
        {
            return Err(invalid("unit InvocationID or cgroup identity refused"));
        }
        Ok(())
    }
}

/// Source of truth is an exact systemd manager and cgroup inspection. A unit
/// omitted by `list-units`, a mismatched invocation or an unknown cgroup is
/// never interpreted as empty. The production inspector queries the manager
/// and the previously pinned cgroup path; uncertainty retains Fenced.
#[derive(Clone, Debug)]
pub(crate) struct UnitStopAudit {
    unit: String,
    invocation_id: Option<String>,
    control_group: Option<String>,
    unit_loaded: bool,
    inactive: bool,
    main_pid: u32,
    queued_job: bool,
    exact_cgroup_empty: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PriorUnitState {
    RunningExact,
    StoppedExact,
    Uncertain,
}

/// Exact running incarnation selected by the source-inspected STOP witness.
/// Its prior completion receipt remains in the lifecycle attempt; this local
/// identity is rechecked under the journal lock before any manager action.
#[derive(Clone)]
#[allow(dead_code)] // STOP caller is gated on the source-inspected prior-running witness.
pub(crate) struct StopIdentity {
    pub app: u64,
    pub generation: u64,
    pub unit: String,
    pub image_identity: String,
    pub invocation_id: String,
    pub control_group: String,
}

#[allow(dead_code)]
impl StopIdentity {
    fn matches(&self, record: &Record) -> io::Result<()> {
        if record.app() != self.app
            || record.generation() != self.generation
            || record.unit() != self.unit
            || record.image_identity() != self.image_identity
            || record.invocation_id() != Some(self.invocation_id.as_str())
            || record.control_group() != Some(self.control_group.as_str())
            || !matches!(record.phase, Phase::Running | Phase::Fenced)
        {
            return Err(invalid(
                "STOP source running incarnation differs from journal",
            ));
        }
        Ok(())
    }
}

impl UnitStopAudit {
    /// Project only the checked post-stop manager/cgroup observations into
    /// Mini's typed StopAudit authoring input. The digest commits this exact
    /// operator-attested summary; Mini still relies on the distinct physical
    /// custodian signature and does not inspect systemd itself.
    pub(crate) fn source_stop_audit(
        &self,
        expected: &StopIdentity,
    ) -> io::Result<serde_json::Value> {
        let hex_bytes = |bytes: &[u8]| -> String {
            let mut out = String::with_capacity(bytes.len() * 2);
            for byte in bytes {
                use std::fmt::Write as _;
                write!(out, "{byte:02x}").expect("writing hex into String");
            }
            out
        };
        if self.unit != expected.unit
            || self.invocation_id.is_some()
            || self.control_group.as_deref() != Some(expected.control_group.as_str())
            || !self.unit_loaded
            || !self.inactive
            || self.main_pid != 0
            || self.queued_job
            || !self.exact_cgroup_empty
        {
            return Err(invalid(
                "STOP physical audit differs from selected prior incarnation",
            ));
        }
        let projection = serde_json::json!({
            "unit": hex_bytes(expected.unit.as_bytes()),
            "recordedInvocationId": hex_bytes(expected.invocation_id.as_bytes()),
            "recordedControlGroup": hex_bytes(expected.control_group.as_bytes()),
            "managerLoaded": self.unit_loaded,
            "managerInactive": self.inactive,
            "managerMainPid": self.main_pid.to_string(),
            "managerJobEmpty": !self.queued_job,
            "managerInvocationCleared": self.invocation_id.is_none(),
            "cgroupUnpopulated": self.exact_cgroup_empty,
        });
        let mut hasher = Sha256::new();
        hasher.update(b"DREGG/SPK-STOP-POST-AUDIT/v1");
        // The report codec contains only StopAudit fields. Bind the operator's
        // full source-selected incarnation in the attested digest as well.
        hasher.update(serde_json::to_vec(&serde_json::json!({
            "app": expected.app.to_string(),
            "generation": expected.generation.to_string(),
            "imageIdentity": hex_bytes(expected.image_identity.as_bytes()),
            "audit": projection,
        }))?);
        let digest = hasher.finalize();
        let mut decimal_digits = vec![0u8];
        for byte in digest.iter().rev() {
            let mut carry = u16::from(*byte);
            for digit in &mut decimal_digits {
                let value = u16::from(*digit) * 256 + carry;
                *digit = (value % 10) as u8;
                carry = value / 10;
            }
            while carry > 0 {
                decimal_digits.push((carry % 10) as u8);
                carry /= 10;
            }
        }
        let observation_digest: String = decimal_digits
            .iter()
            .rev()
            .map(|digit| char::from(b'0' + *digit))
            .collect();
        let mut projection = projection;
        projection["observationDigest"] = serde_json::Value::String(observation_digest);
        Ok(projection)
    }

    fn before_stop(record: &Record) -> io::Result<()> {
        let output = systemd_show(record.unit())?;
        if property(&output, "Id")? != record.unit() || property(&output, "LoadState")? != "loaded"
        {
            return Err(invalid("exact unit absent before stop"));
        }
        if let Some(expected) = record.invocation_id.as_deref() {
            if property(&output, "InvocationID")? != expected
                || property(&output, "ControlGroup")?
                    != record.control_group.as_deref().unwrap_or("")
            {
                return Err(invalid("unit invocation/cgroup drift before stop"));
            }
        }
        Ok(())
    }

    fn inspect(record: &Record) -> io::Result<Self> {
        let output = systemd_show(record.unit())?;
        let unit = property(&output, "Id")?.to_owned();
        let invocation = property(&output, "InvocationID")?;
        let manager_group = property(&output, "ControlGroup")?;
        let recorded_group = record.control_group.as_deref();
        if !manager_group.is_empty() && Some(manager_group) != recorded_group {
            return Err(invalid("systemd cgroup differs from durable unit instance"));
        }
        let exact_cgroup_empty = if let Some(group) = recorded_group {
            let path = Path::new("/sys/fs/cgroup").join(group.trim_start_matches('/'));
            match fs::read_to_string(path.join("cgroup.events")) {
                Ok(events) => {
                    let populated = events
                        .lines()
                        .find_map(|line| line.strip_prefix("populated "))
                        .ok_or_else(|| invalid("missing cgroup populated field"))?;
                    populated == "0"
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => true,
                Err(error) => return Err(error),
            }
        } else {
            manager_group.is_empty()
        };
        let main_pid = property(&output, "MainPID")?
            .parse::<u32>()
            .map_err(|_| invalid("invalid systemd MainPID"))?;
        Ok(Self {
            unit,
            invocation_id: (!invocation.is_empty()).then(|| invocation.to_owned()),
            control_group: recorded_group.map(str::to_owned),
            unit_loaded: property(&output, "LoadState")? == "loaded",
            inactive: property(&output, "ActiveState")? == "inactive",
            main_pid,
            queued_job: !matches!(property(&output, "Job")?, "0" | ""),
            exact_cgroup_empty,
        })
    }

    fn prove(&self, record: &Record) -> io::Result<()> {
        if self.unit != record.identity.unit
            || self.invocation_id.is_some()
            || self.control_group != record.control_group
            || !self.unit_loaded
            || !self.inactive
            || self.main_pid != 0
            || self.queued_job
            || !self.exact_cgroup_empty
        {
            return Err(invalid("exact unit invocation/cgroup stop not proven"));
        }
        Ok(())
    }
}

/// One operation's protected directory, not a shared mutable app name. Its
/// `record.json` is never removed: a fenced operation cannot be rearmed.
#[derive(Clone, Debug)]
pub struct Journal {
    directory: PathBuf,
}

trait ChildHandle {
    fn pid(&self) -> u32;
    fn abort_under_lock(&mut self) -> io::Result<()>;
}

impl ChildHandle for BoundedChild {
    fn pid(&self) -> u32 {
        self.pid()
    }
    fn abort_under_lock(&mut self) -> io::Result<()> {
        if self.kill_and_reap() {
            Ok(())
        } else {
            Err(invalid(
                "spawned child could not be reaped under journal lock",
            ))
        }
    }
}

// The mutators are intentionally unreachable from the public binary until
// native verified BEGIN admission is wired. Keep the physical state machine
// separately testable without exposing an operator-minted launch command.
#[allow(dead_code)]
impl Journal {
    /// Read-only classification of a retained START incarnation after the
    /// supervisor restarts. This cannot recover fd3, authorize HTTP, or
    /// change the Mini lifecycle phase. An exact stopped audit requires a
    /// separate source STOP transition before another START.
    pub(crate) fn audit_prior_running(
        &self,
        expected: &VerifiedBegin,
    ) -> io::Result<PriorUnitState> {
        self.with_lock(|this| {
            let record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("prior START journal absent"))?;
            if &record.identity != expected
                || !matches!(
                    record.phase,
                    Phase::Running | Phase::Fenced | Phase::Stopped
                )
            {
                return Err(invalid("prior START identity differs from retained claim"));
            }
            if UnitStopAudit::inspect(&record)
                .and_then(|audit| audit.prove(&record))
                .is_ok()
            {
                return Ok(PriorUnitState::StoppedExact);
            }
            let manager = systemd_show(record.unit())?;
            let child_group = record
                .child_pid
                .and_then(|pid| fs::read_to_string(format!("/proc/{pid}/cgroup")).ok());
            let running = property(&manager, "Id")? == record.unit()
                && property(&manager, "LoadState")? == "loaded"
                && property(&manager, "ActiveState")? == "active"
                && matches!(property(&manager, "Job")?, "0" | "")
                && property(&manager, "InvocationID")? == record.invocation_id().unwrap_or("")
                && property(&manager, "ControlGroup")? == record.control_group().unwrap_or("")
                && property(&manager, "MainPID")?
                    .parse::<u32>()
                    .ok()
                    .is_some_and(|pid| pid > 0)
                && child_group.as_deref().is_some_and(|group| {
                    group
                        .lines()
                        .any(|line| line == format!("0::{}", record.control_group().unwrap_or("")))
                });
            Ok(if running {
                PriorUnitState::RunningExact
            } else {
                PriorUnitState::Uncertain
            })
        })
    }
    /// Refuse a misinstalled resident unit before consuming a one-shot Mini
    /// claim. The spawn path repeats this check under the journal lock.
    pub(crate) fn preflight_current_unit(unit: &str) -> io::Result<()> {
        UnitInstance::current(unit).map(|_| ())
    }

    pub fn open(directory: &Path) -> io::Result<Self> {
        let uid = unsafe { libc::geteuid() };
        if !directory.is_absolute() {
            return Err(invalid("hostd state directory must be absolute"));
        }
        // Only root or this operator may own a path component. In particular,
        // an app UID cannot rename an otherwise private journal ancestor.
        for ancestor in directory.ancestors() {
            let meta = fs::symlink_metadata(ancestor)?;
            if !meta.is_dir()
                || meta.file_type().is_symlink()
                || (meta.uid() != 0 && meta.uid() != uid)
                || meta.permissions().mode() & 0o022 != 0
            {
                return Err(invalid(
                    "hostd journal ancestor is task-writable or symlinked",
                ));
            }
        }
        let protected = File::from(open_protected_directory(directory, u32::MAX, false)?);
        let metadata = fs::metadata(directory)?;
        if metadata.uid() != uid
            || metadata.permissions().mode() & 0o777 != 0o700
            || metadata.dev() != protected.metadata()?.dev()
            || metadata.ino() != protected.metadata()?.ino()
        {
            return Err(invalid(
                "hostd state directory must be owner-private and pinned",
            ));
        }
        Ok(Self {
            directory: directory.to_owned(),
        })
    }

    pub(crate) fn directory(&self) -> &Path {
        &self.directory
    }

    fn with_lock<T>(&self, f: impl FnOnce(&Self) -> io::Result<T>) -> io::Result<T> {
        let path = self.directory.join(".lock");
        let lock = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path)?;
        let metadata = lock.metadata()?;
        if !metadata.is_file()
            || metadata.nlink() != 1
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.permissions().mode() & 0o777 != 0o600
        {
            return Err(invalid("hostd lock identity or mode drift"));
        }
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_EX) } != 0 {
            return Err(io::Error::last_os_error());
        }
        // The lock remains held throughout the callback, including the spawn
        // handshake. Fence cannot linearize between gate entry and child spawn.
        let result = f(self);
        if unsafe { libc::flock(lock.as_raw_fd(), libc::LOCK_UN) } != 0 {
            return Err(io::Error::last_os_error());
        }
        result
    }

    fn read_unlocked(&self) -> io::Result<Option<Record>> {
        let path = self.directory.join("record.json");
        let file = match OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(path)
        {
            Ok(file) => file,
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => return Err(error),
        };
        let metadata = file.metadata()?;
        if !metadata.is_file()
            || metadata.nlink() != 1
            || metadata.uid() != unsafe { libc::geteuid() }
            || metadata.permissions().mode() & 0o777 != 0o600
            || metadata.len() > MAX_RECORD_BYTES
        {
            return Err(invalid("hostd record identity, mode or length drift"));
        }
        let mut bytes = Vec::new();
        file.take(MAX_RECORD_BYTES + 1).read_to_end(&mut bytes)?;
        if bytes.len() as u64 > MAX_RECORD_BYTES {
            return Err(invalid("hostd record grew"));
        }
        let record: Record = serde_json::from_slice(&bytes)?;
        record.validate()?;
        Ok(Some(record))
    }

    fn write_unlocked(&self, record: &Record) -> io::Result<()> {
        record.validate()?;
        let bytes = serde_json::to_vec(record)?;
        if bytes.len() as u64 > MAX_RECORD_BYTES {
            return Err(invalid("hostd record too large"));
        }
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| invalid("clock before epoch"))?
            .as_nanos();
        let temporary = self
            .directory
            .join(format!(".record-{}-{nonce}.tmp", std::process::id()));
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&temporary)?;
        let result = (|| {
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temporary, self.directory.join("record.json"))?;
            File::open(&self.directory)?.sync_all()
        })();
        if result.is_err() {
            let _ = fs::remove_file(&temporary);
        }
        result
    }

    fn dispatch_path(&self, identity: &DispatchIdentity) -> PathBuf {
        self.directory
            .join(format!("dispatch-op-{}.json", identity.operation_key()))
    }

    fn active_dispatch_path(&self) -> PathBuf {
        self.directory.join("dispatch-active.json")
    }

    /// Reserve a physical operation number before native authoring. The
    /// counter is advanced and fsynced under the app lock, so a crash may
    /// skip a number but can never reuse one after it was handed to a caller.
    pub(crate) fn allocate_dispatch_operation(&self) -> io::Result<String> {
        self.with_lock(|this| {
            let path = this.directory.join("dispatch-next-id");
            let next = match OpenOptions::new()
                .read(true)
                .custom_flags(libc::O_NOFOLLOW)
                .open(&path)
            {
                Ok(mut file) => {
                    let meta = file.metadata()?;
                    if !meta.is_file()
                        || meta.nlink() != 1
                        || meta.uid() != unsafe { libc::geteuid() }
                        || meta.permissions().mode() & 0o777 != 0o600
                        || meta.len() > 21
                    {
                        return Err(invalid("dispatch operation counter identity drift"));
                    }
                    let mut bytes = String::new();
                    file.read_to_string(&mut bytes)?;
                    let value = bytes
                        .strip_suffix('\n')
                        .ok_or_else(|| invalid("dispatch operation counter framing"))?;
                    if !canonical_decimal(value) {
                        return Err(invalid("dispatch operation counter is noncanonical"));
                    }
                    value
                        .parse::<u64>()
                        .map_err(|_| invalid("dispatch operation counter overflow"))?
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => {
                    // Losing an established counter must not rearm old IDs.
                    for entry in fs::read_dir(&this.directory)? {
                        let name = entry?.file_name();
                        let name = name.to_string_lossy();
                        if name.starts_with("dispatch-op-")
                            || name.starts_with("dispatch-id-")
                            || name.starts_with("dispatch-permit-")
                            || name == "dispatch-active.json"
                        {
                            return Err(invalid("dispatch operation counter missing after use"));
                        }
                    }
                    1
                }
                Err(error) => return Err(error),
            };
            if next == 0 {
                return Err(invalid("dispatch operation counter is zero"));
            }
            let following = next
                .checked_add(1)
                .ok_or_else(|| invalid("dispatch operation counter exhausted"))?;
            // This per-ID marker survives even if a later counter rename is
            // interrupted. An absent or rolled-back counter then fails closed.
            let allocated = this.directory.join(format!("dispatch-id-{next}"));
            let mut marker = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW)
                .open(&allocated)?;
            writeln!(marker, "{next}")?;
            marker.sync_all()?;
            File::open(&this.directory)?.sync_all()?;
            let nonce = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .map_err(|_| invalid("clock before epoch"))?
                .as_nanos();
            let temporary = this
                .directory
                .join(format!(".dispatch-next-{}-{nonce}.tmp", std::process::id()));
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW)
                .open(&temporary)?;
            let result = (|| {
                writeln!(file, "{following}")?;
                file.sync_all()?;
                fs::rename(&temporary, &path)?;
                File::open(&this.directory)?.sync_all()
            })();
            if result.is_err() {
                let _ = fs::remove_file(&temporary);
            }
            result?;
            Ok(next.to_string())
        })
    }

    fn dispatch_permit_path(&self, identity: &DispatchIdentity) -> PathBuf {
        self.directory
            .join(format!("dispatch-permit-{}.bin", identity.operation_key()))
    }

    fn capture_dispatch_permit_unlocked(
        &self,
        identity: &DispatchIdentity,
        permit: &[u8],
    ) -> io::Result<()> {
        validate_committed_permit(identity, permit)?;
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(self.dispatch_permit_path(identity))?;
        file.write_all(permit)?;
        file.sync_all()?;
        File::open(&self.directory)?.sync_all()
    }

    fn verify_dispatch_permit_unlocked(&self, identity: &DispatchIdentity) -> io::Result<()> {
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(self.dispatch_permit_path(identity))?;
        let meta = file.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() == 0
            || meta.len() > MAX_DISPATCH_PERMIT_BYTES as u64
        {
            return Err(invalid("captured committed permit identity or size drift"));
        }
        let mut hash = Sha256::new();
        let mut reader = file;
        let mut buffer = [0u8; 64 * 1024];
        loop {
            let count = reader.read(&mut buffer)?;
            if count == 0 {
                break;
            }
            hash.update(&buffer[..count]);
        }
        if format!("{:x}", hash.finalize()) != identity.permit_sha256 {
            return Err(invalid("captured committed permit SHA-256 drift"));
        }
        Ok(())
    }

    fn create_active_dispatch_unlocked(&self, identity: &DispatchIdentity) -> io::Result<()> {
        let bytes = serde_json::to_vec(identity)?;
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(self.active_dispatch_path())?;
        file.write_all(&bytes)?;
        file.sync_all()?;
        File::open(&self.directory)?.sync_all()
    }

    fn read_active_dispatch_unlocked(&self) -> io::Result<DispatchIdentity> {
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(self.active_dispatch_path())?;
        let meta = file.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() > 1024
        {
            return Err(invalid("active dispatch marker identity drift"));
        }
        let mut bytes = Vec::new();
        file.take(1025).read_to_end(&mut bytes)?;
        if bytes.len() > 1024 {
            return Err(invalid("active dispatch marker grew"));
        }
        let identity: DispatchIdentity = serde_json::from_slice(&bytes)?;
        identity.validate()?;
        Ok(identity)
    }

    fn clear_active_dispatch_unlocked(&self, identity: &DispatchIdentity) -> io::Result<()> {
        if &self.read_active_dispatch_unlocked()? != identity {
            return Err(invalid("active dispatch marker coordinate drift"));
        }
        fs::remove_file(self.active_dispatch_path())?;
        File::open(&self.directory)?.sync_all()
    }

    fn read_dispatch_unlocked(&self, identity: &DispatchIdentity) -> io::Result<DispatchTombstone> {
        identity.validate()?;
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(self.dispatch_path(identity))?;
        let meta = file.metadata()?;
        if !meta.is_file()
            || meta.nlink() != 1
            || meta.uid() != unsafe { libc::geteuid() }
            || meta.permissions().mode() & 0o777 != 0o600
            || meta.len() > 2048
        {
            return Err(invalid("dispatch tombstone identity or size drift"));
        }
        let mut bytes = Vec::new();
        file.take(2049).read_to_end(&mut bytes)?;
        if bytes.len() > 2048 {
            return Err(invalid("dispatch tombstone grew"));
        }
        let tombstone: DispatchTombstone = serde_json::from_slice(&bytes)?;
        if tombstone.version != VERSION || tombstone.identity != *identity {
            return Err(invalid("dispatch tombstone coordinate drift"));
        }
        Ok(tombstone)
    }

    fn write_dispatch_unlocked(
        &self,
        tombstone: &DispatchTombstone,
        initial: bool,
    ) -> io::Result<()> {
        tombstone.identity.validate()?;
        if tombstone.version != VERSION {
            return Err(invalid("dispatch tombstone version drift"));
        }
        let bytes = serde_json::to_vec(tombstone)?;
        if bytes.len() > 2048 {
            return Err(invalid("dispatch tombstone exceeds bound"));
        }
        let path = self.dispatch_path(&tombstone.identity);
        if initial {
            let mut file = OpenOptions::new()
                .write(true)
                .create_new(true)
                .mode(0o600)
                .custom_flags(libc::O_NOFOLLOW)
                .open(path)?;
            file.write_all(&bytes)?;
            file.sync_all()?;
            return File::open(&self.directory)?.sync_all();
        }
        let old = self.read_dispatch_unlocked(&tombstone.identity)?;
        if !matches!(
            (old.phase, tombstone.phase),
            (DispatchPhase::DeliveryRequested, DispatchPhase::Delivered)
                | (DispatchPhase::DeliveryRequested, DispatchPhase::Uncertain)
                | (DispatchPhase::Uncertain, DispatchPhase::Delivered)
        ) {
            return Err(invalid("dispatch tombstone transition refused"));
        }
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| invalid("clock before epoch"))?
            .as_nanos();
        let temporary = self
            .directory
            .join(format!(".dispatch-{}-{nonce}.tmp", std::process::id()));
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .custom_flags(libc::O_NOFOLLOW)
            .open(&temporary)?;
        let result = (|| {
            file.write_all(&bytes)?;
            file.sync_all()?;
            fs::rename(&temporary, path)?;
            File::open(&self.directory)?.sync_all()
        })();
        if result.is_err() {
            let _ = fs::remove_file(&temporary);
        }
        result
    }

    /// Durable one-shot transition before invoking fd3. The caller must have
    /// captured and checked the exact fresh native permit, but this journal
    /// never interprets that authority. Creating the terminally unique file
    /// first means a crash during the following record fsync cannot rearm it.
    pub(crate) fn request_dispatch(
        &self,
        identity: DispatchIdentity,
        committed_permit: &[u8],
    ) -> io::Result<()> {
        identity.validate()?;
        validate_committed_permit(&identity, committed_permit)?;
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase != Phase::Running || record.dispatch_in_flight.is_some() {
                return Err(invalid("app is not ready for one physical dispatch"));
            }
            if identity.app != record.identity.app
                || identity.app_generation != record.identity.generation
                || record.invocation_id.as_deref() != Some(identity.invocation_id.as_str())
            {
                return Err(invalid("physical dispatch app execution identity drift"));
            }
            match fs::symlink_metadata(this.active_dispatch_path()) {
                Ok(_) => return Err(invalid("prior physical dispatch still needs audit")),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
            match fs::symlink_metadata(this.dispatch_path(&identity)) {
                Ok(_) => return Err(invalid("exact physical request already attempted")),
                Err(error) if error.kind() == io::ErrorKind::NotFound => {}
                Err(error) => return Err(error),
            }
            // This marker is fsynced first. If any later file or record write
            // fails, an operator must audit it before unrelated requests run.
            this.create_active_dispatch_unlocked(&identity)?;
            this.capture_dispatch_permit_unlocked(&identity, committed_permit)?;
            let tombstone = DispatchTombstone {
                version: VERSION,
                identity: identity.clone(),
                phase: DispatchPhase::DeliveryRequested,
            };
            this.write_dispatch_unlocked(&tombstone, true)?;
            record.dispatch_in_flight = Some(identity);
            this.write_unlocked(&record)
        })
    }

    /// Complete only while the same app generation is still Running. Failure
    /// or a concurrent fence retains the operation as uncertain; no caller
    /// may submit it again. This lock is *not* held over the app RPC wait.
    pub(crate) fn finish_dispatch(
        &self,
        identity: &DispatchIdentity,
        delivered: bool,
    ) -> io::Result<()> {
        identity.validate()?;
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.dispatch_in_flight.as_ref() != Some(identity) {
                return Err(invalid("dispatch completion identity drift"));
            }
            if this.read_active_dispatch_unlocked()? != *identity {
                return Err(invalid("active dispatch completion marker drift"));
            }
            this.verify_dispatch_permit_unlocked(identity)?;
            let phase = if delivered && record.phase == Phase::Running {
                DispatchPhase::Delivered
            } else {
                DispatchPhase::Uncertain
            };
            this.write_dispatch_unlocked(
                &DispatchTombstone {
                    version: VERSION,
                    identity: identity.clone(),
                    phase,
                },
                false,
            )?;
            if phase == DispatchPhase::Delivered {
                record.dispatch_in_flight = None;
                this.write_unlocked(&record)?;
                this.clear_active_dispatch_unlocked(identity)?;
                Ok(())
            } else {
                Err(invalid("physical dispatch result uncertain or app fenced"))
            }
        })
    }

    /// Finish an exact response already proven settled by the controller's
    /// read-only native settlement inspection. This is idempotent across a
    /// crash between the Delivered tombstone, record, and active-marker fsyncs.
    /// It cannot establish settlement by itself or authorize another send.
    pub(crate) fn finish_dispatch_recovered(
        &self,
        identity: &DispatchIdentity,
        settlement: &VerifiedSettlementV3,
    ) -> io::Result<()> {
        identity.validate()?;
        if settlement.committed_receipt().transaction_id != identity.dispatch_transaction
            || settlement.committed_receipt().event_id != identity.dispatch_event
        {
            return Err(invalid(
                "recovered settlement receipt differs from dispatch identity",
            ));
        }
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase != Phase::Running
                || record.identity.app != identity.app
                || record.identity.generation != identity.app_generation
                || record.invocation_id.as_deref() != Some(identity.invocation_id.as_str())
            {
                return Err(invalid("recovered dispatch app incarnation drift"));
            }
            this.verify_dispatch_permit_unlocked(identity)?;
            let tombstone = this.read_dispatch_unlocked(identity)?;
            if tombstone.phase != DispatchPhase::DeliveryRequested
                && tombstone.phase != DispatchPhase::Delivered
                && tombstone.phase != DispatchPhase::Uncertain
            {
                return Err(invalid("recovered dispatch tombstone is not deliverable"));
            }
            if tombstone.phase == DispatchPhase::Uncertain {
                // A worker-release fence may already have freed the shared
                // slot after a lost settle ACK. A separately verified native
                // settlement can promote only this exact terminal tombstone;
                // another participant's active slot is left untouched.
                let same_active = record.dispatch_in_flight.as_ref() == Some(identity);
                if same_active && this.read_active_dispatch_unlocked()? != *identity {
                    return Err(invalid("recovered uncertain active marker drift"));
                }
                this.write_dispatch_unlocked(
                    &DispatchTombstone {
                        version: VERSION,
                        identity: identity.clone(),
                        phase: DispatchPhase::Delivered,
                    },
                    false,
                )?;
                if same_active {
                    record.dispatch_in_flight = None;
                    this.write_unlocked(&record)?;
                    this.clear_active_dispatch_unlocked(identity)?;
                }
                return Ok(());
            }
            if tombstone.phase == DispatchPhase::Delivered {
                if let Some(other) = record.dispatch_in_flight.as_ref() {
                    if other != identity {
                        if this.read_active_dispatch_unlocked()? != *other {
                            return Err(invalid("other active dispatch marker drift"));
                        }
                        return Ok(());
                    }
                }
            }
            if record
                .dispatch_in_flight
                .as_ref()
                .is_some_and(|active| active != identity)
            {
                return Err(invalid("another dispatch owns the shared app slot"));
            }
            let active = match fs::symlink_metadata(this.active_dispatch_path()) {
                Ok(_) => {
                    if this.read_active_dispatch_unlocked()? != *identity {
                        return Err(invalid("recovered active dispatch identity drift"));
                    }
                    true
                }
                Err(error) if error.kind() == io::ErrorKind::NotFound => false,
                Err(error) => return Err(error),
            };
            if tombstone.phase == DispatchPhase::DeliveryRequested {
                if !active || record.dispatch_in_flight.as_ref() != Some(identity) {
                    return Err(invalid("recovered requested dispatch lacks active custody"));
                }
                this.write_dispatch_unlocked(
                    &DispatchTombstone {
                        version: VERSION,
                        identity: identity.clone(),
                        phase: DispatchPhase::Delivered,
                    },
                    false,
                )?;
            } else if !active && record.dispatch_in_flight.as_ref() == Some(identity) {
                return Err(invalid(
                    "delivered dispatch lost active marker before record release",
                ));
            }
            if record.dispatch_in_flight.as_ref() == Some(identity) {
                record.dispatch_in_flight = None;
                this.write_unlocked(&record)?;
            }
            if active {
                this.clear_active_dispatch_unlocked(identity)?;
            }
            Ok(())
        })
    }

    /// Release only the shared RPC slot after the worker has stopped holding
    /// this exact command. The app-side effect is still uncertain: its
    /// operation tombstone remains terminal and must never be dispatched
    /// again. A missing/mismatched worker fence or a concurrently fenced app
    /// keeps the global slot held for audit.
    pub(crate) fn finish_dispatch_uncertain_released(
        &self,
        identity: &DispatchIdentity,
        worker_fence: DispatchFence,
    ) -> io::Result<()> {
        identity.validate()?;
        if !worker_fence.matches_and_consume(identity) {
            return Err(invalid("RPC worker release identity drift"));
        }
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase != Phase::Running
                || record.dispatch_in_flight.as_ref() != Some(identity)
                || identity.app != record.identity.app
                || identity.app_generation != record.identity.generation
                || record.invocation_id.as_deref() != Some(identity.invocation_id.as_str())
            {
                return Err(invalid("RPC worker release app execution identity drift"));
            }
            if this.read_active_dispatch_unlocked()? != *identity {
                return Err(invalid("RPC worker release active marker drift"));
            }
            this.verify_dispatch_permit_unlocked(identity)?;
            match this.read_dispatch_unlocked(identity)?.phase {
                DispatchPhase::DeliveryRequested => {
                    this.write_dispatch_unlocked(
                        &DispatchTombstone {
                            version: VERSION,
                            identity: identity.clone(),
                            phase: DispatchPhase::Uncertain,
                        },
                        false,
                    )?;
                }
                DispatchPhase::Uncertain => {}
                DispatchPhase::Delivered => {
                    return Err(invalid("delivered operation cannot release as uncertain"));
                }
            }
            // Clearing the record before the active marker is deliberate.
            // A crash at either step leaves the marker and blocks new work.
            record.dispatch_in_flight = None;
            this.write_unlocked(&record)?;
            this.clear_active_dispatch_unlocked(identity)
        })
    }

    pub fn read(&self) -> io::Result<Option<Record>> {
        self.with_lock(Self::read_unlocked)
    }

    pub(crate) fn arm(&self, begin: VerifiedBegin) -> io::Result<Record> {
        begin.validate()?;
        self.with_lock(|this| {
            if let Some(existing) = this.read_unlocked()? {
                if existing.identity == begin {
                    return Ok(existing);
                }
                return Err(invalid("conflicting BEGIN for durable operation"));
            }
            let record = Record {
                version: VERSION,
                identity: begin,
                phase: Phase::Armed,
                child_pid: None,
                invocation_id: None,
                control_group: None,
                dispatch_in_flight: None,
            };
            this.write_unlocked(&record)?;
            Ok(record)
        })
    }

    pub(crate) fn request_launch(&self, begin: &VerifiedBegin) -> io::Result<()> {
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if &record.identity != begin || record.phase != Phase::Armed {
                return Err(invalid("launch is not armed for this BEGIN"));
            }
            record.phase = Phase::LaunchRequested;
            this.write_unlocked(&record)
        })
    }

    /// Called as the exact service ExecStart, not as an out-of-unit preflight.
    /// The bounded fork/exec handshake occurs under the same lock as the
    /// Entered and Running fsyncs. On a Running write failure, the direct child
    /// is killed and reaped before releasing the lock. The journal remains
    /// uncertain and never grants an automatic retry.
    pub(crate) fn enter_and_spawn(
        &self,
        begin: &VerifiedBegin,
        spec: &SpawnSpec,
    ) -> io::Result<BoundedChild> {
        let instance = UnitInstance::current(&begin.unit)?;
        self.enter_and_spawn_with(
            begin,
            &instance,
            || spawn_gate::spawn_bounded(spec),
            Self::write_unlocked,
        )
    }

    fn enter_and_spawn_with<H: ChildHandle>(
        &self,
        begin: &VerifiedBegin,
        instance: &UnitInstance,
        spawn: impl FnOnce() -> io::Result<H>,
        persist_running: impl FnOnce(&Self, &Record) -> io::Result<()>,
    ) -> io::Result<H> {
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if &record.identity != begin || record.phase != Phase::LaunchRequested {
                return Err(invalid("late or duplicate unit ExecStart refused"));
            }
            instance.validate(&begin.unit)?;
            record.phase = Phase::Entered;
            record.invocation_id = Some(instance.invocation_id.clone());
            record.control_group = Some(instance.control_group.clone());
            this.write_unlocked(&record)?;
            let mut child = spawn()?;
            let pid = child.pid();
            if pid == 0 {
                child.abort_under_lock()?;
                return Err(invalid("spawn returned invalid PID"));
            }
            record.phase = Phase::Running;
            record.child_pid = Some(pid);
            if let Err(error) = persist_running(this, &record) {
                child.abort_under_lock()?;
                return Err(error);
            }
            Ok(child)
        })
    }

    /// Tombstone first; only then call the unit manager. An uncertain manager
    /// response retains Fenced and requires another exact-unit audit.
    pub(crate) fn fence_and_stop(
        &self,
        stop: impl FnOnce(&str) -> io::Result<()>,
        inspect: impl FnOnce(&Record) -> io::Result<UnitStopAudit>,
    ) -> io::Result<()> {
        let fenced_record = self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase == Phase::Stopped {
                return Ok(None);
            }
            // The fsynced active marker and DeliveryRequested tombstone already
            // preserve uncertainty. Do not make physical stop depend on an
            // additional tombstone rewrite that could fail before unit kill.
            record.phase = Phase::Fenced;
            this.write_unlocked(&record)?;
            Ok(Some(record))
        })?;
        let Some(fenced_record) = fenced_record else {
            return Ok(());
        };
        stop(&fenced_record.identity.unit)?;
        inspect(&fenced_record)?.prove(&fenced_record)?;
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing BEGIN"))?;
            if record.phase != Phase::Fenced
                || record.identity != fenced_record.identity
                || record.invocation_id != fenced_record.invocation_id
                || record.control_group != fenced_record.control_group
                || record.child_pid != fenced_record.child_pid
            {
                return Err(invalid("fence identity changed during stop"));
            }
            record.phase = Phase::Stopped;
            record.child_pid = None;
            this.write_unlocked(&record)
        })
    }

    /// Production stop path. The durable tombstone precedes the systemd stop;
    /// a missing/mismatched unit or manager failure retains Fenced.
    pub(crate) fn fence_and_stop_manager(&self) -> io::Result<()> {
        self.fence_and_stop(
            |unit| {
                let record = self
                    .read()?
                    .ok_or_else(|| invalid("missing fenced record"))?;
                // A prior stop may have succeeded just before the Stopped
                // record fsync failed. Systemd then clears InvocationID. A
                // complete exact post-stop audit permits this idempotent retry.
                if UnitStopAudit::inspect(&record)
                    .and_then(|audit| audit.prove(&record))
                    .is_ok()
                {
                    return Ok(());
                }
                UnitStopAudit::before_stop(&record)?;
                let output =
                    bounded_systemctl(&["--system", "stop", unit], Duration::from_secs(10))?;
                if output.status.success() {
                    Ok(())
                } else {
                    Err(invalid("exact systemd stop failed"))
                }
            },
            UnitStopAudit::inspect,
        )
    }

    /// Source-bound STOP uses the exact retained running incarnation and a
    /// root volume recheck while holding the journal lock. Fenced is durable
    /// before systemd stop; a crash after the manager acts can only resume by
    /// auditing that same unit, never by a second Mini claim.
    pub(crate) fn fence_and_stop_manager_checked(
        &self,
        expected: &StopIdentity,
        verify_volume: impl Fn() -> io::Result<()>,
    ) -> io::Result<UnitStopAudit> {
        self.fence_and_stop_checked_with(
            expected,
            verify_volume,
            UnitStopAudit::before_stop,
            |unit| {
                let output =
                    bounded_systemctl(&["--system", "stop", unit], Duration::from_secs(10))?;
                if output.status.success() {
                    Ok(())
                } else {
                    Err(invalid("exact systemd stop failed"))
                }
            },
            UnitStopAudit::inspect,
        )
    }

    /// Resume only an already-fsynced Fenced STOP for the same source-selected
    /// incarnation. A historical receipt or marker can never fence Running.
    pub(crate) fn resume_fenced_stop_manager_checked(
        &self,
        expected: &StopIdentity,
        verify_volume: impl Fn() -> io::Result<()>,
    ) -> io::Result<UnitStopAudit> {
        self.fence_and_stop_checked_with_mode(
            expected,
            verify_volume,
            true,
            UnitStopAudit::before_stop,
            |unit| {
                let output =
                    bounded_systemctl(&["--system", "stop", unit], Duration::from_secs(10))?;
                if output.status.success() {
                    Ok(())
                } else {
                    Err(invalid("exact fenced systemd stop failed"))
                }
            },
            UnitStopAudit::inspect,
        )
    }

    /// Read-only audit after a completed fence. This cannot enter Fenced or
    /// issue another manager command; it is solely for finishing the original
    /// signed STOP report after a process crash.
    pub(crate) fn audit_stopped_manager_checked(
        &self,
        expected: &StopIdentity,
        verify_volume: impl Fn() -> io::Result<()>,
    ) -> io::Result<UnitStopAudit> {
        self.audit_stopped_checked_with(expected, verify_volume, UnitStopAudit::inspect)
    }

    fn audit_stopped_checked_with(
        &self,
        expected: &StopIdentity,
        verify_volume: impl Fn() -> io::Result<()>,
        inspect: impl Fn(&Record) -> io::Result<UnitStopAudit>,
    ) -> io::Result<UnitStopAudit> {
        self.with_lock(|this| {
            let record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing stopped STOP journal"))?;
            if record.phase != Phase::Stopped
                || record.app() != expected.app
                || record.generation() != expected.generation
                || record.unit() != expected.unit
                || record.image_identity() != expected.image_identity
                || record.invocation_id() != Some(expected.invocation_id.as_str())
                || record.control_group() != Some(expected.control_group.as_str())
            {
                return Err(invalid("stopped journal differs from source incarnation"));
            }
            verify_volume()?;
            let audit = inspect(&record)?;
            audit.prove(&record)?;
            Ok(audit)
        })
    }

    fn fence_and_stop_checked_with(
        &self,
        expected: &StopIdentity,
        verify_volume: impl Fn() -> io::Result<()>,
        before_stop: impl Fn(&Record) -> io::Result<()>,
        stop: impl Fn(&str) -> io::Result<()>,
        inspect: impl Fn(&Record) -> io::Result<UnitStopAudit>,
    ) -> io::Result<UnitStopAudit> {
        self.fence_and_stop_checked_with_mode(
            expected,
            verify_volume,
            false,
            before_stop,
            stop,
            inspect,
        )
    }

    fn fence_and_stop_checked_with_mode(
        &self,
        expected: &StopIdentity,
        verify_volume: impl Fn() -> io::Result<()>,
        require_fenced: bool,
        before_stop: impl Fn(&Record) -> io::Result<()>,
        stop: impl Fn(&str) -> io::Result<()>,
        inspect: impl Fn(&Record) -> io::Result<UnitStopAudit>,
    ) -> io::Result<UnitStopAudit> {
        self.with_lock(|this| {
            let mut record = this
                .read_unlocked()?
                .ok_or_else(|| invalid("missing running STOP journal"))?;
            expected.matches(&record)?;
            verify_volume()?;
            if require_fenced && record.phase != Phase::Fenced {
                return Err(invalid("STOP recovery requires fsynced Fenced journal"));
            }
            if !matches!(record.phase, Phase::Running | Phase::Fenced) {
                return Err(invalid("STOP requires Running or Fenced journal"));
            }
            if record.phase == Phase::Running {
                before_stop(&record)?;
                record.phase = Phase::Fenced;
                this.write_unlocked(&record)?;
            }
            // On recovery, a prior stop may have succeeded before the final
            // fsync. A complete exact post-stop audit retires Fenced without
            // another manager command. Otherwise verify the same incarnation
            // again, then invoke the manager while retaining the lock.
            if let Ok(audit) = inspect(&record) {
                if audit.prove(&record).is_ok() {
                    record.phase = Phase::Stopped;
                    record.child_pid = None;
                    this.write_unlocked(&record)?;
                    return Ok(audit);
                }
            }
            verify_volume()?;
            before_stop(&record)?;
            stop(record.unit())?;
            let audit = inspect(&record)?;
            audit.prove(&record)?;
            record.phase = Phase::Stopped;
            record.child_pid = None;
            this.write_unlocked(&record)?;
            Ok(audit)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::agent_api_server::write_agent_delivery_marker;
    use crate::rpc_adapter::RpcDriver;
    use minidregg_spk_rpc::{Header, WebResponse, WebResult};
    use std::os::unix::fs::DirBuilderExt;
    use std::os::unix::net::UnixStream;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, Barrier};
    use std::thread;

    struct MockChild {
        pid: u32,
        aborted: Arc<AtomicBool>,
    }
    impl ChildHandle for MockChild {
        fn pid(&self) -> u32 {
            self.pid
        }
        fn abort_under_lock(&mut self) -> io::Result<()> {
            self.aborted.store(true, Ordering::SeqCst);
            Ok(())
        }
    }
    fn child(pid: u32) -> MockChild {
        MockChild {
            pid,
            aborted: Arc::new(AtomicBool::new(false)),
        }
    }

    fn scratch() -> PathBuf {
        let runtime = std::env::var("XDG_RUNTIME_DIR").expect("Linux user runtime dir");
        let path = Path::new(&runtime).join(format!(
            "mini-spk-hostd-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        path
    }

    fn begin() -> VerifiedBegin {
        VerifiedBegin {
            app: 91,
            generation: 2,
            operation_id: "7".into(),
            transaction_id: "123".into(),
            event_id: "456".into(),
            package_sha256: "c".repeat(64),
            image_identity: "image".into(),
            process_identity: "unit-generation-2".into(),
            unit: "mini-spk-a91-g2.service".into(),
        }
    }

    #[test]
    fn physical_journal_retains_full_native_operation_id_and_reads_historical_number() {
        let mut source = begin();
        source.operation_id =
            "115792089237316195423570985008687907853269984665640564039457584007913129639935".into();
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        journal.arm(source.clone()).unwrap();
        let saved = Journal::open(&path).unwrap().read().unwrap().unwrap();
        assert_eq!(saved.identity.operation_id, source.operation_id);
        fs::remove_dir_all(path).unwrap();

        let mut historical = serde_json::to_value(begin()).unwrap();
        historical["operation_id"] = serde_json::json!(7);
        let parsed: VerifiedBegin = serde_json::from_value(historical).unwrap();
        assert_eq!(parsed.operation_id, "7");
        let mut aliased = serde_json::to_value(begin()).unwrap();
        aliased["operation_id"] = serde_json::json!("07");
        assert!(serde_json::from_value::<VerifiedBegin>(aliased).is_err());
    }

    fn instance() -> UnitInstance {
        UnitInstance {
            invocation_id: "f".repeat(32),
            control_group: "/user.slice/mini-spk-a91-g2.service".into(),
        }
    }

    fn dispatch_identity(digit: char) -> DispatchIdentity {
        DispatchIdentity {
            permit_sha256: format!("{:x}", Sha256::digest(committed_permit())),
            request_digest: if digit == '0' {
                "0".into()
            } else {
                digit.to_string().repeat(64)
            },
            app: 91,
            app_generation: 2,
            invocation_id: "f".repeat(32),
            operation_id: "0".into(),
            session_resource: "6208".into(),
            session_generation: "0".into(),
            dispatch_transaction: "2".repeat(64),
            dispatch_event: "3".repeat(64),
        }
    }

    fn committed_permit() -> &'static [u8] {
        b"private exact committed op34 permit fixture"
    }

    fn running_journal() -> (PathBuf, Journal, VerifiedBegin) {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let begin = begin();
        journal.arm(begin.clone()).unwrap();
        journal.request_launch(&begin).unwrap();
        journal
            .enter_and_spawn_with(
                &begin,
                &instance(),
                || Ok(child(123)),
                Journal::write_unlocked,
            )
            .unwrap();
        (path, journal, begin)
    }

    #[test]
    fn dispatch_operation_ids_are_fsynced_and_never_reused_after_reopen() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        assert_eq!(journal.allocate_dispatch_operation().unwrap(), "1");
        assert_eq!(
            fs::read_to_string(path.join("dispatch-next-id")).unwrap(),
            "2\n"
        );
        assert_eq!(
            fs::read_to_string(path.join("dispatch-id-1")).unwrap(),
            "1\n"
        );
        drop(journal);
        let reopened = Journal::open(&path).unwrap();
        assert_eq!(reopened.allocate_dispatch_operation().unwrap(), "2");
        assert_eq!(
            fs::read_to_string(path.join("dispatch-next-id")).unwrap(),
            "3\n"
        );
        fs::remove_file(path.join("dispatch-next-id")).unwrap();
        assert!(reopened.allocate_dispatch_operation().is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn dispatch_delivered_is_one_shot_and_next_distinct_request_can_run() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('1');
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        assert_eq!(
            fs::read(journal.dispatch_permit_path(&first)).unwrap(),
            committed_permit()
        );
        assert_eq!(
            journal.read_dispatch_unlocked(&first).unwrap().phase,
            DispatchPhase::DeliveryRequested
        );
        journal.finish_dispatch(&first, true).unwrap();
        assert_eq!(
            journal.read_dispatch_unlocked(&first).unwrap().phase,
            DispatchPhase::Delivered
        );
        assert!(journal
            .read()
            .unwrap()
            .unwrap()
            .dispatch_in_flight
            .is_none());
        assert!(!journal.active_dispatch_path().exists());
        assert!(journal.request_dispatch(first, committed_permit()).is_err());
        assert!(!journal.active_dispatch_path().exists());
        // A real op34 permit contains the unique request coordinate. This
        // fixture changes its exact bytes when it changes the request digest.
        let second_permit = b"private exact committed op34 permit fixture two";
        let mut second = dispatch_identity('2');
        second.operation_id = "1".into();
        second.permit_sha256 = format!("{:x}", Sha256::digest(second_permit));
        journal
            .request_dispatch(second.clone(), second_permit)
            .unwrap();
        assert!(journal.finish_dispatch(&second, false).is_err());
        assert_eq!(
            journal.read_dispatch_unlocked(&second).unwrap().phase,
            DispatchPhase::Uncertain
        );
        assert!(journal
            .request_dispatch(dispatch_identity('3'), committed_permit())
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn recovered_delivered_dispatch_releases_exact_slot_and_is_idempotent() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('1');
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        let reopened = Journal::open(&path).unwrap();
        let settled = VerifiedSettlementV3::test_only();
        assert!(reopened
            .finish_dispatch_recovered(&first, &VerifiedSettlementV3::test_only_wrong_receipt())
            .is_err());
        assert!(reopened.active_dispatch_path().exists());
        reopened
            .finish_dispatch_recovered(&first, &settled)
            .unwrap();
        reopened
            .finish_dispatch_recovered(&first, &settled)
            .unwrap();
        assert_eq!(
            reopened.read_dispatch_unlocked(&first).unwrap().phase,
            DispatchPhase::Delivered
        );
        assert!(!reopened.active_dispatch_path().exists());
        let mut wrong = first.clone();
        wrong.app_generation += 1;
        assert!(reopened
            .finish_dispatch_recovered(&wrong, &settled)
            .is_err());
        assert!(reopened
            .request_dispatch(first, committed_permit())
            .is_err());
        let mut second = dispatch_identity('2');
        second.operation_id = "1".into();
        reopened
            .request_dispatch(second.clone(), committed_permit())
            .unwrap();
        reopened.finish_dispatch(&second, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn verified_settlement_reconciles_uncertain_a_without_clearing_b() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('1');
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        journal
            .finish_dispatch_uncertain_released(
                &first,
                DispatchFence::test_worker_released_for(first.clone()),
            )
            .unwrap();
        let mut second = dispatch_identity('2');
        second.operation_id = "1".into();
        journal
            .request_dispatch(second.clone(), committed_permit())
            .unwrap();
        journal
            .finish_dispatch_recovered(&first, &VerifiedSettlementV3::test_only())
            .unwrap();
        journal
            .finish_dispatch_recovered(&first, &VerifiedSettlementV3::test_only())
            .unwrap();
        assert_eq!(
            journal.read_dispatch_unlocked(&first).unwrap().phase,
            DispatchPhase::Delivered
        );
        assert_eq!(journal.read_active_dispatch_unlocked().unwrap(), second);
        journal.finish_dispatch(&second, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn recovered_delivered_cleans_crash_between_tombstone_and_active_marker() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('1');
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        journal
            .write_dispatch_unlocked(
                &DispatchTombstone {
                    version: VERSION,
                    identity: first.clone(),
                    phase: DispatchPhase::Delivered,
                },
                false,
            )
            .unwrap();
        assert!(journal.active_dispatch_path().exists());
        journal
            .finish_dispatch_recovered(&first, &VerifiedSettlementV3::test_only())
            .unwrap();
        assert!(!journal.active_dispatch_path().exists());
        assert!(journal
            .read()
            .unwrap()
            .unwrap()
            .dispatch_in_flight
            .is_none());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn worker_release_keeps_uncertain_operation_terminal_but_allows_other_session() {
        let (path, journal, _) = running_journal();
        let cancelled = dispatch_identity('1');
        journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .unwrap();
        let released = DispatchFence::test_worker_released_for(cancelled.clone());
        journal
            .finish_dispatch_uncertain_released(&cancelled, released)
            .unwrap();
        assert_eq!(
            journal.read_dispatch_unlocked(&cancelled).unwrap().phase,
            DispatchPhase::Uncertain
        );
        assert!(!journal.active_dispatch_path().exists());
        assert!(journal
            .read()
            .unwrap()
            .unwrap()
            .dispatch_in_flight
            .is_none());
        assert!(journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .is_err());

        let mut other = dispatch_identity('2');
        other.session_resource = "6209".into();
        journal
            .request_dispatch(other.clone(), committed_permit())
            .unwrap();
        journal.finish_dispatch(&other, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn proven_no_enqueue_releases_slot_without_rearming_operation() {
        let (path, journal, _) = running_journal();
        let cancelled = dispatch_identity('9');
        journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .unwrap();
        let no_enqueue = DispatchFence::test_no_enqueue_for(cancelled.clone());
        journal
            .finish_dispatch_uncertain_released(&cancelled, no_enqueue)
            .unwrap();
        assert_eq!(
            journal.read_dispatch_unlocked(&cancelled).unwrap().phase,
            DispatchPhase::Uncertain
        );
        assert!(journal
            .request_dispatch(cancelled, committed_permit())
            .is_err());
        let mut other = dispatch_identity('1');
        other.session_resource = "6209".into();
        journal
            .request_dispatch(other.clone(), committed_permit())
            .unwrap();
        journal.finish_dispatch(&other, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn real_prequeue_guard_releases_only_its_unqueued_operation() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('9');
        let mut second = dispatch_identity('1');
        second.session_resource = "6209".into();
        let (supervisor, _app) = UnixStream::pair().unwrap();
        let mut driver = RpcDriver::from_connected_stream(91, 2, supervisor).unwrap();

        let wrong_guard = driver.prepare_cancellable(first.clone()).unwrap();
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        assert!(journal
            .finish_dispatch_uncertain_released(&second, wrong_guard.abort_no_enqueue())
            .is_err());
        assert!(journal.active_dispatch_path().exists());

        let guard = driver.prepare_cancellable(first.clone()).unwrap();
        let client_dir = path.join("agent-client-op-9");
        fs::create_dir(&client_dir).unwrap();
        let marker = client_dir.join("delivery-requested.json");
        let native_marker = path.join("native-agent-dispatch-active.json");
        fs::write(&native_marker, b"retained native attempt").unwrap();
        fs::write(&marker, b"prior marker").unwrap();
        assert!(
            write_agent_delivery_marker(guard, &journal, &first, &client_dir, || Ok(())).is_err()
        );
        assert_eq!(
            journal.read_dispatch_unlocked(&first).unwrap().phase,
            DispatchPhase::Uncertain
        );
        assert!(journal.request_dispatch(first, committed_permit()).is_err());
        assert_eq!(fs::read(&marker).unwrap(), b"prior marker");
        assert_eq!(
            fs::read(&native_marker).unwrap(),
            b"retained native attempt"
        );
        journal
            .request_dispatch(second.clone(), committed_permit())
            .unwrap();
        journal.finish_dispatch(&second, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn completed_worker_invalid_http_response_retains_uncertainty_and_frees_other_session() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('2');
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        // Component boundary: the worker completed, but the host must refuse
        // this app-forged security header before returning a controller reply.
        let response = WebResponse {
            result: WebResult::Content {
                status: 200,
                mime_type: "text/plain".into(),
                encoding: "".into(),
                language: "".into(),
                etag: None,
                body: b"ok".to_vec(),
                download_name: None,
            },
            headers: vec![Header {
                name: "x-sandstorm-app-permissions".into(),
                value: "write".into(),
            }],
            set_cookies: vec![],
        };
        assert!(crate::http_response::serialize(&response, false).is_err());
        let released = DispatchFence::test_worker_released_for(first.clone());
        journal
            .finish_dispatch_uncertain_released(&first, released)
            .unwrap();
        assert_eq!(
            journal.read_dispatch_unlocked(&first).unwrap().phase,
            DispatchPhase::Uncertain
        );
        let mut second = dispatch_identity('3');
        second.session_resource = "6209".into();
        journal
            .request_dispatch(second.clone(), committed_permit())
            .unwrap();
        journal.finish_dispatch(&second, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn worker_release_rejects_wrong_identity_and_fenced_or_restarted_app() {
        let (path, journal, _) = running_journal();
        let cancelled = dispatch_identity('3');
        journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .unwrap();
        let other = dispatch_identity('4');
        let wrong = DispatchFence::test_worker_released_for(other);
        assert!(journal
            .finish_dispatch_uncertain_released(&cancelled, wrong)
            .is_err());
        assert_eq!(
            journal.read_dispatch_unlocked(&cancelled).unwrap().phase,
            DispatchPhase::DeliveryRequested
        );
        assert!(journal.active_dispatch_path().exists());

        // A restart with only the durable tombstone is not a worker ACK.
        drop(journal);
        let reopened = Journal::open(&path).unwrap();
        assert!(reopened
            .request_dispatch(dispatch_identity('5'), committed_permit())
            .is_err());
        reopened.fence_and_stop(|_| Ok(()), stopped).unwrap();
        let released = DispatchFence::test_worker_released_for(cancelled.clone());
        assert!(reopened
            .finish_dispatch_uncertain_released(&cancelled, released)
            .is_err());
        assert!(reopened.active_dispatch_path().exists());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn worker_release_after_uncertain_tombstone_can_finish_same_live_operation() {
        let (path, journal, _) = running_journal();
        let cancelled = dispatch_identity('6');
        journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .unwrap();
        assert!(journal.finish_dispatch(&cancelled, false).is_err());
        assert_eq!(
            journal.read_dispatch_unlocked(&cancelled).unwrap().phase,
            DispatchPhase::Uncertain
        );
        let released = DispatchFence::test_worker_released_for(cancelled.clone());
        journal
            .finish_dispatch_uncertain_released(&cancelled, released)
            .unwrap();
        assert!(!journal.active_dispatch_path().exists());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn crash_between_record_clear_and_active_unlink_stays_fail_closed() {
        let (path, journal, _) = running_journal();
        let cancelled = dispatch_identity('7');
        journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .unwrap();
        assert!(journal.finish_dispatch(&cancelled, false).is_err());
        journal
            .with_lock(|this| {
                let mut record = this.read_unlocked()?.unwrap();
                record.dispatch_in_flight = None;
                this.write_unlocked(&record)
            })
            .unwrap();
        drop(journal);
        let reopened = Journal::open(&path).unwrap();
        assert!(reopened.active_dispatch_path().exists());
        assert!(reopened
            .request_dispatch(dispatch_identity('8'), committed_permit())
            .is_err());
        let released = DispatchFence::test_worker_released_for(cancelled.clone());
        assert!(reopened
            .finish_dispatch_uncertain_released(&cancelled, released)
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn concurrent_app_fence_serializes_with_exact_worker_release() {
        let (path, journal, _) = running_journal();
        let cancelled = dispatch_identity('4');
        journal
            .request_dispatch(cancelled.clone(), committed_permit())
            .unwrap();
        let release_journal = Journal::open(&path).unwrap();
        let stop_journal = Journal::open(&path).unwrap();
        let barrier = Arc::new(Barrier::new(3));
        let release_barrier = Arc::clone(&barrier);
        let release_identity = cancelled.clone();
        let release = thread::spawn(move || {
            let witness = DispatchFence::test_worker_released_for(release_identity.clone());
            release_barrier.wait();
            release_journal
                .finish_dispatch_uncertain_released(&release_identity, witness)
                .is_ok()
        });
        let stop_barrier = Arc::clone(&barrier);
        let stop = thread::spawn(move || {
            stop_barrier.wait();
            stop_journal.fence_and_stop(|_| Ok(()), stopped).unwrap();
        });
        barrier.wait();
        let released = release.join().unwrap();
        stop.join().unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        assert_eq!(
            journal.read_dispatch_unlocked(&cancelled).unwrap().phase,
            if released {
                DispatchPhase::Uncertain
            } else {
                DispatchPhase::DeliveryRequested
            }
        );
        assert_eq!(journal.active_dispatch_path().exists(), !released);
        assert!(journal
            .request_dispatch(dispatch_identity('5'), committed_permit())
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn hard_fence_between_rpc_send_and_reply_retains_uncertain_one_shot() {
        let (path, journal, _) = running_journal();
        let identity = dispatch_identity('4');
        journal
            .request_dispatch(identity.clone(), committed_permit())
            .unwrap();
        journal.fence_and_stop(|_| Ok(()), stopped).unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        assert_eq!(
            journal.read_dispatch_unlocked(&identity).unwrap().phase,
            DispatchPhase::DeliveryRequested
        );
        assert!(journal.finish_dispatch(&identity, true).is_err());
        assert!(journal.active_dispatch_path().exists());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn crash_after_active_marker_fsync_blocks_new_dispatch() {
        let (path, journal, _) = running_journal();
        journal
            .with_lock(|this| this.create_active_dispatch_unlocked(&dispatch_identity('5')))
            .unwrap();
        assert!(journal
            .request_dispatch(dispatch_identity('6'), committed_permit())
            .is_err());
        assert!(!journal.dispatch_path(&dispatch_identity('6')).exists());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn dispatch_refuses_other_app_generation_or_unit_invocation_before_marker() {
        let (path, journal, _) = running_journal();
        let mut identity = dispatch_identity('7');
        identity.app = 92;
        assert!(journal
            .request_dispatch(identity.clone(), committed_permit())
            .is_err());
        identity.app = 91;
        identity.app_generation = 3;
        assert!(journal
            .request_dispatch(identity.clone(), committed_permit())
            .is_err());
        identity.app_generation = 2;
        identity.invocation_id = "e".repeat(32);
        assert!(journal
            .request_dispatch(identity, committed_permit())
            .is_err());
        assert!(!journal.active_dispatch_path().exists());
        assert!(!journal.dispatch_path(&dispatch_identity('7')).exists());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn dispatch_refuses_wrong_permit_hash_without_marking_in_flight() {
        let (path, journal, _) = running_journal();
        let identity = dispatch_identity('8');
        assert!(journal
            .request_dispatch(identity.clone(), b"wrong permit")
            .is_err());
        assert!(!journal.active_dispatch_path().exists());
        assert!(!journal.dispatch_permit_path(&identity).exists());
        assert!(journal
            .read()
            .unwrap()
            .unwrap()
            .dispatch_in_flight
            .is_none());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn source_digest_and_receipt_ids_are_canonical_decimal_nats() {
        let identity = dispatch_identity('1');
        assert!(identity.validate().is_ok());
        assert!(canonical_digest_decimal("0"));
        assert!(canonical_digest_decimal(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935"
        ));
        assert!(!canonical_digest_decimal(
            "115792089237316195423570985008687907853269984665640564039457584007913129639936"
        ));
        let mut hex_id = identity.clone();
        hex_id.dispatch_event = "a".repeat(64);
        assert!(hex_id.validate().is_err());
        let mut leading_zero = identity;
        leading_zero.request_digest = "01".into();
        assert!(leading_zero.validate().is_err());
    }

    #[test]
    fn dispatch_tombstone_is_per_session_operation_not_http_digest() {
        let (path, journal, _) = running_journal();
        let first = dispatch_identity('9');
        journal
            .request_dispatch(first.clone(), committed_permit())
            .unwrap();
        journal.finish_dispatch(&first, true).unwrap();

        // Same operation coordinate with changed HTTP bytes and receipt is a
        // replay, even though its request digest points elsewhere.
        let mut changed = dispatch_identity('8');
        changed.dispatch_transaction = "4".repeat(64);
        assert_eq!(first.operation_key(), changed.operation_key());
        assert!(journal
            .request_dispatch(changed.clone(), committed_permit())
            .is_err());
        assert!(!journal.active_dispatch_path().exists());

        // A different participant session can make the same HTTP request.
        let mut other_session = first.clone();
        other_session.session_resource = "6209".into();
        assert_ne!(first.operation_key(), other_session.operation_key());
        journal
            .request_dispatch(other_session.clone(), committed_permit())
            .unwrap();
        assert!(journal.dispatch_path(&other_session).exists());
        assert!(journal.dispatch_permit_path(&other_session).exists());
        journal.finish_dispatch(&other_session, true).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn changed_captured_permit_cannot_be_marked_delivered() {
        let (path, journal, _) = running_journal();
        let identity = dispatch_identity('0');
        journal
            .request_dispatch(identity.clone(), committed_permit())
            .unwrap();
        fs::write(journal.dispatch_permit_path(&identity), b"altered bytes").unwrap();
        assert!(journal.finish_dispatch(&identity, true).is_err());
        assert_eq!(
            journal.read_dispatch_unlocked(&identity).unwrap().phase,
            DispatchPhase::DeliveryRequested
        );
        assert!(journal.active_dispatch_path().exists());
        fs::remove_dir_all(path).unwrap();
    }

    fn stopped(record: &Record) -> io::Result<UnitStopAudit> {
        Ok(UnitStopAudit {
            unit: record.identity.unit.clone(),
            invocation_id: None,
            control_group: record.control_group.clone(),
            unit_loaded: true,
            inactive: true,
            main_pid: 0,
            queued_job: false,
            exact_cgroup_empty: true,
        })
    }

    #[test]
    fn source_bound_stop_checks_incarnation_and_volume_under_lock_and_recovers_fence() {
        use std::sync::atomic::AtomicUsize;

        let (path, journal, begin) = running_journal();
        let expected = StopIdentity {
            app: begin.app,
            generation: begin.generation,
            unit: begin.unit.clone(),
            image_identity: begin.image_identity.clone(),
            invocation_id: instance().invocation_id,
            control_group: instance().control_group,
        };
        let stops = AtomicUsize::new(0);
        let volume_checks = AtomicUsize::new(0);
        let mut wrong = expected.clone();
        wrong.invocation_id = "e".repeat(32);
        let inspect = |record: &Record| {
            if stops.load(Ordering::SeqCst) == 0 {
                Err(invalid("injected manager still active"))
            } else {
                stopped(record)
            }
        };
        assert!(journal
            .fence_and_stop_checked_with_mode(
                &expected,
                || Ok(()),
                true,
                |_| Ok(()),
                |_| {
                    stops.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                },
                inspect,
            )
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Running);
        assert_eq!(stops.load(Ordering::SeqCst), 0);
        assert!(journal
            .fence_and_stop_checked_with(&wrong, || Ok(()), |_| Ok(()), |_| Ok(()), inspect)
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Running);
        wrong.invocation_id = expected.invocation_id.clone();
        assert!(journal
            .fence_and_stop_checked_with(
                &wrong,
                || Err(invalid("injected volume drift")),
                |_| Ok(()),
                |_| Ok(()),
                inspect,
            )
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Running);
        assert!(journal
            .fence_and_stop_checked_with(
                &expected,
                || {
                    volume_checks.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                },
                |_| Ok(()),
                |_| Err(invalid("injected uncertain manager reply")),
                inspect,
            )
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Fenced);
        journal
            .fence_and_stop_checked_with_mode(
                &expected,
                || {
                    volume_checks.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                },
                true,
                |_| Ok(()),
                |_| {
                    stops.fetch_add(1, Ordering::SeqCst);
                    Ok(())
                },
                inspect,
            )
            .unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        assert_eq!(stops.load(Ordering::SeqCst), 1);
        assert!(volume_checks.load(Ordering::SeqCst) >= 2);
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn checked_stop_audit_projects_prior_incarnation_and_commits_observation() {
        let (path, _, begin) = running_journal();
        let expected = StopIdentity {
            app: begin.app,
            generation: begin.generation,
            unit: begin.unit,
            image_identity: begin.image_identity,
            invocation_id: instance().invocation_id,
            control_group: instance().control_group,
        };
        let audit = UnitStopAudit {
            unit: expected.unit.clone(),
            invocation_id: None,
            control_group: Some(expected.control_group.clone()),
            unit_loaded: true,
            inactive: true,
            main_pid: 0,
            queued_job: false,
            exact_cgroup_empty: true,
        };
        let projected = audit.source_stop_audit(&expected).unwrap();
        assert_eq!(projected["managerMainPid"], "0");
        assert_eq!(
            projected["recordedInvocationId"],
            expected
                .invocation_id
                .as_bytes()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect::<String>()
        );
        let digest = projected["observationDigest"].as_str().unwrap();
        assert!(canonical_digest_decimal(digest));
        assert_eq!(audit.source_stop_audit(&expected).unwrap(), projected);
        let mut wrong = expected.clone();
        wrong.unit = "different.service".into();
        assert!(audit.source_stop_audit(&wrong).is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn stopped_audit_is_read_only_and_refuses_running_or_wrong_incarnation() {
        let (path, journal, begin) = running_journal();
        let expected = StopIdentity {
            app: begin.app,
            generation: begin.generation,
            unit: begin.unit,
            image_identity: begin.image_identity,
            invocation_id: instance().invocation_id,
            control_group: instance().control_group,
        };
        assert!(journal
            .audit_stopped_checked_with(&expected, || Ok(()), stopped)
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Running);
        journal
            .fence_and_stop_checked_with(&expected, || Ok(()), |_| Ok(()), |_| Ok(()), stopped)
            .unwrap();
        let before = journal.read().unwrap().unwrap();
        let audit = journal
            .audit_stopped_checked_with(&expected, || Ok(()), stopped)
            .unwrap();
        assert!(audit.source_stop_audit(&expected).is_ok());
        assert_eq!(journal.read().unwrap().unwrap(), before);
        let mut wrong = expected.clone();
        wrong.image_identity.push('x');
        assert!(journal
            .audit_stopped_checked_with(&wrong, || Ok(()), stopped)
            .is_err());
        assert!(journal
            .audit_stopped_checked_with(
                &expected,
                || Err(invalid("injected volume drift")),
                stopped
            )
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn duplicate_conflict_and_fence_are_durable() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        assert_eq!(journal.arm(identity.clone()).unwrap().phase, Phase::Armed);
        let mut conflict = identity.clone();
        conflict.event_id = "789".into();
        assert!(journal.arm(conflict).is_err());
        journal.request_launch(&identity).unwrap();
        assert!(journal.request_launch(&identity).is_err());
        journal.fence_and_stop(|_| Ok(()), stopped).unwrap();
        assert_eq!(
            Journal::open(&path).unwrap().read().unwrap().unwrap().phase,
            Phase::Stopped
        );
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                &instance(),
                || Ok(child(123)),
                Journal::write_unlocked
            )
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn uncertain_start_and_stop_never_clear_tombstone_early() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                &instance(),
                || Err::<MockChild, _>(invalid("injected start fault")),
                Journal::write_unlocked
            )
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Entered);
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                &instance(),
                || Ok(child(124)),
                Journal::write_unlocked
            )
            .is_err());
        assert!(journal
            .fence_and_stop(|_| Err(invalid("injected stop fault")), stopped)
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Fenced);
        assert!(journal
            .fence_and_stop(
                |_| Ok(()),
                |record| {
                    let mut audit = stopped(record)?;
                    audit.exact_cgroup_empty = false;
                    Ok(audit)
                }
            )
            .is_err());
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Fenced);
        journal.fence_and_stop(|_| Ok(()), stopped).unwrap();
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn fence_waits_for_spawn_linearization_then_stops_exact_unit() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        let entered = Arc::new(Barrier::new(2));
        let release = Arc::new(Barrier::new(2));
        let worker = {
            let journal = journal.clone();
            let identity = identity.clone();
            let entered = entered.clone();
            let release = release.clone();
            thread::spawn(move || {
                journal.enter_and_spawn_with(
                    &identity,
                    &instance(),
                    || {
                        entered.wait();
                        release.wait();
                        Ok(child(456))
                    },
                    Journal::write_unlocked,
                )
            })
        };
        entered.wait();
        let stopper = {
            let journal = journal.clone();
            thread::spawn(move || {
                journal.fence_and_stop(
                    |unit| {
                        assert_eq!(unit, "mini-spk-a91-g2.service");
                        Ok(())
                    },
                    stopped,
                )
            })
        };
        release.wait();
        assert_eq!(worker.join().unwrap().unwrap().pid(), 456);
        stopper.join().unwrap().unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn running_fsync_failure_aborts_spawn_before_unlock() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        let aborted = Arc::new(AtomicBool::new(false));
        let observed = aborted.clone();
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                &instance(),
                || Ok(MockChild { pid: 457, aborted }),
                |_, _| Err(invalid("injected Running fsync failure"))
            )
            .is_err());
        assert!(observed.load(Ordering::SeqCst));
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Entered);
        assert!(journal
            .enter_and_spawn_with(
                &identity,
                &instance(),
                || Ok(child(458)),
                Journal::write_unlocked
            )
            .is_err());
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn mismatched_or_missing_unit_audit_retains_fence() {
        let path = scratch();
        let journal = Journal::open(&path).unwrap();
        let identity = begin();
        journal.arm(identity.clone()).unwrap();
        journal.request_launch(&identity).unwrap();
        let child = journal
            .enter_and_spawn_with(
                &identity,
                &instance(),
                || Ok(child(459)),
                Journal::write_unlocked,
            )
            .unwrap();
        assert_eq!(child.pid(), 459);
        for changed in ["missing", "invocation", "cgroup", "job", "pid"] {
            assert!(journal
                .fence_and_stop(
                    |_| Ok(()),
                    |record| {
                        let mut audit = stopped(record)?;
                        match changed {
                            "missing" => audit.unit_loaded = false,
                            "invocation" => audit.invocation_id = Some("e".repeat(32)),
                            "cgroup" => audit.control_group = Some("/other/unit".into()),
                            "job" => audit.queued_job = true,
                            "pid" => audit.main_pid = 459,
                            _ => unreachable!(),
                        }
                        Ok(audit)
                    },
                )
                .is_err());
            assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Fenced);
        }
        journal.fence_and_stop(|_| Ok(()), stopped).unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn installed_system_unit_stop_audit_probe() {
        if std::env::var("MINI_SPK_SYSTEMD_AUDIT_PROBE").as_deref() != Ok("1") {
            return;
        }
        assert_eq!(unsafe { libc::geteuid() }, 0);
        let identity = VerifiedBegin {
            app: 991005,
            generation: 1,
            operation_id: "1".into(),
            transaction_id: "123".into(),
            event_id: "456".into(),
            package_sha256: "c".repeat(64),
            image_identity: "harmless-systemd-audit-probe".into(),
            process_identity: "installed-unit".into(),
            unit: "mini-spk-a991005-g1.service".into(),
        };
        let output = systemd_show(&identity.unit).unwrap();
        assert_eq!(property(&output, "LoadState").unwrap(), "loaded");
        assert_eq!(property(&output, "ActiveState").unwrap(), "active");
        let instance = UnitInstance {
            invocation_id: property(&output, "InvocationID").unwrap().to_owned(),
            control_group: property(&output, "ControlGroup").unwrap().to_owned(),
        };
        instance.validate(&identity.unit).unwrap();
        let record = Record {
            version: VERSION,
            identity,
            phase: Phase::Fenced,
            child_pid: Some(1),
            invocation_id: Some(instance.invocation_id),
            control_group: Some(instance.control_group),
            dispatch_in_flight: None,
        };
        UnitStopAudit::before_stop(&record).unwrap();
        let status = Command::new("/usr/bin/systemctl")
            .args(["--system", "stop", record.unit()])
            .status()
            .unwrap();
        assert!(status.success());
        UnitStopAudit::inspect(&record)
            .unwrap()
            .prove(&record)
            .unwrap();
        // Simulate a crash after systemd stop but before Stopped fsync. The
        // production retry must recognize the exact cleared manager/cgroup
        // state and finish the durable tombstone without a second stop.
        let path = Path::new("/run").join(format!("mini-spk-stop-audit-{}", std::process::id()));
        fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
        let journal = Journal::open(&path).unwrap();
        journal
            .with_lock(|this| this.write_unlocked(&record))
            .unwrap();
        journal.fence_and_stop_manager().unwrap();
        assert_eq!(journal.read().unwrap().unwrap().phase, Phase::Stopped);
        fs::remove_dir_all(path).unwrap();
    }

    #[test]
    fn unit_process_matches_manager_invocation_probe() {
        if std::env::var("MINI_SPK_UNIT_INSTANCE_PROBE").as_deref() != Ok("1") {
            return;
        }
        assert_eq!(unsafe { libc::geteuid() }, 0);
        let instance = UnitInstance::current("mini-spk-a991006-g1.service").unwrap();
        assert_eq!(instance.invocation_id.len(), 32);
        assert_eq!(
            instance.control_group,
            "/system.slice/mini-spk-a991006-g1.service"
        );
    }
}
