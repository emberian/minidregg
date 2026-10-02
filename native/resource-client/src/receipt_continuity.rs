//! Durable receipt continuity custody. Lean owns every proof decision; this module
//! only bounds transport, serializes completions, and durably remembers verified points.
pub(crate) mod carry;
use crate::{workspace, Result, SOCKET};
use serde_json::{json, Value};
use std::cmp::Ordering;
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};

#[path = "fresh_onboarding.rs"]
pub(crate) mod fresh;

const DIRECTORY: &str = "receipt-continuity";
const ALGORITHM: &str = "minidregg-continuity-v1";
const MAX_JSON: u64 = 1024 * 1024;
const MAX_HOPS: usize = 4096;
#[cfg(target_os = "macos")]
const NOFOLLOW: i32 = 0x100;
#[cfg(not(target_os = "macos"))]
const NOFOLLOW: i32 = 0x20000;
#[cfg(target_os = "macos")]
const DIRECTORY_FLAG: i32 = 0x100000;
#[cfg(not(target_os = "macos"))]
const DIRECTORY_FLAG: i32 = 0x10000;
unsafe extern "C" {
    fn geteuid() -> u32;
    fn flock(fd: i32, operation: i32) -> i32;
}

fn fail(error: impl std::fmt::Display) -> String {
    format!("receipt continuity: {error}")
}
fn text<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| fail(format!("missing {key}")))
}
fn decimal(value: &str) -> Result<()> {
    if value.is_empty()
        || value.len() > 80
        || (value.len() > 1 && value.starts_with('0'))
        || !value.bytes().all(|c| c.is_ascii_digit())
    {
        return Err(fail(
            "expected a canonical decimal string of at most 80 digits",
        ));
    }
    Ok(())
}
fn compare(left: &str, right: &str) -> Ordering {
    left.len().cmp(&right.len()).then(left.cmp(right))
}

#[derive(Clone, Debug)]
struct Point {
    height: String,
    world_root: String,
    witness: Option<(String, Vec<String>)>,
}
impl PartialEq for Point {
    fn eq(&self, other: &Self) -> bool {
        self.height == other.height && self.world_root == other.world_root
    }
}
impl Eq for Point {}
impl Point {
    fn parse(value: &Value) -> Result<Self> {
        let height = text(value, "height")?;
        let world_root = text(value, "worldRoot")?;
        decimal(height)?;
        decimal(world_root)?;
        Ok(Self {
            height: height.into(),
            world_root: world_root.into(),
            witness: None,
        })
    }
    fn json(&self) -> Value {
        json!({"height":self.height,"worldRoot":self.world_root})
    }
    fn with_witness(mut self, value: &Value) -> Result<Self> {
        let chain = text(value, "chain")?;
        decimal(chain)?;
        let values = value["siblings"]
            .as_array()
            .ok_or_else(|| fail("missing endpoint siblings"))?;
        if values.len() > 256 {
            return Err(fail("endpoint siblings exceed bound"));
        }
        let siblings = values
            .iter()
            .map(|value| {
                let value = value
                    .as_str()
                    .ok_or_else(|| fail("endpoint sibling is not a string"))?;
                decimal(value)?;
                Ok(value.to_owned())
            })
            .collect::<Result<Vec<_>>>()?;
        self.witness = Some((chain.into(), siblings));
        Ok(self)
    }
}
fn identity(profile: &Value) -> Result<Value> {
    for name in ["domain", "semantics", "expectedSeed"] {
        decimal(text(profile, name)?)?;
    }
    Ok(json!({"algorithm":ALGORITHM,"domain":profile["domain"],
        "semantics":profile["semantics"],"expectedSeed":profile["expectedSeed"]}))
}
fn private_metadata(file: &File, directory: bool) -> Result<()> {
    let meta = file.metadata().map_err(fail)?;
    if meta.uid() != unsafe { geteuid() }
        || meta.mode() & 0o077 != 0
        || if directory {
            !meta.is_dir()
        } else {
            !meta.is_file() || meta.nlink() != 1
        }
    {
        return Err(fail(
            "custody path must be owner-private, regular, and unlinked elsewhere",
        ));
    }
    Ok(())
}
fn directory(path: &Path) -> Result<File> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW | DIRECTORY_FLAG)
        .open(path)
        .map_err(fail)?;
    private_metadata(&file, true)?;
    Ok(file)
}
fn read_json(path: &Path) -> Result<Value> {
    read_json_mode(path, true)
}
fn read_json_mode(path: &Path, custody: bool) -> Result<Value> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(NOFOLLOW)
        .open(path)
        .map_err(fail)?;
    if custody {
        private_metadata(&file, false)?;
    } else {
        // Existing retained query files are public-mode inside a private workspace.
        // This imports only the claimed point; the prefix proof authenticates it.
        let meta = file.metadata().map_err(fail)?;
        if !meta.is_file() || meta.uid() != unsafe { geteuid() } {
            return Err(fail("retained point is not an owned regular file"));
        }
    }
    if file.metadata().map_err(fail)?.len() > MAX_JSON {
        return Err(fail("JSON exceeds custody bound"));
    }
    let mut bytes = Vec::new();
    file.take(MAX_JSON + 1)
        .read_to_end(&mut bytes)
        .map_err(fail)?;
    if bytes.len() as u64 > MAX_JSON {
        return Err(fail("JSON exceeds custody bound"));
    }
    serde_json::from_slice(&bytes).map_err(fail)
}
fn create_file(path: &Path, bytes: &[u8]) -> Result<()> {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(NOFOLLOW)
        .open(path)
        .map_err(fail)?;
    file.write_all(bytes)
        .and_then(|()| file.sync_all())
        .map_err(fail)
}
fn lock(root: &Path) -> Result<File> {
    lock_named(root, "lock")
}
fn lock_named(root: &Path, name: &str) -> Result<File> {
    let _directory = directory(root)?;
    let path = root.join(name);
    let file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .custom_flags(NOFOLLOW)
        .open(&path)
        .map_err(fail)?;
    private_metadata(&file, false)?;
    // Separate open descriptions also serialize threads in this process.
    for _ in 0..100 {
        if unsafe { flock(file.as_raw_fd(), 2 | 4) } == 0 {
            return Ok(file);
        }
        let error = std::io::Error::last_os_error();
        if error.kind() != std::io::ErrorKind::WouldBlock {
            return Err(fail(error));
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
    Err(fail("another completion owns the anchor; retry this read"))
}
#[derive(Clone, Copy, PartialEq)]
enum SaveStage {
    BeforeFileSync,
    BeforeRename,
    AfterRename,
    AfterDirectorySync,
}
fn save_with(
    root: &Path,
    name: &str,
    value: &Value,
    mut stage: impl FnMut(SaveStage) -> Result<()>,
) -> Result<()> {
    let parent = directory(root)?;
    let temporary = root.join(format!(".pending-{}", workspace::random_nonce()?));
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .mode(0o600)
        .custom_flags(NOFOLLOW)
        .open(&temporary)
        .map_err(fail)?;
    let bytes = serde_json::to_vec(value).map_err(fail)?;
    if bytes.len() as u64 > MAX_JSON {
        return Err(fail("persisted JSON exceeds custody bound"));
    }
    file.write_all(&bytes).map_err(fail)?;
    stage(SaveStage::BeforeFileSync)?;
    file.sync_all().map_err(fail)?;
    stage(SaveStage::BeforeRename)?;
    let named = fs::symlink_metadata(root).map_err(fail)?;
    let opened = parent.metadata().map_err(fail)?;
    if (named.dev(), named.ino()) != (opened.dev(), opened.ino()) {
        return Err(fail("custody directory changed"));
    }
    fs::rename(&temporary, root.join(name)).map_err(fail)?;
    stage(SaveStage::AfterRename)?;
    parent.sync_all().map_err(fail)?;
    stage(SaveStage::AfterDirectorySync)
}
fn save(root: &Path, name: &str, value: &Value) -> Result<()> {
    save_with(root, name, value, |_| Ok(()))
}

#[derive(Clone)]
struct Settings {
    identity: Value,
    verifier: PathBuf,
    verifier_sha256: String,
}
impl Settings {
    fn load(root: &Path) -> Result<Self> {
        let value = read_json(&root.join("enabled.json")).map_err(|e| {
            fail(format!(
                "enabled or incomplete custody cannot be reset automatically: {e}"
            ))
        })?;
        Self::parse(&value)
    }
    fn parse(value: &Value) -> Result<Self> {
        if text(&value, "type")? != "minidregg-receipt-continuity-custody-v1" {
            return Err(fail("unknown custody version"));
        }
        let selected = identity(&value["identity"])?;
        if selected != value["identity"] {
            return Err(fail("identity or algorithm changed"));
        }
        let verifier = PathBuf::from(text(&value, "verifier")?);
        if !verifier.is_absolute() {
            return Err(fail("verifier path is not absolute"));
        }
        Ok(Self {
            identity: selected,
            verifier,
            verifier_sha256: text(&value, "verifierSha256")?.into(),
        })
    }
    fn json(&self) -> Value {
        json!({"type":"minidregg-receipt-continuity-custody-v1","identity":self.identity,
            "verifier":self.verifier,"verifierSha256":self.verifier_sha256})
    }
    fn check(&self, config: &Path) -> Result<()> {
        if crate::host_image_sha256(&self.verifier)? != self.verifier_sha256 {
            return Err(fail("local verifier image changed"));
        }
        if local_identity(&self.verifier, config)? != self.identity {
            return Err(fail("configured deployment identity changed"));
        }
        Ok(())
    }
}
fn local_identity(verifier: &Path, config: &Path) -> Result<Value> {
    let output = Command::new(verifier)
        .arg(config)
        .arg("profile")
        .output()
        .map_err(fail)?;
    if !output.status.success() || output.stdout.len() as u64 > MAX_JSON {
        return Err(fail("local verifier profile failed or exceeded bound"));
    }
    identity(&serde_json::from_slice(&output.stdout).map_err(fail)?)
}
fn anchor(root: &Path, settings: &Settings) -> Result<Point> {
    let value = read_json(&root.join("anchor.json")).map_err(|e| {
        fail(format!(
            "enabled workspace anchor missing or corrupt; restore durable custody: {e}"
        ))
    })?;
    if value["identity"] != settings.identity {
        return Err(fail("anchor deployment identity differs"));
    }
    let point = Point::parse(&value["point"])?.with_witness(&value)?;
    // A previous writer may have died after rename but before directory fsync.
    // Reconfirm the recovered pathname before it becomes any request's baseline.
    directory(root)?.sync_all().map_err(fail)?;
    Ok(point)
}
fn persist(root: &Path, settings: &Settings, point: &Point) -> Result<()> {
    let (chain, siblings) = point
        .witness
        .as_ref()
        .ok_or_else(|| fail("verified endpoint lacks witness"))?;
    save(
        root,
        "anchor.json",
        &json!({"identity":settings.identity,"point":point.json(),
        "chain":chain,"siblings":siblings}),
    )
}
#[derive(Clone, Copy, PartialEq)]
pub(crate) enum Mode {
    Ordinary,
    Historical,
    ReceiptReplay,
}
pub(crate) struct Ticket {
    baseline: Point,
    settings: Settings,
}
/// Explicit key commitment adoption requires an already authenticated lineage.
/// This never enrolls an unprotected workspace or trusts an endpoint profile.
pub(crate) fn key_transition_identity(root: &Path, workspace: &Value) -> Result<Value> {
    key_transition_identity_if_enabled(root, workspace)?
        .ok_or_else(|| fail("key adoption requires existing authenticated continuity custody"))
}

pub(crate) fn key_transition_identity_if_enabled(root: &Path, workspace: &Value) -> Result<Option<Value>> {
    Ok(begin(root, workspace)?.map(|ticket| ticket.settings.identity))
}

/// Closed pure source operations for signing an adoption or protected rotation.
/// No Store command or caller-selected arbitrary native operation is exposed.
#[derive(Clone, Copy)]
pub(crate) enum KeySourceOperation {
    AdoptionPlan,
    AdoptionIngress,
    RotationPlan,
    RotationCommand,
    NextKeyDigest,
}
pub(crate) fn key_source(
    root: &Path, workspace: &Value, expected_identity: &Value,
    operation: KeySourceOperation, input: &[u8],
) -> Result<Vec<u8>> {
    const LIMIT: usize = 256 * 1024;
    if input.is_empty() || input.len() > LIMIT {
        return Err(fail("key source input exceeds bound"));
    }
    if key_transition_identity(root, workspace)? != *expected_identity {
        return Err(fail("key source lineage changed"));
    }
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    if read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail("workspace manifest changed before key source verification"));
    }
    let settings = Settings::load(&custody)?;
    let config = workspace::member_path(workspace, "config")?;
    if settings.identity != *expected_identity {
        return Err(fail("key source identity changed under custody lock"));
    }
    settings.check(&config)?;
    anchor(&custody, &settings)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let (verb, kind) = match operation {
        KeySourceOperation::AdoptionPlan => ("inspect", "subject-key-adoption-plan"),
        KeySourceOperation::AdoptionIngress => ("inspect", "subject-key-adoption-ingress"),
        KeySourceOperation::RotationPlan => ("inspect", "subject-key-rotation-plan"),
        KeySourceOperation::RotationCommand => ("author", "subject-key-rotation"),
        KeySourceOperation::NextKeyDigest => ("author", "signing-key-next-digest"),
    };
    directory(&root.join("attempts"))?;
    let scratch = root.join("attempts").join(format!("key-source-{}", workspace::random_nonce()?));
    workspace::make_private_dir(&scratch)?;
    let input_path = scratch.join("input.bin");
    let output_path = scratch.join("output.bin");
    create_file(&input_path, input)?;
    create_file(&output_path, b"")?;
    let status = Command::new(&settings.verifier).arg(&config).arg(verb).arg(kind)
        .arg(&input_path).arg(&output_path)
        .stdout(std::process::Stdio::null()).stderr(std::process::Stdio::null())
        .status().map_err(fail)?;
    if !status.success() { return Err(fail(format!("pinned local verifier refused {kind}"))); }
    if crate::host_image_sha256(&settings.verifier)? != settings.verifier_sha256
        || crate::agent_reserve::bounded(&config, MAX_JSON as usize)? != config_bytes
        || read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail("key source custody inputs changed during verification"));
    }
    let output = OpenOptions::new().read(true).custom_flags(NOFOLLOW).open(&output_path).map_err(fail)?;
    private_metadata(&output, false)?;
    if output.metadata().map_err(fail)?.len() > LIMIT as u64 {
        return Err(fail("key source output exceeds bound"));
    }
    let mut bytes = Vec::new();
    output.take((LIMIT + 1) as u64).read_to_end(&mut bytes).map_err(fail)?;
    if bytes.is_empty() || bytes.len() > LIMIT { return Err(fail("invalid key source output size")); }
    Ok(bytes)
}

static LEGACY_WARNING: AtomicBool = AtomicBool::new(false);
pub(crate) fn begin(root: &Path, workspace: &Value) -> Result<Option<Ticket>> {
    // A long-lived shell can hold an older manifest while another process enables
    // continuity. Consult the durable manifest rather than downgrading that shell.
    let mut manifest = read_json(&root.join("workspace.json"))?;
    directory(root)?.sync_all().map_err(fail)?;
    if workspace.get("receiptContinuity").is_some() && manifest.get("receiptContinuity").is_none() {
        return Err(fail("workspace continuity enablement disappeared"));
    }
    fresh::guard(root, &manifest)?;
    let enabled = match manifest.get("receiptContinuity") {
        None => false,
        Some(Value::String(value)) if value == ALGORITHM => true,
        _ => return Err(fail("unknown workspace continuity mode")),
    };
    let workspace_root = root;
    let root = root.join(DIRECTORY);
    match fs::symlink_metadata(&root) {
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            if enabled {
                return Err(fail(
                    "enabled workspace custody directory is missing; restore durable custody",
                ));
            }
            if !LEGACY_WARNING.swap(true, AtomicOrdering::Relaxed) {
                eprintln!("workspace continuity: legacy; initialize with workspace --action continuity-init --name REF");
            }
            return Ok(None);
        }
        Err(error) => return Err(fail(error)),
        Ok(_) => (),
    }
    let _lock = lock(&root)?;
    carry::recover_locked(workspace_root)?;
    manifest = read_json(&workspace_root.join("workspace.json"))?;
    if manifest["config"] != workspace["config"]
        || manifest["host"] != workspace["host"]
        || manifest["hostSha256"] != workspace["hostSha256"]
    {
        return Err(fail(
            "workspace migrated; reload its configuration before requesting",
        ));
    }
    let settings = Settings::load(&root)?;
    settings.check(&workspace::member_path(workspace, "config")?)?;
    let baseline = anchor(&root, &settings)?;
    if !enabled {
        // Recover only a completely persisted initial anchor and enable marker;
        // never bootstrap or replace an endpoint during an ordinary read.
        manifest["receiptContinuity"] = json!(ALGORITHM);
        save(workspace_root, "workspace.json", &manifest)?;
    }
    Ok(Some(Ticket { baseline, settings }))
}

trait ProofSource {
    fn verified_hop(&mut self, from: Option<&Point>, target: &Point) -> Result<(Point, bool)>;
}
struct HostProof<'a> {
    workspace: &'a Value,
    settings: &'a Settings,
    scratch: PathBuf,
}
impl HostProof<'_> {
    fn challenge_point(&self, challenge: &Value) -> Result<Point> {
        let config = workspace::member_path(self.workspace, "config")?;
        let hop = self.scratch.join(workspace::random_nonce()?);
        workspace::make_private_dir(&hop)?;
        let input = hop.join("challenge.json");
        let output = hop.join("point.json");
        let bytes = serde_json::to_vec(challenge).map_err(fail)?;
        if bytes.len() as u64 > MAX_JSON {
            return Err(fail("challenge exceeds bound"));
        }
        create_file(&input, &bytes)?;
        create_file(&output, b"")?;
        self.settings.check(&config)?;
        // Challenge heights include genesisHeight. Lean converts them to receipt
        // accepted-count coordinates and binds domain/semantics to this config.
        let result = Command::new(&self.settings.verifier)
            .arg(&config)
            .arg("continuity-point")
            .arg(&input)
            .arg(&output)
            .output()
            .map_err(fail)?;
        if !result.status.success() {
            return Err(fail("local Lean verifier refused observation point"));
        }
        Point::parse(&read_json(&output)?)
    }
    fn new<'a>(root: &Path, workspace: &'a Value, settings: &'a Settings) -> Result<HostProof<'a>> {
        let scratch = root
            .join("attempts")
            .join(format!("continuity-{}", workspace::random_nonce()?));
        workspace::make_private_dir(&scratch)?;
        Ok(HostProof {
            workspace,
            settings,
            scratch,
        })
    }
}
fn bounded_response(value: &Value) -> Result<()> {
    for (name, maximum) in [("suffix", 4096), ("fromSiblings", 256), ("toSiblings", 256)] {
        let values = value
            .get(name)
            .and_then(Value::as_array)
            .ok_or_else(|| fail(format!("missing {name}")))?;
        if values.len() > maximum {
            return Err(fail(format!("{name} exceeds hop bound")));
        }
        for value in values {
            decimal(
                value
                    .as_str()
                    .ok_or_else(|| fail("hash is not a decimal string"))?,
            )?;
        }
    }
    for name in ["startChain", "endChain"] {
        decimal(text(value, name)?)?;
    }
    Point::parse(&value["from"])?;
    Point::parse(&value["to"])?;
    Ok(())
}
impl HostProof<'_> {
    fn verify_response(&self, query: &Value, response_bytes: &[u8]) -> Result<(Point, bool)> {
        if response_bytes.len() as u64 > MAX_JSON {
            return Err(fail("response exceeds proof bound"));
        }
        let bytes = serde_json::to_vec(query).map_err(fail)?;
        let config = workspace::member_path(self.workspace, "config")?;
        let response: Value = serde_json::from_slice(response_bytes).map_err(fail)?;
        bounded_response(&response)?;
        // A fresh private directory per hop avoids reuse of a stale success result.
        let hop = self.scratch.join(workspace::random_nonce()?);
        workspace::make_private_dir(&hop)?;
        let request_path = hop.join("request.json");
        let response_path = hop.join("response.json");
        let result_path = hop.join("verified.json");
        create_file(&request_path, &bytes)?;
        create_file(&response_path, response_bytes)?;
        create_file(&result_path, b"")?;
        self.settings.check(&config)?;
        let result = Command::new(&self.settings.verifier)
            .arg(&config)
            .arg("continuity-verify")
            .arg(&request_path)
            .arg(&response_path)
            .arg(&result_path)
            .output()
            .map_err(fail)?;
        if !result.status.success() {
            return Err(fail("local Lean verifier refused continuity proof"));
        }
        let verified = read_json(&result_path)?;
        let point = Point::parse(&verified["to"])?.with_witness(&verified)?;
        let complete = verified["complete"]
            .as_bool()
            .ok_or_else(|| fail("verifier result lacks complete"))?;
        if point.json() != response["to"]
            || Some(complete) != response["complete"].as_bool()
            || verified["chain"] != response["endChain"]
            || verified["siblings"] != response["toSiblings"]
        {
            return Err(fail("verifier result and response disagree"));
        }
        Ok((point, complete))
    }
}
impl HostProof<'_> {
    fn response(&self, query: &Value) -> Result<Vec<u8>> {
        let bytes = serde_json::to_vec(query).map_err(fail)?;
        let host = workspace::workspace_host(self.workspace)?;
        let config = workspace::member_path(self.workspace, "config")?;
        let socket = SOCKET
            .get()
            .ok_or_else(|| fail("continuity requires a pinned Host socket"))?;
        let frame = crate::session_invoke(&host, socket, &config, 151, &bytes)?;
        if frame.first() != Some(&151) || frame.len() as u64 > MAX_JSON {
            return Err(fail("Host refused continuity or exceeded hop bound"));
        }
        Ok(frame[1..].to_vec())
    }
}
impl ProofSource for HostProof<'_> {
    fn verified_hop(&mut self, from: Option<&Point>, target: &Point) -> Result<(Point, bool)> {
        let mut query = json!({"identity":self.settings.identity,"from":from.map(Point::json),"target":target.json()});
        if let Some((chain, siblings)) = from.and_then(|point| point.witness.as_ref()) {
            query["fromChain"] = json!(chain);
            query["fromSiblings"] = json!(siblings);
        }
        self.verify_response(&query, &self.response(&query)?)
    }
}
fn walk(
    source: &mut impl ProofSource,
    from: &Point,
    target: &Point,
    mut accepted: impl FnMut(&Point) -> Result<()>,
) -> Result<()> {
    let mut cursor = from.clone();
    for _ in 0..MAX_HOPS {
        let (next, complete) = source.verified_hop(Some(&cursor), target)?;
        if compare(&next.height, &cursor.height) == Ordering::Less
            || compare(&next.height, &target.height) == Ordering::Greater
            || (next.height == cursor.height && next != cursor)
            || (complete && next != *target)
            || (!complete && compare(&next.height, &cursor.height) != Ordering::Greater)
            || (!complete && next.height == target.height)
        {
            return Err(fail("verifier returned invalid pagination progress"));
        }
        accepted(&next)?;
        if complete {
            return Ok(());
        }
        cursor = next;
    }
    Err(fail(
        "proof exceeded hop budget; verified progress retained, retry read",
    ))
}
fn finish_locked(
    root: &Path,
    ticket: &Ticket,
    target: &Point,
    mode: Mode,
    source: &mut impl ProofSource,
) -> Result<()> {
    if mode == Mode::Ordinary && compare(&target.height, &ticket.baseline.height) == Ordering::Less
    {
        return Err(fail("read is older than its pre-read baseline"));
    }
    if target.height == ticket.baseline.height && *target != ticket.baseline {
        return Err(fail("same-height read root differs from pre-read baseline"));
    }
    let current = anchor(root, &ticket.settings)?;
    if compare(&current.height, &ticket.baseline.height) == Ordering::Less
        || (current.height == ticket.baseline.height && current != ticket.baseline)
    {
        return Err(fail(
            "durable anchor was rolled back or replaced during read",
        ));
    }
    match compare(&target.height, &current.height) {
        Ordering::Equal if *target != current => {
            Err(fail("same-height root differs from durable anchor"))
        }
        Ordering::Equal => Ok(()),
        Ordering::Less => walk(source, target, &current, |_| Ok(())),
        Ordering::Greater if mode == Mode::Historical => Err(fail(
            "historical receipt is newer than the durable anchor; use an ordinary read",
        )),
        Ordering::Greater => walk(source, &current, target, |point| {
            persist(root, &ticket.settings, point)
        }),
    }
}
pub(crate) fn finish(
    root: &Path,
    workspace: &Value,
    ticket: Option<Ticket>,
    challenge: &Value,
    mode: Mode,
) -> Result<Value> {
    finish_resolved(root, workspace, ticket, mode, |source| {
        if mode == Mode::Historical {
            if let Some(point) =
                carry::historical_challenge(root, workspace, source.settings, challenge)?
            {
                return Ok(point);
            }
        }
        source.challenge_point(challenge)
    })
}
fn finish_resolved(
    root: &Path,
    workspace: &Value,
    ticket: Option<Ticket>,
    mode: Mode,
    resolve: impl FnOnce(&HostProof<'_>) -> Result<Point>,
) -> Result<Value> {
    let Some(ticket) = ticket else {
        if fs::symlink_metadata(root.join(DIRECTORY)).is_ok()
            || read_json(&root.join("workspace.json"))?
                .get("receiptContinuity")
                .is_some()
        {
            return Err(fail(
                "continuity was enabled during this legacy read; retry with a baseline",
            ));
        }
        return Ok(Value::Null);
    };
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    carry::recover_locked(root)?;
    let current_settings = Settings::load(&custody)?;
    if current_settings.json() != ticket.settings.json() {
        return Err(fail("custody changed during read"));
    }
    current_settings.check(&workspace::member_path(workspace, "config")?)?;
    let mut source = HostProof::new(root, workspace, &ticket.settings)?;
    let target = resolve(&source)?;
    if carry::finish_historical_locked(root, workspace, &current_settings, &target, mode)? {
        return Ok(target.json());
    }
    finish_locked(&custody, &ticket, &target, mode, &mut source)?;
    Ok(target.json())
}

pub(crate) struct AttemptTicket {
    root: PathBuf,
    workspace: Value,
    ticket: Option<Ticket>,
}
/// Shared submit/retry seam: only direct workspace attempts opt into workspace
/// custody. Standalone clients retain their existing exact-retry behavior.
pub(crate) fn begin_attempt(attempt: &Path) -> Result<Option<AttemptTicket>> {
    let attempt = crate::absolute(attempt)?;
    let Some(parent) = attempt.parent() else {
        return Ok(None);
    };
    let parent = fs::canonicalize(parent).map_err(fail)?;
    if parent.file_name().and_then(|name| name.to_str()) != Some("attempts") {
        return Ok(None);
    }
    let Some(root) = parent.parent() else {
        return Ok(None);
    };
    let root = fs::canonicalize(root).map_err(fail)?;
    match fs::symlink_metadata(root.join("workspace.json")) {
        Err(error)
            if error.kind() == std::io::ErrorKind::NotFound && !root.join(DIRECTORY).exists() =>
        {
            return Ok(None)
        }
        Err(error) => return Err(fail(error)),
        Ok(_) => (),
    }
    // Read custody without changing this request's selected transport. In
    // particular --direct must not acquire a socket as a side effect of loading.
    let workspace = read_json(&root.join("workspace.json"))?;
    if text(&workspace, "type")? != "minidregg-participant-workspace-v1" {
        return Err(fail("unknown workspace manifest version"));
    }
    let ticket = begin(&root, &workspace)?;
    if ticket.is_some() {
        let selected = SOCKET.get().ok_or_else(|| fail("protected workspace receipts require the pinned socket before sending; use workspace recover or --socket"))?;
        if workspace
            .get("socket")
            .and_then(Value::as_str)
            .map(Path::new)
            != Some(selected.as_path())
        {
            return Err(fail(
                "receipt transport differs from pinned workspace socket",
            ));
        }
    }
    Ok(Some(AttemptTicket {
        root,
        workspace,
        ticket,
    }))
}
pub(crate) fn finish_attempt(
    attempt: Option<AttemptTicket>,
    outcome: &Value,
    replay: bool,
) -> Result<()> {
    let Some(attempt) = attempt else {
        return Ok(());
    };
    if outcome["type"].as_str() != Some("confirmed") {
        return Ok(());
    }
    // Legacy workspaces still complete through finish_resolved so concurrent
    // enablement cannot create an unguarded success after the first trust point.
    let result = (|| {
        let confirmation = outcome["confirmation"].as_str();
        if attempt.ticket.is_some() && !matches!(confirmation, Some("installed" | "replayed")) {
            return Err(fail("confirmed outcome lacks a known receipt kind"));
        }
        let mode = if replay || confirmation == Some("replayed") {
            Mode::ReceiptReplay
        } else {
            Mode::Ordinary
        };
        finish_resolved(
            &attempt.root,
            &attempt.workspace,
            attempt.ticket,
            mode,
            |_| {
                Point::parse(
                    &json!({"height":outcome["acceptedCount"],"worldRoot":outcome["worldRoot"]}),
                )
            },
        )?;
        Ok(())
    })();
    result.map_err(|error: String| format!("{error}; receipt acknowledgment refused, but mutation may already be accepted; retain the exact attempt and recover by lookup"))
}

pub(crate) fn initialize(
    root: &Path,
    workspace: &Value,
    verifier: Option<&Path>,
    read: impl FnOnce() -> Result<Value>,
) -> Result<Value> {
    let custody = root.join(DIRECTORY);
    if workspace.get("freshContinuity").is_some()
        || fs::symlink_metadata(root.join(fresh::RECORD)).is_ok()
    {
        return Err(fail(
            "fresh enrollment must finish its retained onboarding candidate",
        ));
    }
    if workspace.get("receiptContinuity").is_some() || fs::symlink_metadata(&custody).is_ok() {
        return Err(fail("custody already exists, possibly incomplete; restore it instead of trusting a new endpoint"));
    }
    let selected = verifier
        .map(Path::to_path_buf)
        .unwrap_or(workspace::workspace_host(workspace)?);
    if selected.as_os_str().is_empty() {
        return Err(fail("remote workspace requires --verifier LOCAL-HOST"));
    }
    let verifier = crate::absolute(&selected)?;
    let config = workspace::member_path(workspace, "config")?;
    let settings = Settings {
        identity: local_identity(&verifier, &config)?,
        verifier_sha256: crate::host_image_sha256(&verifier)?,
        verifier,
    };
    // The only operation allowed to trust a first endpoint. No value is exposed
    // until its proof and both custody files have reached durable storage.
    let challenge = read()?;
    let mut source = HostProof::new(root, workspace, &settings)?;
    let target = source.challenge_point(&challenge)?;
    let (verified, complete) = source.verified_hop(None, &target)?;
    if !complete || verified != target {
        return Err(fail("bootstrap did not verify exact signed read point"));
    }
    fs::DirBuilder::new()
        .mode(0o700)
        .create(&custody)
        .map_err(fail)?;
    directory(root)?.sync_all().map_err(fail)?;
    let _lock = lock(&custody)?;
    persist(&custody, &settings, &verified)?;
    save(&custody, "enabled.json", &settings.json())?;
    let mut manifest = read_json(&root.join("workspace.json"))?;
    if manifest != *workspace {
        return Err(fail(
            "workspace changed during initialization; custody retained",
        ));
    }
    manifest["receiptContinuity"] = json!(ALGORITHM);
    save(root, "workspace.json", &manifest)?;
    Ok(json!({"type":"minidregg-receipt-continuity-initialized-v1",
        "identity":settings.identity,"point":target.json()}))
}
/// Explicitly repin an upgraded local verifier without resetting first trust.
pub(crate) fn replace_verifier(root: &Path, workspace: &Value, verifier: &Path) -> Result<Value> {
    let custody = root.join(DIRECTORY);
    let _lock = lock(&custody)?;
    carry::recover_locked(root)?;
    if read_json(&root.join("workspace.json"))? != *workspace {
        return Err(fail(
            "workspace migrated; reload before upgrading its verifier",
        ));
    }
    let old = Settings::load(&custody)?;
    let retained = anchor(&custody, &old)?;
    let verifier = crate::absolute(verifier)?;
    let config = workspace::member_path(workspace, "config")?;
    let replacement = Settings {
        identity: local_identity(&verifier, &config)?,
        verifier_sha256: crate::host_image_sha256(&verifier)?,
        verifier,
    };
    if replacement.identity != old.identity {
        return Err(fail("replacement verifier changes deployment identity"));
    }
    let (chain, siblings) = retained
        .witness
        .as_ref()
        .ok_or_else(|| fail("anchor lacks authenticated opening"))?;
    let query = json!({"identity":old.identity,"from":retained.json(),"target":retained.json(),
        "fromChain":chain,"fromSiblings":siblings});
    let response = json!({"identity":old.identity,"from":retained.json(),"to":retained.json(),
        "startChain":chain,"endChain":chain,"fromSiblings":siblings,"toSiblings":siblings,
        "suffix":[],"complete":true});
    let source = HostProof::new(root, workspace, &replacement)?;
    let (verified, complete) =
        source.verify_response(&query, &serde_json::to_vec(&response).map_err(fail)?)?;
    if !complete || verified != retained {
        return Err(fail("replacement verifier does not accept retained anchor"));
    }
    save(&custody, "enabled.json", &replacement.json())?;
    Ok(
        json!({"type":"minidregg-receipt-continuity-verifier-updated-v1",
        "identity":replacement.identity,"point":retained.json(),"verifierSha256":replacement.verifier_sha256}),
    )
}
pub(crate) fn check_retained(
    root: &Path,
    workspace: &Value,
    attempt: &Path,
    historical: bool,
) -> Result<Value> {
    let ticket = begin(root, workspace)?
        .ok_or_else(|| fail("initialize continuity before checking retained reads"))?;
    let attempt = fs::canonicalize(attempt).map_err(fail)?;
    if attempt.parent()
        != Some(
            fs::canonicalize(root.join("attempts"))
                .map_err(fail)?
                .as_path(),
        )
    {
        return Err(fail(
            "retained read must be a direct child of workspace attempts",
        ));
    }
    let challenge = read_json_mode(&attempt.join("challenge.json"), false)?;
    let point = finish(
        root,
        workspace,
        Some(ticket),
        &challenge,
        if historical {
            Mode::Historical
        } else {
            Mode::Ordinary
        },
    )?;
    Ok(
        json!({"type":"minidregg-receipt-continuity-checked-v1","historical":historical,"point":point}),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::{symlink, PermissionsExt};

    struct Temp(PathBuf);
    impl Temp {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "mini-continuity-test-{}-{}",
                std::process::id(),
                workspace::random_nonce().unwrap()
            ));
            fs::DirBuilder::new().mode(0o700).create(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Temp {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }
    fn point(height: u64) -> Point {
        Point {
            height: height.to_string(),
            world_root: (height * 17).to_string(),
            witness: Some(((height * 7).to_string(), vec!["3".into()])),
        }
    }
    fn settings() -> Settings {
        Settings {
            identity: json!({"algorithm":ALGORITHM,"domain":"1","semantics":"2","expectedSeed":"3"}),
            verifier: PathBuf::from("/unused-test-verifier"),
            verifier_sha256: "test".into(),
        }
    }
    fn setup(height: u64) -> (Temp, Ticket) {
        let root = Temp::new();
        let ticket = Ticket {
            baseline: point(height),
            settings: settings(),
        };
        persist(&root.0, &ticket.settings, &ticket.baseline).unwrap();
        save(&root.0, "enabled.json", &ticket.settings.json()).unwrap();
        (root, ticket)
    }
    struct Proof {
        calls: usize,
        reject: bool,
        page: Option<Point>,
    }
    impl Proof {
        fn good() -> Self {
            Self {
                calls: 0,
                reject: false,
                page: None,
            }
        }
    }
    impl ProofSource for Proof {
        fn verified_hop(&mut self, from: Option<&Point>, target: &Point) -> Result<(Point, bool)> {
            self.calls += 1;
            if self.reject {
                return Err(fail("local verifier rejected tampered proof"));
            }
            assert!(from.is_some());
            if let Some(page) = self.page.take() {
                self.reject = true;
                return Ok((page, false));
            }
            Ok((point(target.height.parse().unwrap()), true))
        }
    }
    fn bytes(root: &Path) -> Vec<u8> {
        fs::read(root.join("anchor.json")).unwrap()
    }

    #[test]
    fn ordinary_lower_and_same_height_forks_fail_before_proof() {
        let (root, ticket) = setup(10);
        let original = bytes(&root.0);
        let mut proof = Proof::good();
        assert!(finish_locked(&root.0, &ticket, &point(9), Mode::Ordinary, &mut proof).is_err());
        let mut fork = point(10);
        fork.world_root = "999".into();
        assert!(finish_locked(&root.0, &ticket, &fork, Mode::Ordinary, &mut proof).is_err());
        assert_eq!(proof.calls, 0);
        assert_eq!(bytes(&root.0), original);
    }

    #[test]
    fn historical_needs_verified_prefix_and_never_changes_anchor() {
        let (root, ticket) = setup(10);
        let original = bytes(&root.0);
        let mut proof = Proof::good();
        finish_locked(&root.0, &ticket, &point(3), Mode::Historical, &mut proof).unwrap();
        assert_eq!(proof.calls, 1);
        assert_eq!(bytes(&root.0), original);
        proof.reject = true;
        assert!(finish_locked(&root.0, &ticket, &point(4), Mode::Historical, &mut proof).is_err());
        assert!(finish_locked(&root.0, &ticket, &point(11), Mode::Historical, &mut proof).is_err());
        assert_eq!(bytes(&root.0), original);
    }

    #[test]
    fn exact_receipt_replay_can_be_historical_or_advance_without_downgrade() {
        let (root, ticket) = setup(5);
        let original = bytes(&root.0);
        finish_locked(
            &root.0,
            &ticket,
            &point(3),
            Mode::ReceiptReplay,
            &mut Proof::good(),
        )
        .unwrap();
        assert_eq!(bytes(&root.0), original);
        finish_locked(
            &root.0,
            &ticket,
            &point(7),
            Mode::ReceiptReplay,
            &mut Proof::good(),
        )
        .unwrap();
        assert_eq!(anchor(&root.0, &ticket.settings).unwrap(), point(7));
    }

    #[test]
    fn tampered_proof_verdict_cannot_persist_or_acknowledge() {
        let (root, ticket) = setup(1);
        let original = bytes(&root.0);
        let mut proof = Proof::good();
        proof.reject = true;
        assert!(finish_locked(&root.0, &ticket, &point(3), Mode::Ordinary, &mut proof).is_err());
        assert_eq!(bytes(&root.0), original);
    }

    #[test]
    fn interrupted_pagination_retains_only_verified_progress() {
        let (root, ticket) = setup(1);
        let mut proof = Proof::good();
        proof.page = Some(point(2));
        assert!(finish_locked(&root.0, &ticket, &point(3), Mode::Ordinary, &mut proof).is_err());
        let saved = anchor(&root.0, &ticket.settings).unwrap();
        assert_eq!(saved, point(2));
        assert_eq!(saved.witness, point(2).witness);
        assert_eq!(proof.calls, 2);
    }

    #[test]
    fn out_of_order_completion_proves_to_current_without_downgrade() {
        let (root, first) = setup(1);
        let later = Ticket {
            baseline: first.baseline.clone(),
            settings: first.settings.clone(),
        };
        finish_locked(
            &root.0,
            &later,
            &point(5),
            Mode::Ordinary,
            &mut Proof::good(),
        )
        .unwrap();
        let original = bytes(&root.0);
        let mut proof = Proof::good();
        finish_locked(&root.0, &first, &point(3), Mode::Ordinary, &mut proof).unwrap();
        assert_eq!(proof.calls, 1);
        assert_eq!(bytes(&root.0), original);
        let mut fork = point(5);
        fork.world_root = "666".into();
        assert!(finish_locked(&root.0, &first, &fork, Mode::Ordinary, &mut proof).is_err());
    }

    #[test]
    fn anchor_loss_incomplete_enablement_and_identity_change_fail_closed() {
        let (root, ticket) = setup(1);
        fs::remove_file(root.0.join("anchor.json")).unwrap();
        assert!(anchor(&root.0, &ticket.settings)
            .unwrap_err()
            .contains("missing or corrupt"));
        persist(&root.0, &ticket.settings, &ticket.baseline).unwrap();
        let mut other = settings();
        other.identity["expectedSeed"] = json!("4");
        assert!(anchor(&root.0, &other).is_err());
        fs::remove_file(root.0.join("enabled.json")).unwrap();
        assert!(Settings::load(&root.0).is_err());
    }

    #[test]
    fn custody_refuses_symlinks_public_files_and_hard_links() {
        let (root, ticket) = setup(1);
        let other = Temp::new();
        symlink(&root.0, other.0.join("alias")).unwrap();
        assert!(directory(&other.0.join("alias")).is_err());
        symlink(root.0.join("anchor.json"), other.0.join("alias.json")).unwrap();
        assert!(read_json(&other.0.join("alias.json")).is_err());
        symlink(root.0.join("anchor.json"), root.0.join("lock")).unwrap();
        assert!(lock(&root.0).is_err());
        fs::set_permissions(
            root.0.join("anchor.json"),
            fs::Permissions::from_mode(0o644),
        )
        .unwrap();
        assert!(anchor(&root.0, &ticket.settings).is_err());
        fs::set_permissions(
            root.0.join("anchor.json"),
            fs::Permissions::from_mode(0o600),
        )
        .unwrap();
        fs::hard_link(root.0.join("anchor.json"), other.0.join("hard.json")).unwrap();
        assert!(anchor(&root.0, &ticket.settings).is_err());
    }

    #[test]
    fn malformed_or_oversized_proof_is_bounded_before_verifier() {
        let mut response = json!({"from":point(1).json(),"to":point(2).json(),"startChain":"1","endChain":"2",
            "suffix":[],"fromSiblings":[],"toSiblings":[]});
        bounded_response(&response).unwrap();
        response["suffix"] = json!(vec!["1"; 4097]);
        assert!(bounded_response(&response).is_err());
        response["suffix"] = json!(["01"]);
        assert!(bounded_response(&response).is_err());
        assert!(Point::parse(&json!({"height":1,"worldRoot":"1"})).is_err());
        assert!(Point::parse(&json!({"height":"01","worldRoot":"1"})).is_err());
    }

    #[test]
    fn attempt_alias_cannot_bypass_workspace_custody() {
        let root = Temp::new();
        fs::DirBuilder::new()
            .mode(0o700)
            .create(root.0.join("attempts"))
            .unwrap();
        symlink(root.0.join("attempts"), root.0.join("alias")).unwrap();
        let mut manifest = json!({"type":"minidregg-participant-workspace-v1"});
        save(&root.0, "workspace.json", &manifest).unwrap();
        let aliased = root.0.join("alias/not-sent");
        assert!(begin_attempt(&aliased).unwrap().is_some());
        manifest["receiptContinuity"] = json!(ALGORITHM);
        save(&root.0, "workspace.json", &manifest).unwrap();
        assert!(begin_attempt(&aliased)
            .err()
            .unwrap()
            .contains("directory is missing"));
        assert!(!aliased.exists());
    }

    #[test]
    fn removing_custody_directory_cannot_disable_enabled_workspace() {
        let root = Temp::new();
        let enabled = json!({"receiptContinuity":ALGORITHM});
        save(&root.0, "workspace.json", &enabled).unwrap();
        // The stale in-memory manifest of a long-lived shell cannot disable it either.
        assert!(begin(&root.0, &json!({}))
            .err()
            .unwrap()
            .contains("directory is missing"));
        assert!(begin(&root.0, &enabled)
            .err()
            .unwrap()
            .contains("directory is missing"));
        assert!(initialize(&root.0, &enabled, None, || panic!("must not bootstrap")).is_err());
        let custody = root.0.join(DIRECTORY);
        fs::DirBuilder::new().mode(0o700).create(&custody).unwrap();
        assert!(finish(&root.0, &json!({}), None, &point(1).json(), Mode::Ordinary).is_err());
    }

    #[test]
    fn crash_child() {
        let Ok(root) = std::env::var("MINI_CONTINUITY_CRASH_ROOT") else {
            return;
        };
        let selected = std::env::var("MINI_CONTINUITY_CRASH_STAGE")
            .unwrap()
            .parse::<u8>()
            .unwrap();
        let value = json!({"identity":settings().identity,"point":point(2).json(),"chain":"14","siblings":["3"]});
        save_with(Path::new(&root), "anchor.json", &value, |stage| {
            if stage as u8 == selected {
                std::process::exit(73);
            }
            Ok(())
        })
        .unwrap();
        panic!("crash failpoint did not execute");
    }

    #[test]
    fn process_crashes_preserve_old_or_complete_new_anchor() {
        for stage in [
            SaveStage::BeforeFileSync,
            SaveStage::BeforeRename,
            SaveStage::AfterRename,
            SaveStage::AfterDirectorySync,
        ] {
            let (root, ticket) = setup(1);
            let status = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "receipt_continuity::tests::crash_child"])
                .env("MINI_CONTINUITY_CRASH_ROOT", &root.0)
                .env("MINI_CONTINUITY_CRASH_STAGE", (stage as u8).to_string())
                .output()
                .unwrap()
                .status;
            assert_eq!(status.code(), Some(73));
            let expected = if matches!(stage, SaveStage::BeforeFileSync | SaveStage::BeforeRename) {
                1
            } else {
                2
            };
            assert_eq!(anchor(&root.0, &ticket.settings).unwrap(), point(expected));
            // Crash recovery never consumes leftover temporary files.
            assert!(Settings::load(&root.0).is_ok());
        }
    }

    #[test]
    fn concurrent_process_child() {
        let Ok(root) = std::env::var("MINI_CONTINUITY_CONCURRENT_ROOT") else {
            return;
        };
        let target = std::env::var("MINI_CONTINUITY_TARGET")
            .unwrap()
            .parse()
            .unwrap();
        let root = Path::new(&root);
        // Both requests captured this baseline before either network read completed.
        let ticket = Ticket {
            baseline: point(1),
            settings: settings(),
        };
        let _lock = lock(root).unwrap();
        finish_locked(
            root,
            &ticket,
            &point(target),
            Mode::Ordinary,
            &mut Proof::good(),
        )
        .unwrap();
    }

    #[test]
    fn concurrent_process_requests_do_not_lose_progress() {
        let (root, ticket) = setup(1);
        let mut children = Vec::new();
        for height in [9, 3, 8, 4] {
            children.push(
                Command::new(std::env::current_exe().unwrap())
                    .args([
                        "--exact",
                        "receipt_continuity::tests::concurrent_process_child",
                    ])
                    .env("MINI_CONTINUITY_CONCURRENT_ROOT", &root.0)
                    .env("MINI_CONTINUITY_TARGET", height.to_string())
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null())
                    .spawn()
                    .unwrap(),
            );
        }
        for mut child in children {
            assert!(child.wait().unwrap().success());
        }
        assert_eq!(anchor(&root.0, &ticket.settings).unwrap(), point(9));
    }
}
