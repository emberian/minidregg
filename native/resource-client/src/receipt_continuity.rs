//! Durable receipt continuity custody. Lean owns every proof decision; this module
//! only bounds transport, serializes completions, and durably remembers verified points.
pub(crate) mod carry;
use crate::{workspace, Result, SOCKET};
use mini_sdk::durable::{Perm, Stage};
use mini_sdk::lock::{Create, Lease, LockError, Wait};
use serde_json::{json, Value};
use std::cmp::Ordering;
use std::fs::{self, File, OpenOptions};
use std::io::Read;
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
    if !mini_sdk::decimal::is_canonical_max(value, 80)
    {
        return Err(fail(
            "expected a canonical decimal string of at most 80 digits",
        ));
    }
    Ok(())
}
use mini_sdk::decimal::compare;

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
    if !(if directory {
        mini_sdk::private::dir_ok(&meta)
    } else {
        mini_sdk::private::file_ok(&meta)
    }) {
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
        if !meta.is_file() || !mini_sdk::private::owned(&meta) {
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
    crate::create_private(path, bytes).map_err(fail)
}
fn lock(root: &Path) -> Result<Lease> {
    lock_named(root, "lock")
}
fn lock_named(root: &Path, name: &str) -> Result<Lease> {
    let _directory = directory(root)?;
    // Separate open descriptions also serialize threads in this process.
    Lease::acquire(
        &root.join(name),
        Create::Yes,
        Wait::Poll { tries: 100, interval: std::time::Duration::from_millis(50) },
    )
    .map_err(|error| match error {
        LockError::Busy => fail("another completion owns the anchor; retry this read"),
        LockError::Unsafe => fail("custody path must be owner-private, regular, and unlinked elsewhere"),
        LockError::Io(error) => fail(error),
    })
}
fn save_with(
    root: &Path,
    name: &str,
    value: &Value,
    mut stage: impl FnMut(Stage) -> std::io::Result<()>,
) -> Result<()> {
    let parent = directory(root)?;
    let bytes = serde_json::to_vec(value).map_err(fail)?;
    if bytes.len() as u64 > MAX_JSON {
        return Err(fail("persisted JSON exceeds custody bound"));
    }
    mini_sdk::durable::replace_with(&root.join(name), &bytes, Perm::Private, &mut |at| {
        if at == Stage::BeforeCommit {
            let named = fs::symlink_metadata(root)?;
            let opened = parent.metadata()?;
            if (named.dev(), named.ino()) != (opened.dev(), opened.ino()) {
                return Err(std::io::Error::other("custody directory changed"));
            }
        }
        stage(at)
    })
    .map_err(fail)
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
        if checked_identity(&self.verifier, &self.verifier_sha256, config)? != self.identity {
            return Err(fail("configured deployment identity changed"));
        }
        Ok(())
    }
}

/// `profile` is a pure function of the verifier image and the config bytes.
/// Within one process, an identical (image SHA-256, config bytes) pair
/// reuses the identity the verifier already printed instead of spawning the
/// Lean verifier again for every check of every hop. A changed image or a
/// changed config byte misses the cache and runs `profile` again.
static PROFILED: std::sync::Mutex<Vec<(PathBuf, String, Vec<u8>, Value)>> =
    std::sync::Mutex::new(Vec::new());

fn checked_identity(verifier: &Path, verifier_sha256: &str, config: &Path) -> Result<Value> {
    let bytes = crate::agent_reserve::bounded(config, MAX_JSON as usize)?;
    if let Some((_, _, _, identity)) = PROFILED
        .lock()
        .map_err(|_| fail("verifier profile cache poisoned"))?
        .iter()
        .find(|(path, sha, seen, _)| path == verifier && sha == verifier_sha256 && *seen == bytes)
    {
        return Ok(identity.clone());
    }
    let identity = local_identity(verifier, verifier_sha256, config, &bytes)?;
    // Execution used these exact sealed bytes on Linux. Retain the pathname
    // fence as well; a changed configuration does not populate this cache key.
    if crate::agent_reserve::bounded(config, MAX_JSON as usize)? == bytes {
        let mut cache = PROFILED
            .lock()
            .map_err(|_| fail("verifier profile cache poisoned"))?;
        cache.retain(|(path, _, _, _)| path != verifier);
        cache.push((verifier.to_path_buf(), verifier_sha256.to_owned(), bytes, identity.clone()));
    }
    Ok(identity)
}
fn pinned_verifier(verifier: &Path, verifier_sha256: &str, config: &Path,
    config_bytes: &[u8]) -> Result<crate::transport::PinnedLocalInvocation> {
    // The verifier pin arrives in settings a person writes, not from the Host.
    let expected: [u8; 32] = crate::decode_hex(verifier_sha256).map_err(fail)?
        .try_into().map_err(|_| fail("local verifier pin must be exactly 32 bytes"))?;
    crate::transport::PinnedLocalInvocation::new(verifier, config, &expected, config_bytes)
        .map_err(fail)
}
fn local_identity(verifier: &Path, verifier_sha256: &str, config: &Path,
    config_bytes: &[u8]) -> Result<Value> {
    let invocation = pinned_verifier(verifier, verifier_sha256, config, config_bytes)?;
    let started = std::time::Instant::now();
    let output = invocation.output(&[std::ffi::OsStr::new("profile")]).map_err(fail)?;
    crate::trace::record("spawn", "verifier profile", 0, output.stdout.len(), started);
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
    let invocation = pinned_verifier(&settings.verifier, &settings.verifier_sha256, &config, &config_bytes)?;
    let status = invocation.status(&[std::ffi::OsStr::new(verb), std::ffi::OsStr::new(kind),
        input_path.as_os_str(), output_path.as_os_str()]).map_err(fail)?;
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
    // One immutable executable/config pair for the entire multi-hop proof, sealed at its first
    // use: a read whose point is already known (`POINTS`) and needs no hop spawns nothing.
    invocation: std::cell::OnceCell<crate::transport::PinnedLocalInvocation>,
    config_bytes: Vec<u8>,
}

/// Points this process's verifier derived, by everything `continuity-point` reads: the verifier
/// image pin, the exact config bytes, and the challenge's `domain`, `semantics`, `height` and
/// `worldRoot` (`Compiler/ReceiptContinuityIO.challengePointJson` reads those four fields and the
/// config's domain, semantics and genesis height, nothing else; the nonce and the rest of the
/// challenge do not enter). A member's warm resident shell reads the same head again and again
/// while nothing is written: those reads get the point the verifier already derived instead of
/// a 185 MB process start per read. A changed field, image or config byte is a miss and runs the
/// verifier. A refused point is never kept.
static POINTS: std::sync::Mutex<Vec<(Value, Point)>> = std::sync::Mutex::new(Vec::new());
const POINTS_KEPT: usize = 16;

impl HostProof<'_> {
    fn invocation(&self) -> Result<&crate::transport::PinnedLocalInvocation> {
        if let Some(invocation) = self.invocation.get() {
            return Ok(invocation);
        }
        let config = workspace::member_path(self.workspace, "config")?;
        let invocation = pinned_verifier(&self.settings.verifier, &self.settings.verifier_sha256,
            &config, &self.config_bytes)?;
        Ok(self.invocation.get_or_init(|| invocation))
    }
    fn point_key(&self, challenge: &Value) -> Value {
        json!({"verifier":self.settings.verifier_sha256,
            "config":crate::hex(&<[u8; 32]>::from(<sha2::Sha256 as sha2::Digest>::digest(&self.config_bytes))),
            "domain":challenge.get("domain"),"semantics":challenge.get("semantics"),
            "height":challenge.get("height"),"worldRoot":challenge.get("worldRoot")})
    }
    fn check_launch(&self, config: &Path) -> Result<()> {
        if crate::agent_reserve::bounded(config, MAX_JSON as usize)? != self.config_bytes {
            return Err(fail("continuity verifier config changed during proof"));
        }
        self.settings.check(config)
    }
    fn challenge_point(&self, challenge: &Value) -> Result<Point> {
        let key = self.point_key(challenge);
        if let Some((_, point)) = POINTS.lock().map_err(|_| fail("continuity point cache poisoned"))?
            .iter().find(|(seen, _)| *seen == key)
        {
            return Ok(point.clone());
        }
        let point = self.derive_point(challenge)?;
        let mut kept = POINTS.lock().map_err(|_| fail("continuity point cache poisoned"))?;
        if kept.len() >= POINTS_KEPT {
            kept.remove(0);
        }
        kept.push((key, point.clone()));
        Ok(point)
    }
    fn derive_point(&self, challenge: &Value) -> Result<Point> {
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
        self.check_launch(&config)?;
        // Challenge heights include genesisHeight. Lean converts them to receipt
        // accepted-count coordinates and binds domain/semantics to this config.
        let started = std::time::Instant::now();
        let result = self.invocation()?.output(&[std::ffi::OsStr::new("continuity-point"),
            input.as_os_str(), output.as_os_str()]).map_err(fail)?;
        crate::trace::record("spawn", "verifier continuity-point", 0, result.stdout.len(), started);
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
        let config = workspace::member_path(workspace, "config")?;
        let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
        Ok(HostProof {
            workspace,
            settings,
            scratch,
            invocation: std::cell::OnceCell::new(),
            config_bytes,
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
        self.check_launch(&config)?;
        let started = std::time::Instant::now();
        let result = self.invocation()?.output(&[std::ffi::OsStr::new("continuity-verify"),
            request_path.as_os_str(), response_path.as_os_str(), result_path.as_os_str()])
            .map_err(fail)?;
        crate::trace::record("spawn", "verifier continuity-verify", 0, result.stdout.len(), started);
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
        record_verified_witness(
            &response["from"]["height"],
            &response["from"]["worldRoot"],
            &response["startChain"],
            &response["fromSiblings"],
        );
        record_verified_witness(
            &response["to"]["height"],
            &response["to"]["worldRoot"],
            &response["endChain"],
            &response["toSiblings"],
        );
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
        let frame = crate::session_invoke(&host, socket, &config, mini_sdk::host_operations::RECEIPT_CONTINUITY, &bytes)?;
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
    attempt: PathBuf,
}

/// Attempts whose confirmed outcome this process already carried through
/// `finish_attempt`, with that exact outcome. Recording the same confirmed
/// point again in the same process would repeat the lock, verifier checks
/// and writes for an anchor that is already durable.
static FINISHED_ATTEMPTS: std::sync::Mutex<Vec<(PathBuf, Value)>> =
    std::sync::Mutex::new(Vec::new());

/// The attempt path with its parent canonicalized, as `begin_attempt` names it.
fn canonical_attempt(attempt: &Path) -> Result<PathBuf> {
    let attempt = crate::absolute(attempt)?;
    let parent = attempt.parent().ok_or_else(|| fail("attempt has no parent"))?;
    let name = attempt.file_name().ok_or_else(|| fail("attempt has no name"))?;
    Ok(fs::canonicalize(parent).map_err(fail)?.join(name))
}

/// Whether this process already finished continuity for exactly this
/// confirmed outcome of this attempt.
pub(crate) fn finished_in_process(attempt: &Path, outcome: &Value) -> Result<bool> {
    let attempt = canonical_attempt(attempt)?;
    Ok(FINISHED_ATTEMPTS
        .lock()
        .map_err(|_| fail("finished attempt record poisoned"))?
        .iter()
        .any(|(path, value)| *path == attempt && value == outcome))
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
        attempt: parent.join(attempt.file_name().ok_or_else(|| fail("attempt has no name"))?),
    }))
}
/// The native recovered variant is exact accepted history after readback,
/// but it is not evidence that this response won a fresh CAS. Check its
/// lineage like replay, without lowering the durable anchor.
fn receipt_mode(confirmation: Option<&str>, protected: bool, replay: bool) -> Result<Mode> {
    if protected && !matches!(confirmation,
        Some("installed" | "recoveredAfterUncertainResponse" | "replayed")) {
        return Err(fail("confirmed outcome lacks a known receipt kind"));
    }
    Ok(if replay || matches!(confirmation,
        Some("replayed" | "recoveredAfterUncertainResponse")) {
        Mode::ReceiptReplay
    } else {
        Mode::Ordinary
    })
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
        let mode = receipt_mode(outcome["confirmation"].as_str(), attempt.ticket.is_some(), replay)?;
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
        retain_attempt_witness_if_matching(&attempt.root, &attempt.attempt, outcome);
        FINISHED_ATTEMPTS
            .lock()
            .map_err(|_| fail("finished attempt record poisoned"))?
            .push((attempt.attempt, outcome.clone()));
        Ok(())
    })();
    result.map_err(|error: String| format!("{error}; receipt acknowledgment refused, but mutation may already be accepted; retain the exact attempt and recover by lookup"))
}

static VERIFIED_WITNESSES: std::sync::Mutex<Vec<(String, String, String, Value)>> =
    std::sync::Mutex::new(Vec::new());

fn record_verified_witness(height: &Value, world_root: &Value, chain: &Value, siblings: &Value) {
    let (Some(h), Some(r), Some(c)) = (height.as_str(), world_root.as_str(), chain.as_str()) else {
        return;
    };
    if !siblings.is_array() {
        return;
    }
    if let Ok(mut cache) = VERIFIED_WITNESSES.lock() {
        cache.retain(|(eh, er, _, _)| !(eh == h && er == r));
        cache.push((h.to_owned(), r.to_owned(), c.to_owned(), siblings.clone()));
    }
}

fn retain_attempt_witness_if_matching(root: &Path, attempt: &Path, outcome: &Value) {
    let (Some(height), Some(world_root)) = (
        outcome["acceptedCount"].as_str(),
        outcome["worldRoot"].as_str(),
    ) else {
        return;
    };
    let mut found: Option<(Value, Value)> = None;
    if let Ok(anchor_val) = read_json(&root.join(DIRECTORY).join("anchor.json")) {
        if anchor_val["point"]["height"].as_str() == Some(height)
            && anchor_val["point"]["worldRoot"].as_str() == Some(world_root)
            && anchor_val.get("chain").is_some()
            && anchor_val.get("siblings").is_some()
        {
            found = Some((anchor_val["chain"].clone(), anchor_val["siblings"].clone()));
        }
    }
    if found.is_none() {
        if let Ok(cache) = VERIFIED_WITNESSES.lock() {
            if let Some((_, _, chain, siblings)) = cache
                .iter()
                .rev()
                .find(|(h, r, _, _)| h == height && r == world_root)
            {
                found = Some((json!(chain), siblings.clone()));
            }
        }
    }
    if let Some((chain, siblings)) = found {
        let witness = json!({
            "type": "minidregg-world-root-opening-v1",
            "height": height,
            "worldRoot": world_root,
            "chain": chain,
            "siblings": siblings,
        });
        if let Ok(bytes) = serde_json::to_vec(&witness) {
            let _ = crate::fsio::replace_private(&attempt.join("continuity-witness.json"), &bytes);
        }
    }
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
    let verifier_sha256 = crate::host_image_sha256(&verifier)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let settings = Settings {
        identity: local_identity(&verifier, &verifier_sha256, &config, &config_bytes)?,
        verifier_sha256,
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
    crate::fsio::create_private_dir(&custody)?;
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
    let verifier_sha256 = crate::host_image_sha256(&verifier)?;
    let config_bytes = crate::agent_reserve::bounded(&config, MAX_JSON as usize)?;
    let replacement = Settings {
        identity: local_identity(&verifier, &verifier_sha256, &config, &config_bytes)?,
        verifier_sha256,
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
    retain_attempt_witness_if_matching(
        root,
        &attempt,
        &json!({"acceptedCount": point["height"], "worldRoot": point["worldRoot"]}),
    );
    Ok(
        json!({"type":"minidregg-receipt-continuity-checked-v1","historical":historical,"point":point}),
    )
}

// ------------------------------------------------------------------ deterministic cSHAKE256 world-root opening verifier (op 151)

/// `PersistedCodecTags.world_root_v2` (`Kernel/WorldRoot.lean` `worldCustomization`).
pub(crate) const WORLD_ROOT_CUSTOMIZATION: &[u8] = b"DREGG.WORLD-ROOT/v3";
/// `PersistedCodecTags.native_host_system_v1` (`Compiler/DurableCheckpointCodec.lean` `systemCustomization`).
pub(crate) const SYSTEM_LEAF_CUSTOMIZATION: &[u8] = b"DREGG.NATIVE-HOST.SYSTEM/v2";
/// `Kernel/WorldRoot.lean` `logCustomization`.
pub(crate) const LOG_CHAIN_CUSTOMIZATION: &[u8] = b"DREGG.LOG/v1";

/// One step of the `AuthTrie.climb` walk from `.leaf .system (systemLeaf height chain)` up to `worldRoot`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BranchStep {
    pub step: usize,
    pub depth: usize,
    pub bit: bool,
    pub direction: &'static str,
    pub sibling: String,
    pub sibling_hex: String,
    pub parent: String,
    pub parent_hex: String,
}

/// Deterministic `cSHAKE256` world-root inclusion opening (`Kernel/ReceiptContinuity.lean` `opens_sound`:
/// `ValidOpening ∨ ConcreteCollision`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VerifiedInclusion {
    pub height: String,
    pub world_root: String,
    pub world_root_hex: String,
    pub chain: String,
    pub chain_hex: String,
    pub system_leaf: String,
    pub system_leaf_hex: String,
    pub leaf_node_digest: String,
    pub leaf_node_hex: String,
    pub key_bits_prefix: String,
    pub siblings: Vec<String>,
    pub steps: Vec<BranchStep>,
    pub start_height: Option<String>,
    pub start_world_root: Option<String>,
    pub start_chain: Option<String>,
    pub suffix: Vec<String>,
}

impl VerifiedInclusion {
    pub(crate) fn json(&self) -> Value {
        let steps: Vec<Value> = self
            .steps
            .iter()
            .map(|s| {
                json!({
                    "step": s.step,
                    "depth": s.depth,
                    "bit": u8::from(s.bit),
                    "direction": s.direction,
                    "sibling": s.sibling,
                    "siblingHex": s.sibling_hex,
                    "parent": s.parent,
                    "parentHex": s.parent_hex,
                })
            })
            .collect();
        let mut out = json!({
            "type": "minidregg-world-root-opening-v1",
            "verified": true,
            "soundness": "ValidOpening ∨ ConcreteCollision (cSHAKE256, Kernel.ReceiptContinuity.opens_sound)",
            "height": self.height,
            "worldRoot": self.world_root,
            "worldRootHex": self.world_root_hex,
            "chain": self.chain,
            "chainHex": self.chain_hex,
            "systemLeaf": self.system_leaf,
            "systemLeafHex": self.system_leaf_hex,
            "leafNodeDigest": self.leaf_node_digest,
            "leafNodeHex": self.leaf_node_hex,
            "keyBitsPrefix": self.key_bits_prefix,
            "siblings": self.siblings,
            "steps": steps,
            "suffix": self.suffix,
        });
        if let Some(h) = &self.start_height {
            out["startHeight"] = json!(h);
        }
        if let Some(r) = &self.start_world_root {
            out["startWorldRoot"] = json!(r);
        }
        if let Some(c) = &self.start_chain {
            out["startChain"] = json!(c);
        }
        out
    }
}

fn cshake256_raw32(custom: &[u8], msg: &[u8]) -> [u8; 32] {
    use sha3::digest::{core_api::CoreWrapper, ExtendableOutput, Update, XofReader};
    use sha3::CShake256Core;
    let mut hasher = CoreWrapper::from_core(CShake256Core::new(custom));
    hasher.update(msg);
    let mut out = [0u8; 32];
    XofReader::read(&mut hasher.finalize_xof(), &mut out);
    out
}

/// `Kernel.WorldRoot.cshake256Digest`: 32 bytes from `cSHAKE256("", custom, msg)` read as a
/// little-endian natural (`digestOfBytesLE`), formatted as its canonical decimal string.
pub(crate) fn cshake256_digest_decimal(custom: &[u8], msg: &[u8]) -> String {
    let mut bytes = cshake256_raw32(custom, msg);
    bytes.reverse();
    mini_sdk::decimal::from_be_bytes(&bytes)
}

/// Format a canonical 256-bit decimal digest as 64 lowercase hex characters (big-endian natural).
pub(crate) fn digest_decimal_to_hex(dec: &str) -> Result<String> {
    decimal(dec)?;
    let be = mini_sdk::decimal::to_be_bytes32(dec).map_err(|e| fail(e.0))?;
    Ok(crate::hex(&be))
}

/// `Theory.StreamCodec.encodeNat`: base-255 little-endian digits terminated by `255` (`0xff`).
pub(crate) fn encode_nat_decimal(dec: &str) -> Result<Vec<u8>> {
    decimal(dec)?;
    let mut be = mini_sdk::decimal::to_be_bytes32(dec).map_err(|e| fail(e.0))?;
    if be.iter().all(|b| *b == 0) {
        return Ok(vec![255]);
    }
    let mut out = Vec::with_capacity(34);
    while be.iter().any(|b| *b != 0) {
        let mut rem = 0u32;
        for byte in &mut be {
            let acc = rem * 256 + u32::from(*byte);
            *byte = (acc / 255) as u8;
            rem = acc % 255;
        }
        out.push(rem as u8);
    }
    out.push(255);
    Ok(out)
}

/// `DurableCheckpointCodec.systemLeaf height chain`:
/// `cshake256Digest "DREGG.NATIVE-HOST.SYSTEM/v2" (StreamCodec.nat.encode height ++ digestStream.encode chain)`.
pub(crate) fn system_leaf_digest(height: &str, chain: &str) -> Result<String> {
    let mut msg = encode_nat_decimal(height)?;
    msg.extend(encode_nat_decimal(chain)?);
    Ok(cshake256_digest_decimal(SYSTEM_LEAF_CUSTOMIZATION, &msg))
}

/// `Kernel.WorldRoot.worldDig (.leaf .system v)`:
/// `cshake256Digest "DREGG.WORLD-ROOT/v3" ([1, 0] ++ StreamCodec.nat.encode v.value)`.
pub(crate) fn leaf_system_node_digest(system_leaf: &str) -> Result<String> {
    let mut msg = vec![1u8, 0u8];
    msg.extend(encode_nat_decimal(system_leaf)?);
    Ok(cshake256_digest_decimal(WORLD_ROOT_CUSTOMIZATION, &msg))
}

/// `Kernel.WorldRoot.worldDig (.branch l r)`:
/// `cshake256Digest "DREGG.WORLD-ROOT/v3" ([2] ++ StreamCodec.nat.encode l.value ++ StreamCodec.nat.encode r.value)`.
pub(crate) fn branch_node_digest(left: &str, right: &str) -> Result<String> {
    let mut msg = vec![2u8];
    msg.extend(encode_nat_decimal(left)?);
    msg.extend(encode_nat_decimal(right)?);
    Ok(cshake256_digest_decimal(WORLD_ROOT_CUSTOMIZATION, &msg))
}

/// `Kernel.WorldRoot.chainDigest acc turn`:
/// `cshake256Digest "DREGG.LOG/v1" (digestStream.encode acc ++ digestStream.encode turn)`.
pub(crate) fn chain_step_digest(acc: &str, turn: &str) -> Result<String> {
    let mut msg = encode_nat_decimal(acc)?;
    msg.extend(encode_nat_decimal(turn)?);
    Ok(cshake256_digest_decimal(LOG_CHAIN_CUSTOMIZATION, &msg))
}

/// `Kernel.ReceiptContinuity.chainAfterDigests start suffix`.
pub(crate) fn chain_after_digests(start: &str, suffix: &[String]) -> Result<String> {
    decimal(start)?;
    let mut acc = start.to_owned();
    for turn in suffix {
        acc = chain_step_digest(&acc, turn)?;
    }
    Ok(acc)
}

/// `Kernel.WorldRoot.deployedIx .system`: 256 path bits (`bytesBits` of `cSHAKE256("", "DREGG.WORLD-ROOT/v3", [3, 0])`).
pub(crate) fn deployed_ix_system_bits() -> [bool; 256] {
    let raw = cshake256_raw32(WORLD_ROOT_CUSTOMIZATION, &[3u8, 0u8]);
    let mut bits = [false; 256];
    for (i, byte) in raw.iter().copied().enumerate() {
        for bit in 0..8 {
            bits[i * 8 + bit] = (byte & (128u8 >> bit)) != 0;
        }
    }
    bits
}

/// Deterministically compute the `AuthTrie` root and branch steps from `(height, chain, siblings)`.
pub(crate) fn compute_world_root_from_system_opening(
    height: &str,
    chain: &str,
    siblings: &[String],
) -> Result<VerifiedInclusion> {
    decimal(height)?;
    decimal(chain)?;
    if siblings.len() > 256 {
        return Err(fail("endpoint siblings exceed 256-bit trie depth bound"));
    }
    for sib in siblings {
        decimal(sib)?;
    }
    let system_leaf = system_leaf_digest(height, chain)?;
    let leaf_node_digest = leaf_system_node_digest(&system_leaf)?;
    let bits = deployed_ix_system_bits();
    let mut acc = leaf_node_digest.clone();
    let mut steps = Vec::with_capacity(siblings.len());
    for (step_idx, depth) in (0..siblings.len()).rev().enumerate() {
        let bit = bits[depth];
        let sib = &siblings[depth];
        let parent = if bit {
            branch_node_digest(sib, &acc)?
        } else {
            branch_node_digest(&acc, sib)?
        };
        steps.push(BranchStep {
            step: step_idx + 1,
            depth,
            bit,
            direction: if bit { "right (1)" } else { "left (0)" },
            sibling: sib.clone(),
            sibling_hex: digest_decimal_to_hex(sib)?,
            parent: parent.clone(),
            parent_hex: digest_decimal_to_hex(&parent)?,
        });
        acc = parent;
    }
    let key_bits_prefix = if siblings.is_empty() {
        "root (depth 0)".to_owned()
    } else {
        let mut s = String::from("0b");
        for b in &bits[..siblings.len()] {
            s.push(if *b { '1' } else { '0' });
        }
        s
    };
    Ok(VerifiedInclusion {
        height: height.to_owned(),
        world_root: acc.clone(),
        world_root_hex: digest_decimal_to_hex(&acc)?,
        chain: chain.to_owned(),
        chain_hex: digest_decimal_to_hex(chain)?,
        system_leaf: system_leaf.clone(),
        system_leaf_hex: digest_decimal_to_hex(&system_leaf)?,
        leaf_node_digest: leaf_node_digest.clone(),
        leaf_node_hex: digest_decimal_to_hex(&leaf_node_digest)?,
        key_bits_prefix,
        siblings: siblings.to_vec(),
        steps,
        start_height: None,
        start_world_root: None,
        start_chain: None,
        suffix: Vec::new(),
    })
}

/// Deterministically verify `ReceiptContinuity.opens`: recomputes `systemLeaf(height, chain)` and
/// climbs `siblings` along `deployedIx Key.system`, refusing unless the computed root equals `expected_world_root`.
pub(crate) fn verify_world_root_opening(
    height: &str,
    expected_world_root: &str,
    chain: &str,
    siblings: &[String],
) -> Result<VerifiedInclusion> {
    decimal(expected_world_root)?;
    let computed = compute_world_root_from_system_opening(height, chain, siblings)?;
    if computed.world_root != expected_world_root {
        return Err(fail(format!(
            "world-root inclusion opening refused: computed root {} does not match confirmation worldRoot {}",
            computed.world_root, expected_world_root
        )));
    }
    Ok(computed)
}

fn parse_string_list(value: &Value, key: &str, limit: usize) -> Result<Vec<String>> {
    let arr = value
        .get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| fail(format!("missing {key}")))?;
    if arr.len() > limit {
        return Err(fail(format!("{key} exceeds bound")));
    }
    arr.iter()
        .map(|v| {
            let s = v.as_str().ok_or_else(|| fail(format!("{key} item is not a string")))?;
            decimal(s)?;
            Ok(s.to_owned())
        })
        .collect()
}

/// Offline verification of a retained `inclusion-opening.json` if present in `attempt`.
pub(crate) fn load_verified_attempt_inclusion(
    attempt: &Path,
    expected_height: &str,
    expected_world_root: &str,
) -> Option<Result<VerifiedInclusion>> {
    let path = attempt.join("inclusion-opening.json");
    if !path.is_file() {
        return None;
    }
    Some((|| {
        let value = read_json_mode(&path, false)?;
        let height = text(&value, "height")?;
        let world_root = text(&value, "worldRoot")?;
        if height != expected_height || world_root != expected_world_root {
            return Err(fail(
                "retained inclusion opening point differs from the attempt's confirmation point",
            ));
        }
        let chain = text(&value, "chain")?;
        let siblings = parse_string_list(&value, "siblings", 256)?;
        let mut verified = verify_world_root_opening(height, world_root, chain, &siblings)?;
        if let Some(start_chain) = value.get("startChain").and_then(Value::as_str) {
            decimal(start_chain)?;
            let suffix = parse_string_list(&value, "suffix", MAX_HOPS)?;
            let end = chain_after_digests(start_chain, &suffix)?;
            if end != chain {
                return Err(fail(
                    "retained inclusion opening suffix chain does not fold to endChain",
                ));
            }
            verified.start_chain = Some(start_chain.to_owned());
            verified.suffix = suffix;
            if let (Some(sh), Some(sr)) = (
                value.get("startHeight").and_then(Value::as_str),
                value.get("startWorldRoot").and_then(Value::as_str),
            ) {
                decimal(sh)?;
                decimal(sr)?;
                if let Ok(from_siblings) = parse_string_list(&value, "fromSiblings", 256) {
                    verify_world_root_opening(sh, sr, start_chain, &from_siblings)?;
                }
                verified.start_height = Some(sh.to_owned());
                verified.start_world_root = Some(sr.to_owned());
            }
        }
        Ok(verified)
    })())
}

/// Fetch (if not yet cached) and deterministically verify the `cSHAKE256` world-root inclusion opening
/// (`op 151`) for a confirmed or charged attempt, persisting `attempt/inclusion-opening.json`.
pub(crate) fn verify_attempt_inclusion(
    root: &Path,
    workspace: &Value,
    attempt: &Path,
) -> Result<VerifiedInclusion> {
    let (height_str, world_root_str) = match workspace::retained_attempt_outcome(attempt)? {
        workspace::AttemptOutcome::Confirmed(v) | workspace::AttemptOutcome::Charged(v) => (
            text(&v, "acceptedCount")?.to_owned(),
            text(&v, "worldRoot")?.to_owned(),
        ),
        workspace::AttemptOutcome::Refused => {
            return Err(fail("refused attempt has no confirmation worldRoot to open"))
        }
        workspace::AttemptOutcome::Pending => {
            let witness_file = attempt.join("continuity-witness.json");
            if witness_file.is_file() {
                let val = read_json_mode(&witness_file, false)?;
                (
                    text(&val, "height")?.to_owned(),
                    text(&val, "worldRoot")?.to_owned(),
                )
            } else {
                return Err(fail(
                    "undecided attempt has no confirmation point yet; run lookup or retry first",
                ));
            }
        }
    };
    let height = height_str.as_str();
    let world_root = world_root_str.as_str();
    decimal(height)?;
    decimal(world_root)?;

    let mut last_err: Option<String> = None;

    // 1. Check existing `inclusion-opening.json` or `continuity-witness.json` in `attempt`.
    if let Some(res) = load_verified_attempt_inclusion(attempt, height, world_root) {
        match res {
            Ok(verified) => return Ok(verified),
            Err(err) => last_err = Some(err),
        }
    }
    let witness_file = attempt.join("continuity-witness.json");
    if witness_file.is_file() {
        match (|| -> Result<VerifiedInclusion> {
            let val = read_json_mode(&witness_file, false)?;
            if val.get("height").and_then(Value::as_str) != Some(height)
                || val.get("worldRoot").and_then(Value::as_str) != Some(world_root)
            {
                return Err(fail(
                    "retained continuity witness point differs from the attempt's confirmation point",
                ));
            }
            let chain = text(&val, "chain")?;
            let siblings = parse_string_list(&val, "siblings", 256)?;
            let verified = verify_world_root_opening(height, world_root, chain, &siblings)?;
            let _ = crate::fsio::replace_private(
                &attempt.join("inclusion-opening.json"),
                &serde_json::to_vec(&verified.json()).map_err(fail)?,
            );
            Ok(verified)
        })() {
            Ok(verified) => return Ok(verified),
            Err(err) => last_err = Some(err),
        }
    }

    // 2. Check `receipt-continuity/anchor.json` if it matches this exact confirmation point.
    let anchor_path = root.join(DIRECTORY).join("anchor.json");
    if anchor_path.is_file() {
        if let Ok(anchor_val) = read_json_mode(&anchor_path, false) {
            if anchor_val["point"]["height"].as_str() == Some(height)
                && anchor_val["point"]["worldRoot"].as_str() == Some(world_root)
            {
                match (|| -> Result<VerifiedInclusion> {
                    let chain = text(&anchor_val, "chain")?;
                    let siblings = parse_string_list(&anchor_val, "siblings", 256)?;
                    let verified = verify_world_root_opening(height, world_root, chain, &siblings)?;
                    let _ = crate::fsio::replace_private(
                        &attempt.join("inclusion-opening.json"),
                        &serde_json::to_vec(&verified.json()).map_err(fail)?,
                    );
                    Ok(verified)
                })() {
                    Ok(verified) => return Ok(verified),
                    Err(err) => last_err = Some(err),
                }
            }
        }
    }

    // 3. Query Host `op 151` (`RECEIPT_CONTINUITY`) for the deterministic world-root opening at `(height, worldRoot)`.
    let socket = match SOCKET.get() {
        Some(s) => s,
        None => {
            return Err(last_err.unwrap_or_else(|| {
                fail("no retained world-root opening for this attempt and no Host socket is connected to request op 151")
            }))
        }
    };
    let host = workspace::workspace_host(workspace)?;
    let config = workspace::member_path(workspace, "config")?;
    let id_val = if let Ok(settings) = Settings::load(&root.join(DIRECTORY)) {
        settings.identity
    } else {
        let sha = workspace
            .get("hostSha256")
            .and_then(Value::as_str)
            .map(str::to_owned)
            .unwrap_or_else(|| crate::host_image_sha256(&host).unwrap_or_default());
        checked_identity(&host, &sha, &config)?
    };
    let target = json!({"height": height, "worldRoot": world_root});
    let mut query = json!({"identity": id_val, "from": Value::Null, "target": target});
    if anchor_path.is_file() {
        if let Ok(anchor_val) = read_json_mode(&anchor_path, false) {
            if let (Some(ah), Some(ar), Some(ac), Some(asib)) = (
                anchor_val["point"]["height"].as_str(),
                anchor_val["point"]["worldRoot"].as_str(),
                anchor_val.get("chain").and_then(Value::as_str),
                anchor_val.get("siblings").and_then(Value::as_array),
            ) {
                if compare(ah, height) != Ordering::Greater
                    && compare(&mini_sdk::decimal::add(ah, "4096").unwrap_or_else(|_| height.to_owned()), height)
                        != Ordering::Less
                {
                    query["from"] = json!({"height": ah, "worldRoot": ar});
                    query["fromChain"] = json!(ac);
                    query["fromSiblings"] = json!(asib);
                }
            }
        }
    }
    let query_bytes = serde_json::to_vec(&query).map_err(fail)?;
    let frame = crate::session_invoke(
        &host,
        socket,
        &config,
        mini_sdk::host_operations::RECEIPT_CONTINUITY,
        &query_bytes,
    )?;
    if frame.first() != Some(&mini_sdk::host_operations::RECEIPT_CONTINUITY)
        || frame.len() as u64 > MAX_JSON
    {
        return Err(fail("Host refused continuity opening (op 151) or exceeded bound"));
    }
    let response: Value = serde_json::from_slice(&frame[1..]).map_err(fail)?;
    bounded_response(&response)?;
    if response["to"]["height"].as_str() != Some(height)
        || response["to"]["worldRoot"].as_str() != Some(world_root)
    {
        return Err(fail("Host op 151 response endpoint differs from requested confirmation point"));
    }
    let start_chain = text(&response, "startChain")?;
    let end_chain = text(&response, "endChain")?;
    let from_siblings = parse_string_list(&response, "fromSiblings", 256)?;
    let to_siblings = parse_string_list(&response, "toSiblings", 256)?;
    let suffix = parse_string_list(&response, "suffix", MAX_HOPS)?;
    let from_height = text(&response["from"], "height")?;
    let from_root = text(&response["from"], "worldRoot")?;
    verify_world_root_opening(from_height, from_root, start_chain, &from_siblings)?;
    if chain_after_digests(start_chain, &suffix)? != end_chain {
        return Err(fail("Host op 151 suffix digests do not fold to endChain"));
    }
    let mut verified = verify_world_root_opening(height, world_root, end_chain, &to_siblings)?;
    verified.start_height = Some(from_height.to_owned());
    verified.start_world_root = Some(from_root.to_owned());
    verified.start_chain = Some(start_chain.to_owned());
    verified.suffix = suffix;
    let mut persisted = verified.json();
    persisted["fromSiblings"] = json!(from_siblings);
    let _ = crate::fsio::replace_private(
        &attempt.join("inclusion-opening.json"),
        &serde_json::to_vec(&persisted).map_err(fail)?,
    );
    Ok(verified)
}

// ------------------------------------------------------------------ Pred.hashEq commit-reveal witness custody (DREGG.PRED.HASHEQ/v2)

/// `Pred.HashEqDigest.deployedCustomization` (`Pred/HashEqDigest.lean`).
pub(crate) const HASHEQ_CUSTOMIZATION: &[u8] = b"DREGG.PRED.HASHEQ/v2";

/// Durable per-workspace ballot commitment witness store file.
pub(crate) const BALLOT_COMMITMENTS_FILE: &str = "ballot-commitments.json";

/// One saved ballot commitment witness in workspace custody (`ballot-commitments.json`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BallotCommitment {
    pub object: String,
    pub voter: String,
    pub vote: String,
    pub salt: String,
    pub digest: String,
}

impl BallotCommitment {
    pub(crate) fn to_json(&self) -> Value {
        json!({
            "object": self.object,
            "voter": self.voter,
            "vote": self.vote,
            "salt": self.salt,
            "digest": self.digest,
        })
    }

    pub(crate) fn from_json(v: &Value) -> Option<Self> {
        Some(Self {
            object: v.get("object")?.as_str()?.to_owned(),
            voter: v.get("voter")?.as_str()?.to_owned(),
            vote: v.get("vote")?.as_str()?.to_owned(),
            salt: v.get("salt")?.as_str()?.to_owned(),
            digest: v.get("digest")?.as_str()?.to_owned(),
        })
    }
}

/// Compute the canonical `Pred.hashEq` commitment digest (`cSHAKE256("", "DREGG.PRED.HASHEQ/v2", Opening.preimage)`)
/// matching `Pred/HashEqDigest.lean` and `hasheq_commit` in `world-activity-admit.py`.
///
/// Each element of `values` may be either a bare integer/natural string (defaulting the slot name
/// to `"state/vote"` for slot 0 and `"state/value{i}"` for subsequent slots, matching
/// `world/ballot/SealedBallot.obend`'s `hashEq([vote], salt, commit)`) or `"slot=value"`.
pub(crate) fn hasheq_commit_digest(
    object_cell: &str,
    salt: &str,
    values: &[&str],
) -> Result<String> {
    let object_cell = object_cell.trim();
    let salt = salt.trim();
    decimal(object_cell)?;
    decimal(salt)?;
    let cell_u64 = object_cell
        .parse::<u64>()
        .map_err(|_| fail("object cell must fit in 64-bit unsigned integer"))?;
    let blinder_bytes = mini_sdk::decimal::to_be_bytes32(salt).map_err(|e| fail(e.0))?;

    let mut parsed_slots: Vec<(String, i128)> = Vec::with_capacity(values.len());
    for (idx, raw) in values.iter().enumerate() {
        let trimmed = raw.trim();
        let (slot_name, val_str) = if let Some((slot, val)) = trimmed.split_once('=') {
            let slot = slot.trim();
            let full_slot = if slot.contains('/') {
                slot.to_owned()
            } else {
                format!("state/{slot}")
            };
            (full_slot, val.trim())
        } else {
            let default_slot = if idx == 0 {
                "state/vote".to_owned()
            } else {
                format!("state/value{idx}")
            };
            (default_slot, trimmed)
        };
        let val_i128 = val_str
            .parse::<i128>()
            .map_err(|_| fail(format!("value `{val_str}` must be an integer")))?;
        parsed_slots.push((slot_name, val_i128));
    }

    let pre = crate::market::preimage(
        cell_u64,
        &parsed_slots,
        "state/salt",
        "state/commit",
        &blinder_bytes,
    );
    let raw = cshake256_raw32(HASHEQ_CUSTOMIZATION, &pre);
    Ok(mini_sdk::decimal::from_be_bytes(&raw))
}

/// Load saved ballot commitments from `root/ballot-commitments.json`.
pub(crate) fn load_ballot_commitments(root: &Path) -> Vec<BallotCommitment> {
    let path = root.join(BALLOT_COMMITMENTS_FILE);
    let Ok(bytes) = crate::fsio::read_bounded(&path, MAX_JSON as usize) else {
        return Vec::new();
    };
    let Ok(val) = serde_json::from_slice::<Value>(&bytes) else {
        return Vec::new();
    };
    val.as_array()
        .map(|arr| arr.iter().filter_map(BallotCommitment::from_json).collect())
        .unwrap_or_default()
}

/// Save a `BallotCommitment` into `root/ballot-commitments.json` and return the updated list.
pub(crate) fn save_ballot_commitment(
    root: &Path,
    entry: BallotCommitment,
) -> Result<Vec<BallotCommitment>> {
    decimal(&entry.object)?;
    decimal(&entry.voter)?;
    decimal(&entry.vote)?;
    decimal(&entry.salt)?;
    decimal(&entry.digest)?;
    let mut entries = load_ballot_commitments(root);
    entries.retain(|e| !(e.object == entry.object && e.voter == entry.voter && e.digest == entry.digest));
    entries.push(entry);
    let json_arr: Vec<Value> = entries.iter().map(BallotCommitment::to_json).collect();
    let mut bytes = serde_json::to_vec_pretty(&json_arr).map_err(fail)?;
    bytes.push(b'\n');
    crate::fsio::replace_private(&root.join(BALLOT_COMMITMENTS_FILE), &bytes)?;
    Ok(entries)
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
    fn recovered_receipt_verifies_history_without_downgrading_anchor() {
        let mode = receipt_mode(Some("recoveredAfterUncertainResponse"), true, false).unwrap();
        assert!(mode == Mode::ReceiptReplay);
        let (root, ticket) = setup(10);
        let original = bytes(&root.0);
        let mut proof = Proof::good();
        finish_locked(&root.0, &ticket, &point(3), mode, &mut proof).unwrap();
        assert_eq!(proof.calls, 1);
        assert_eq!(bytes(&root.0), original);
        proof.reject = true;
        assert!(finish_locked(&root.0, &ticket, &point(4), mode, &mut proof).is_err());
        assert_eq!(bytes(&root.0), original);
    }

    #[test]
    fn protected_receipt_modes_reject_unknown_kinds_even_on_retry() {
        assert!(receipt_mode(Some("installed"), true, false).unwrap() == Mode::Ordinary);
        assert!(receipt_mode(Some("replayed"), true, false).unwrap() == Mode::ReceiptReplay);
        for confirmation in [None, Some("uncertain"), Some("invented")] {
            assert!(receipt_mode(confirmation, true, false).is_err());
            assert!(receipt_mode(confirmation, true, true).is_err());
        }
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
        for stage in [Stage::BeforeCommit, Stage::AfterCommit] {
            let (root, ticket) = setup(1);
            let status = Command::new(std::env::current_exe().unwrap())
                .args(["--exact", "receipt_continuity::tests::crash_child"])
                .env("MINI_CONTINUITY_CRASH_ROOT", &root.0)
                .env("MINI_CONTINUITY_CRASH_STAGE", (stage as u8).to_string())
                .output()
                .unwrap()
                .status;
            assert_eq!(status.code(), Some(73));
            let expected = if stage == Stage::BeforeCommit {
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

    /// The verifier's `profile` runs once per (image SHA-256, config bytes)
    /// in a process, not once per check; any config byte change runs it again.
    #[test]
    fn verifier_profile_runs_once_per_image_and_config_bytes() {
        let root = Temp::new();
        let count = root.0.join("count");
        let verifier = root.0.join("verifier");
        fs::write(
            &verifier,
            format!(
                "#!/bin/sh\necho x >> {}\nprintf '{{\"domain\":\"7\",\"semantics\":\"8\",\"expectedSeed\":\"9\"}}'\n",
                count.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&verifier, fs::Permissions::from_mode(0o700)).unwrap();
        let config = root.0.join("config.json");
        fs::write(&config, b"{\"a\":1}").unwrap();
        let runs = || fs::read_to_string(&count).map(|t| t.lines().count()).unwrap_or(0);
        let sha_a = crate::host_image_sha256(&verifier).unwrap();
        let first = checked_identity(&verifier, &sha_a, &config).unwrap();
        assert_eq!(first["domain"], "7");
        assert_eq!(checked_identity(&verifier, &sha_a, &config).unwrap(), first);
        assert_eq!(runs(), 1);
        fs::write(&config, b"{\"a\":2}").unwrap();
        checked_identity(&verifier, &sha_a, &config).unwrap();
        assert_eq!(runs(), 2);
        // A claimed new pin must match an actual changed executable, not an
        // arbitrary cache label. The failed pin cannot execute or fill cache.
        assert!(checked_identity(&verifier, &"0".repeat(64), &config).is_err());
        assert_eq!(runs(), 2);
        let mut changed = fs::read(&verifier).unwrap();
        changed.extend_from_slice(b"\n# new pinned edition\n");
        fs::write(&verifier, changed).unwrap();
        let sha_b = crate::host_image_sha256(&verifier).unwrap();
        checked_identity(&verifier, &sha_b, &config).unwrap();
        assert_eq!(runs(), 3);
        checked_identity(&verifier, &sha_b, &config).unwrap();
        assert_eq!(runs(), 3);
    }

    #[test]
    fn finished_attempt_is_recognised_only_for_its_exact_outcome() {
        let root = Temp::new();
        let attempt = root.0.join("attempts").join("a1");
        fs::create_dir_all(&attempt).unwrap();
        let outcome = json!({"type":"confirmed","acceptedCount":"5","worldRoot":"6"});
        assert!(!finished_in_process(&attempt, &outcome).unwrap());
        FINISHED_ATTEMPTS
            .lock()
            .unwrap()
            .push((canonical_attempt(&attempt).unwrap(), outcome.clone()));
        assert!(finished_in_process(&attempt, &outcome).unwrap());
        let other = json!({"type":"confirmed","acceptedCount":"5","worldRoot":"7"});
        assert!(!finished_in_process(&attempt, &other).unwrap());
        let sibling = root.0.join("attempts").join("a2");
        fs::create_dir_all(&sibling).unwrap();
        assert!(!finished_in_process(&sibling, &outcome).unwrap());
    }

    #[test]
    fn encode_nat_decimal_matches_stream_codec_base255_terminator() {
        assert_eq!(encode_nat_decimal("0").unwrap(), vec![255]);
        assert_eq!(encode_nat_decimal("1").unwrap(), vec![1, 255]);
        assert_eq!(encode_nat_decimal("254").unwrap(), vec![254, 255]);
        assert_eq!(encode_nat_decimal("255").unwrap(), vec![0, 1, 255]);
        assert_eq!(encode_nat_decimal("256").unwrap(), vec![1, 1, 255]);
        assert!(encode_nat_decimal("-1").is_err());
        assert!(encode_nat_decimal("01").is_err());
    }

    #[test]
    fn deterministic_cshake256_world_root_opening_verifies_and_rejects_tampering() {
        let height = "7";
        let chain0 = "0";
        let ev1 = "111";
        let ev2 = "222";
        let end_chain = chain_after_digests(chain0, &[ev1.to_owned(), ev2.to_owned()]).unwrap();
        let siblings = vec!["12345".to_owned(), "67890".to_owned(), "54321".to_owned()];
        let computed = compute_world_root_from_system_opening(height, &end_chain, &siblings).unwrap();
        let root_dec = computed.world_root;
        assert_eq!(computed.steps.len(), 3);
        let verified = verify_world_root_opening(height, &root_dec, &end_chain, &siblings).unwrap();
        assert_eq!(verified.world_root, root_dec);
        assert_eq!(verified.height, height);
        assert_eq!(verified.chain, end_chain);
        assert_eq!(verified.steps.len(), 3);

        // Any tamper to worldRoot, endChain, height, or siblings is deterministically rejected.
        assert!(verify_world_root_opening("8", &root_dec, &end_chain, &siblings).is_err());
        assert!(verify_world_root_opening(height, "999", &end_chain, &siblings).is_err());
        assert!(verify_world_root_opening(height, &root_dec, "999", &siblings).is_err());
        let bad_siblings = vec!["12345".to_owned(), "67891".to_owned(), "54321".to_owned()];
        assert!(verify_world_root_opening(height, &root_dec, &end_chain, &bad_siblings).is_err());
        let too_many_siblings = vec!["1".to_owned(); deployed_ix_system_bits().len() + 1];
        assert!(compute_world_root_from_system_opening(height, &end_chain, &too_many_siblings).is_err());
    }

    #[test]
    fn verify_attempt_inclusion_persists_verified_opening_and_rejects_tampered_witness() {
        let root = Temp::new();
        let ws = json!({"type":"minidregg-participant-workspace-v1"});
        save(&root.0, "workspace.json", &ws).unwrap();

        let height = "12";
        let chain = "987654321";
        let siblings = vec!["42".to_owned(), "84".to_owned()];
        let world_root = compute_world_root_from_system_opening(height, chain, &siblings)
            .unwrap()
            .world_root;

        let attempt = root.0.join("attempts").join("w-abc123");
        workspace::make_private_dir(&root.0.join("attempts")).unwrap();
        workspace::make_private_dir(&attempt).unwrap();
        let confirmation = json!({
            "type": "confirmed",
            "acceptedCount": height,
            "worldRoot": world_root,
            "transactionId": "10",
            "eventId": "20",
            "confirmation": "installed"
        });
        save(&attempt, "outcome.json", &confirmation).unwrap();
        let witness = json!({
            "height": height,
            "worldRoot": world_root,
            "chain": chain,
            "siblings": siblings
        });
        save(&attempt, "continuity-witness.json", &witness).unwrap();

        assert!(load_verified_attempt_inclusion(&attempt, height, &world_root).is_none());
        let verified = verify_attempt_inclusion(&root.0, &ws, &attempt).unwrap();
        assert_eq!(verified.world_root, world_root);
        assert_eq!(verified.steps.len(), 2);
        assert!(attempt.join("inclusion-opening.json").is_file());

        let loaded = load_verified_attempt_inclusion(&attempt, height, &world_root)
            .expect("inclusion-opening.json present")
            .expect("valid opening");
        assert_eq!(loaded.world_root, world_root);
        assert_eq!(loaded.system_leaf, verified.system_leaf);

        // Tamper with inclusion-opening.json and continuity-witness.json -> rejected
        let tampered = json!({
            "height": height,
            "worldRoot": world_root,
            "chain": "111",
            "siblings": ["42", "84"]
        });
        fs::write(attempt.join("inclusion-opening.json"), serde_json::to_vec(&tampered).unwrap()).unwrap();
        fs::write(attempt.join("continuity-witness.json"), serde_json::to_vec(&tampered).unwrap()).unwrap();
        assert!(load_verified_attempt_inclusion(&attempt, height, &world_root).unwrap().is_err());
        assert!(verify_attempt_inclusion(&root.0, &ws, &attempt).is_err());
    }

    #[test]
    fn retain_attempt_witness_and_verify_from_cached_hop_or_public_mode_dir() {
        let root = Temp::new();
        let ws = json!({"type":"minidregg-participant-workspace-v1"});
        save(&root.0, "workspace.json", &ws).unwrap();

        let height = "15";
        let chain = "555666777";
        let siblings = vec!["101".to_owned(), "202".to_owned()];
        let world_root = compute_world_root_from_system_opening(height, chain, &siblings)
            .unwrap()
            .world_root;

        // Simulate a verified hop where `from` was at height 15 while `anchor.json` is at height 30
        record_verified_witness(
            &json!(height),
            &json!(world_root),
            &json!(chain),
            &json!(siblings),
        );

        // Create attempt directory with standard 0755 permissions (not 0700) and no outcome.json (as in check_retained)
        let attempt = root.0.join("attempts").join("r-hist15");
        fs::create_dir_all(&attempt).unwrap();
        fs::set_permissions(&attempt, fs::Permissions::from_mode(0o755)).unwrap();

        retain_attempt_witness_if_matching(
            &root.0,
            &attempt,
            &json!({"acceptedCount": height, "worldRoot": world_root}),
        );
        assert!(attempt.join("continuity-witness.json").is_file());

        let verified = verify_attempt_inclusion(&root.0, &ws, &attempt).unwrap();
        assert_eq!(verified.height, height);
        assert_eq!(verified.world_root, world_root);
        assert!(attempt.join("inclusion-opening.json").is_file());
    }

    #[test]
    fn hasheq_commit_digest_matches_world_activity_admit_reference_vectors_and_persists_custody() {
        // Exact port of `hasheq_commit(cell, vote, salt)` from `native/resource-client/world-activity-admit.py`
        fn python_reference_hasheq_commit(cell: u64, vote: i128, salt: u128) -> String {
            const RC: [u64; 24] = [
                1, 0x8082, 0x800000000000808a, 0x8000000080008000, 0x808b, 0x80000001,
                0x8000000080008081, 0x8000000000008009, 0x8a, 0x88, 0x80008009, 0x8000000a,
                0x8000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
                0x8000000000008002, 0x8000000000000080, 0x800a, 0x800000008000000a,
                0x8000000080008081, 0x8000000000008080, 0x80000001, 0x8000000080008008,
            ];
            const ROT: [u32; 25] = [
                0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2,
                61, 56, 14,
            ];
            const PI: [usize; 25] = [
                0, 10, 20, 5, 15, 16, 1, 11, 21, 6, 7, 17, 2, 12, 22, 23, 8, 18, 3, 13, 14, 24, 9,
                19, 4,
            ];
            let nm = |s: &str| {
                let mut v = (s.len() as u32).to_be_bytes().to_vec();
                v.extend_from_slice(s.as_bytes());
                v
            };
            let mut pre = Vec::new();
            pre.extend_from_slice(&cell.to_be_bytes());
            pre.extend_from_slice(&1u32.to_be_bytes());
            pre.extend_from_slice(&nm("state/vote"));
            pre.extend_from_slice(&nm("state/salt"));
            pre.extend_from_slice(&nm("state/commit"));
            let mut vote_word = if vote < 0 { [0xffu8; 32] } else { [0u8; 32] };
            vote_word[16..].copy_from_slice(&vote.to_be_bytes());
            vote_word[0] ^= 0x80;
            pre.extend_from_slice(&vote_word);
            let mut salt_word = [0u8; 32];
            salt_word[16..].copy_from_slice(&salt.to_be_bytes());
            pre.extend_from_slice(&salt_word);

            let mut msg = vec![1u8, 136, 1, 0, 1, 160];
            msg.extend_from_slice(b"DREGG.PRED.HASHEQ/v2");
            msg.extend_from_slice(&[0u8; 110]);
            msg.extend_from_slice(&pre);
            msg.push(0x04);
            while msg.len() % 136 != 0 {
                msg.push(0);
            }
            if let Some(last) = msg.last_mut() {
                *last |= 0x80;
            }
            let mut st = [0u64; 25];
            for off in (0..msg.len()).step_by(136) {
                for i in 0..17 {
                    let mut chunk = [0u8; 8];
                    chunk.copy_from_slice(&msg[off + 8 * i..off + 8 * i + 8]);
                    st[i] ^= u64::from_le_bytes(chunk);
                }
                for rc in RC {
                    let mut c = [0u64; 5];
                    for x in 0..5 {
                        c[x] = st[x] ^ st[x + 5] ^ st[x + 10] ^ st[x + 15] ^ st[x + 20];
                    }
                    let mut d = [0u64; 5];
                    for x in 0..5 {
                        d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
                    }
                    for i in 0..25 {
                        st[i] ^= d[i % 5];
                    }
                    let mut b = [0u64; 25];
                    for i in 0..25 {
                        b[PI[i]] = st[i].rotate_left(ROT[i]);
                    }
                    for i in 0..25 {
                        let row = 5 * (i / 5);
                        st[i] = b[i] ^ ((!b[row + (i + 1) % 5]) & b[row + (i + 2) % 5]);
                    }
                    st[0] ^= rc;
                }
            }
            let mut out = [0u8; 32];
            for i in 0..4 {
                out[8 * i..8 * i + 8].copy_from_slice(&st[i].to_le_bytes());
            }
            mini_sdk::decimal::from_be_bytes(&out)
        }

        for (cell, vote, salt) in [(5001u64, 1i128, 111u128), (5001, 1, 222), (42, 0, 999999), (42, 2, 0)] {
            let expected = python_reference_hasheq_commit(cell, vote, salt);
            let actual = hasheq_commit_digest(&cell.to_string(), &salt.to_string(), &[&vote.to_string()]).unwrap();
            assert_eq!(actual, expected, "mismatch for cell={cell}, vote={vote}, salt={salt}");
            let explicit_slot = hasheq_commit_digest(
                &cell.to_string(),
                &salt.to_string(),
                &[&format!("vote={vote}")],
            )
            .unwrap();
            assert_eq!(explicit_slot, expected);
        }

        let root = Temp::new();
        let d1 = hasheq_commit_digest("5001", "111", &["1"]).unwrap();
        let d2 = hasheq_commit_digest("5001", "222", &["0"]).unwrap();
        let saved1 = save_ballot_commitment(
            &root.0,
            BallotCommitment {
                object: "5001".into(),
                voter: "1".into(),
                vote: "1".into(),
                salt: "111".into(),
                digest: d1.clone(),
            },
        )
        .unwrap();
        assert_eq!(saved1.len(), 1);
        let saved2 = save_ballot_commitment(
            &root.0,
            BallotCommitment {
                object: "5001".into(),
                voter: "2".into(),
                vote: "0".into(),
                salt: "222".into(),
                digest: d2.clone(),
            },
        )
        .unwrap();
        assert_eq!(saved2.len(), 2);
        let loaded = load_ballot_commitments(&root.0);
        assert_eq!(loaded.len(), 2);
        assert_eq!(loaded[0].digest, d1);
        assert_eq!(loaded[1].digest, d2);
    }
}

