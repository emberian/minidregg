//! Physical candidate IDs shared by controllers of one deployment. A reservation
//! is neither a grant nor evidence of birth: the current Lean admission path
//! remains the authority for every proposed resource and capability.
use crate::{create_private, hex, sync_directory_ancestors, transport, Result};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::thread;
use std::time::Duration;

const FORMAT: &str = "minidregg-participant-reservation-v1";
const MAX_RECORD: u64 = 32 * 1024;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IdKind {
    Resource,
    Capability,
    Subject,
    Key,
}

impl IdKind {
    fn label(self) -> &'static str {
        match self {
            Self::Resource => "resource",
            Self::Capability => "capability",
            Self::Subject => "subject",
            Self::Key => "key",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Role {
    pub label: String,
    pub kind: IdKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Reservation {
    pub request_digest: String,
    pub ids: BTreeMap<String, String>,
    pub record_path: PathBuf,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AttemptBinding {
    pub attempt_path: PathBuf,
    pub source_sha256: String,
    pub record_path: PathBuf,
}

fn random_bytes<const N: usize>() -> Result<[u8; N]> {
    let mut bytes = [0; N];
    File::open("/dev/urandom")
        .and_then(|mut source| source.read_exact(&mut bytes))
        .map_err(|error| format!("cannot obtain namespace randomness: {error}"))?;
    Ok(bytes)
}

fn private_root(root: &Path) -> Result<()> {
    if !root.is_absolute() {
        return Err("namespace root must be absolute".into());
    }
    match fs::DirBuilder::new().mode(0o700).create(root) {
        Ok(()) => sync_directory_ancestors(root)?,
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => (),
        Err(error) => return Err(format!("cannot create namespace root: {error}")),
    }
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    let info = fs::symlink_metadata(root).map_err(|error| error.to_string())?;
    if !info.file_type().is_dir()
        || info.uid() != unsafe { geteuid() }
        || info.permissions().mode() & 0o077 != 0
    {
        return Err("namespace root must be an owner-private directory".into());
    }
    Ok(())
}

fn lock(root: &Path) -> Result<File> {
    let path = root.join("namespace.lock");
    for _ in 0..500 {
        match transport::service_lock(&path) {
            Ok(guard) => return Ok(guard),
            Err(error) if error.starts_with("another service owns ") => {
                thread::sleep(Duration::from_millis(10))
            }
            Err(error) => return Err(error),
        }
    }
    Err("namespace is busy; retry the same request".into())
}

fn checked_text(name: &str, value: &str) -> Result<()> {
    if value.is_empty() || value.len() > 256 || value.chars().any(char::is_control) {
        return Err(format!(
            "namespace {name} must be 1..=256 printable UTF-8 bytes"
        ));
    }
    Ok(())
}

fn record(path: &Path) -> Result<Value> {
    let metadata = fs::symlink_metadata(path).map_err(|error| error.to_string())?;
    unsafe extern "C" {
        fn geteuid() -> u32;
    }
    if !metadata.file_type().is_file()
        || metadata.uid() != unsafe { geteuid() }
        || metadata.permissions().mode() & 0o077 != 0
        || metadata.len() > MAX_RECORD
    {
        return Err(format!(
            "invalid private namespace record {}",
            path.display()
        ));
    }
    let bytes = fs::read(path).map_err(|error| error.to_string())?;
    serde_json::from_slice(&bytes).map_err(|error| format!("namespace record JSON: {error}"))
}

fn role_json(roles: &[Role]) -> Value {
    Value::Array(
        roles
            .iter()
            .map(|role| {
                json!({
                    "label": role.label, "kind": role.kind.label()
                })
            })
            .collect(),
    )
}

fn parse_ids(value: &Value, roles: &[Role]) -> Result<BTreeMap<String, String>> {
    let saved = value
        .get("ids")
        .and_then(Value::as_object)
        .ok_or("namespace record lacks ids")?;
    if saved.len() != roles.len() {
        return Err("namespace record has wrong ID count".into());
    }
    let mut ids = BTreeMap::new();
    for role in roles {
        let id = saved
            .get(&role.label)
            .and_then(Value::as_str)
            .ok_or("namespace record lacks role ID")?;
        if id
            .parse::<u64>()
            .ok()
            .is_none_or(|number| number < (1u64 << 63))
            || id.starts_with('0')
        {
            return Err("namespace record has invalid candidate ID".into());
        }
        ids.insert(role.label.clone(), id.to_owned());
    }
    Ok(ids)
}

/// Reserve all IDs for one exact request. `fingerprint` is the caller's
/// pre-allocation source; a changed request with the same key refuses. All
/// controllers for a deployment must use the same root. Never delete a record
/// after an uncertain submit, because a later request must not reinterpret it.
pub(crate) fn reserve(
    root: &Path,
    deployment: &str,
    participant: &str,
    request: &str,
    fingerprint: &[u8],
    roles: &[Role],
) -> Result<Reservation> {
    for (name, value) in [
        ("deployment", deployment),
        ("participant", participant),
        ("request", request),
    ] {
        checked_text(name, value)?;
    }
    if fingerprint.is_empty() || fingerprint.len() > 256 * 1024 {
        return Err("namespace request fingerprint must contain 1..=262144 bytes".into());
    }
    if roles.is_empty() || roles.len() > 64 {
        return Err("namespace request must name 1..=64 roles".into());
    }
    let mut labels = BTreeSet::new();
    for role in roles {
        checked_text("role", &role.label)?;
        if !labels.insert(&role.label) {
            return Err("duplicate namespace role".into());
        }
    }
    private_root(root)?;
    let _guard = lock(root)?;
    let key = serde_json::to_vec(&json!([deployment, participant, request]))
        .map_err(|error| error.to_string())?;
    let request_digest = hex(&Sha256::digest(&key));
    let path = root.join(format!("request-{request_digest}.json"));
    let fingerprint_digest = hex(&Sha256::digest(fingerprint));
    let role_spec = role_json(roles);
    let mut used = BTreeSet::new();
    for entry in fs::read_dir(root).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if !name.starts_with("request-") || !name.ends_with(".json") {
            continue;
        }
        let prior = record(&entry.path())?;
        if prior.get("format") != Some(&json!(FORMAT)) {
            return Err("namespace contains unsupported reservation record".into());
        }
        if prior.get("deployment") != Some(&json!(deployment)) {
            continue;
        }
        let prior_ids = prior
            .get("ids")
            .and_then(Value::as_object)
            .ok_or("namespace record lacks ids")?;
        for value in prior_ids.values() {
            let id = value.as_str().ok_or("namespace record has non-string ID")?;
            if id
                .parse::<u64>()
                .ok()
                .is_none_or(|number| number < (1u64 << 63))
                || id.starts_with('0')
            {
                return Err("namespace record has invalid candidate ID".into());
            }
            if !used.insert(id.to_owned()) {
                return Err("namespace contains colliding candidate IDs".into());
            }
        }
    }
    if path.exists() {
        let saved = record(&path)?;
        if saved.get("deployment") != Some(&json!(deployment))
            || saved.get("participant") != Some(&json!(participant))
            || saved.get("request") != Some(&json!(request))
            || saved.get("fingerprintSha256") != Some(&json!(fingerprint_digest))
            || saved.get("roles") != Some(&role_spec)
        {
            return Err(
                "namespace request key is already bound to different source or roles".into(),
            );
        }
        return Ok(Reservation {
            request_digest,
            ids: parse_ids(&saved, roles)?,
            record_path: path,
        });
    }
    let mut ids = BTreeMap::new();
    for role in roles {
        let mut candidate = None;
        for _ in 0..16 {
            let mut number = u64::from_be_bytes(random_bytes()?);
            number |= 1u64 << 63;
            let id = number.to_string();
            if used.insert(id.clone()) {
                candidate = Some(id);
                break;
            }
        }
        ids.insert(
            role.label.clone(),
            candidate.ok_or("namespace random ID collision budget exhausted")?,
        );
    }
    let saved = json!({
        "format":FORMAT,"deployment":deployment,"participant":participant,
        "request":request,"fingerprintSha256":fingerprint_digest,
        "roles":role_spec,"ids":ids,
        "status":"candidate-only"
    });
    let mut bytes = serde_json::to_vec_pretty(&saved).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let temp = root.join(format!(".pending-{}.json", hex(&random_bytes::<16>()?)));
    create_private(&temp, &bytes)?;
    fs::hard_link(&temp, &path)
        .map_err(|error| format!("cannot publish namespace record: {error}"))?;
    fs::remove_file(&temp)
        .map_err(|error| format!("cannot retire namespace staging record: {error}"))?;
    sync_directory_ancestors(root)?;
    Ok(Reservation {
        request_digest,
        ids,
        record_path: path,
    })
}

/// Whether this reservation is already bound to an exact custody attempt.
/// Once bound, a native attempt may exist and its source is fixed.
pub(crate) fn is_bound(reservation: &Reservation) -> Result<bool> {
    let root = reservation
        .record_path
        .parent()
        .ok_or("namespace reservation lacks root")?;
    Ok(root
        .join(format!("binding-{}.json", reservation.request_digest))
        .exists())
}

/// Bind a reserved request to one exact retained source and one custody
/// attempt before any call may be submitted. A second controller can find the
/// original path, but cannot bind a different attempt or source to these IDs.
pub(crate) fn bind_attempt(
    reservation: &Reservation,
    attempt_path: &Path,
    source_sha: &str,
) -> Result<AttemptBinding> {
    if source_sha.len() != 64
        || !source_sha
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err("namespace source SHA-256 must be 64 lowercase hex digits".into());
    }
    if !attempt_path.is_absolute() {
        return Err("namespace attempt path must be absolute".into());
    }
    let parent = attempt_path
        .parent()
        .ok_or("namespace attempt lacks parent")?;
    let parent = fs::canonicalize(parent).map_err(|error| error.to_string())?;
    let attempt_name = attempt_path
        .file_name()
        .ok_or("namespace attempt lacks filename")?;
    let attempt_path = parent.join(attempt_name);
    let root = reservation
        .record_path
        .parent()
        .ok_or("namespace reservation lacks root")?;
    private_root(root)?;
    let _guard = lock(root)?;
    let saved = record(&reservation.record_path)?;
    if saved.get("format") != Some(&json!(FORMAT))
        || parse_ids(&saved, &saved_roles(&saved)?)? != reservation.ids
        || saved_request_digest(&saved)? != reservation.request_digest
        || reservation
            .record_path
            .file_name()
            .and_then(|name| name.to_str())
            != Some(format!("request-{}.json", reservation.request_digest).as_str())
    {
        return Err("namespace reservation changed before attempt binding".into());
    }
    let path = root.join(format!("binding-{}.json", reservation.request_digest));
    if path.exists() {
        let prior = record(&path)?;
        let original = prior
            .get("attemptPath")
            .and_then(Value::as_str)
            .ok_or("namespace binding lacks attempt path")?;
        if prior.get("format") != Some(&json!("minidregg-participant-attempt-binding-v1"))
            || prior.get("requestDigest") != Some(&json!(reservation.request_digest))
            || prior.get("sourceSha256") != Some(&json!(source_sha))
            || original != attempt_path.to_string_lossy()
        {
            return Err(format!(
                "namespace request is already bound to exact attempt {original}"
            ));
        }
        return Ok(AttemptBinding {
            attempt_path,
            source_sha256: source_sha.to_owned(),
            record_path: path,
        });
    }
    let value = json!({
        "format":"minidregg-participant-attempt-binding-v1",
        "requestDigest":reservation.request_digest,
        "attemptPath":attempt_path,
        "sourceSha256":source_sha,
        "status":"exact-attempt-only"
    });
    let mut bytes = serde_json::to_vec_pretty(&value).map_err(|error| error.to_string())?;
    bytes.push(b'\n');
    let temp = root.join(format!(
        ".pending-binding-{}.json",
        hex(&random_bytes::<16>()?)
    ));
    create_private(&temp, &bytes)?;
    fs::hard_link(&temp, &path)
        .map_err(|error| format!("cannot publish namespace attempt binding: {error}"))?;
    fs::remove_file(&temp)
        .map_err(|error| format!("cannot retire namespace binding staging record: {error}"))?;
    sync_directory_ancestors(root)?;
    Ok(AttemptBinding {
        attempt_path,
        source_sha256: source_sha.to_owned(),
        record_path: path,
    })
}

/// Release a reservation's exact-attempt binding once that attempt is
/// DEFINITELY unadmitted: it never assembled an exact call, or the Host
/// answered its exact call with a final refusal. The caller decides
/// definiteness; an uncertain outcome must never reach here. The binding
/// record is retained as `released-{digest}-{n}.json` (never read by
/// `reserve`), and the reservation's IDs stay reserved for the same request,
/// so the next attempt reuses them and at most one attempt over these IDs can
/// ever install. Returns the retained record, or `None` when nothing was bound.
pub(crate) fn release_attempt(
    reservation: &Reservation,
    attempt_path: &Path,
) -> Result<Option<PathBuf>> {
    if !attempt_path.is_absolute() {
        return Err("namespace attempt path must be absolute".into());
    }
    let parent = attempt_path
        .parent()
        .ok_or("namespace attempt lacks parent")?;
    let parent = fs::canonicalize(parent).map_err(|error| error.to_string())?;
    let attempt_name = attempt_path
        .file_name()
        .ok_or("namespace attempt lacks filename")?;
    let attempt_path = parent.join(attempt_name);
    let root = reservation
        .record_path
        .parent()
        .ok_or("namespace reservation lacks root")?;
    private_root(root)?;
    let _guard = lock(root)?;
    let path = root.join(format!("binding-{}.json", reservation.request_digest));
    if !path.exists() {
        return Ok(None);
    }
    let prior = record(&path)?;
    if prior.get("format") != Some(&json!("minidregg-participant-attempt-binding-v1"))
        || prior.get("requestDigest") != Some(&json!(reservation.request_digest))
        || prior.get("attemptPath").and_then(Value::as_str)
            != Some(attempt_path.to_string_lossy().as_ref())
    {
        return Err("namespace binding names a different attempt; not released".into());
    }
    let mut index = 1u32;
    let retained = loop {
        let candidate = root.join(format!(
            "released-{}-{index:04}.json",
            reservation.request_digest
        ));
        if !candidate.exists() {
            break candidate;
        }
        index = index
            .checked_add(1)
            .filter(|next| *next < 10_000)
            .ok_or("namespace release records exhausted")?;
    };
    fs::rename(&path, &retained)
        .map_err(|error| format!("cannot release namespace attempt binding: {error}"))?;
    sync_directory_ancestors(root)?;
    Ok(Some(retained))
}

fn saved_roles(value: &Value) -> Result<Vec<Role>> {
    let entries = value
        .get("roles")
        .and_then(Value::as_array)
        .ok_or("namespace reservation lacks roles")?;
    let mut roles = Vec::new();
    for entry in entries {
        let label = entry
            .get("label")
            .and_then(Value::as_str)
            .ok_or("namespace reservation role lacks label")?;
        let kind = match entry.get("kind").and_then(Value::as_str) {
            Some("resource") => IdKind::Resource,
            Some("capability") => IdKind::Capability,
            Some("subject") => IdKind::Subject,
            Some("key") => IdKind::Key,
            _ => return Err("namespace reservation role has invalid kind".into()),
        };
        roles.push(Role {
            label: label.to_owned(),
            kind,
        });
    }
    Ok(roles)
}

fn saved_request_digest(value: &Value) -> Result<String> {
    let mut parts = Vec::new();
    for field in ["deployment", "participant", "request"] {
        parts.push(
            value
                .get(field)
                .and_then(Value::as_str)
                .ok_or("namespace reservation lacks request identity")?,
        );
    }
    let key = serde_json::to_vec(&parts).map_err(|error| error.to_string())?;
    Ok(hex(&Sha256::digest(&key)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::{Command, Stdio};
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{SystemTime, UNIX_EPOCH};

    static NEXT_ROOT: AtomicU64 = AtomicU64::new(0);

    fn root() -> PathBuf {
        std::env::temp_dir().join(format!(
            "mini-participant-namespace-{}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_nanos(),
            NEXT_ROOT.fetch_add(1, Ordering::Relaxed)
        ))
    }

    fn roles() -> Vec<Role> {
        vec![
            Role {
                label: "target".into(),
                kind: IdKind::Resource,
            },
            Role {
                label: "ownerCapability".into(),
                kind: IdKind::Capability,
            },
            Role {
                label: "controlCapability".into(),
                kind: IdKind::Capability,
            },
        ]
    }

    #[test]
    fn exact_request_survives_restart_and_changed_request_refuses() {
        let root = root();
        let first = reserve(
            &root,
            "deployment-1",
            "alice",
            "create-project",
            b"source-v1",
            &roles(),
        )
        .unwrap();
        let again = reserve(
            &root,
            "deployment-1",
            "alice",
            "create-project",
            b"source-v1",
            &roles(),
        )
        .unwrap();
        assert_eq!(first, again);
        assert_eq!(first.ids.len(), 3);
        assert_eq!(first.ids.values().collect::<BTreeSet<_>>().len(), 3);
        assert!(reserve(
            &root,
            "deployment-1",
            "alice",
            "create-project",
            b"source-v2",
            &roles()
        )
        .is_err());
        let mut changed_roles = roles();
        changed_roles[1].kind = IdKind::Resource;
        assert!(reserve(
            &root,
            "deployment-1",
            "alice",
            "create-project",
            b"source-v1",
            &changed_roles
        )
        .is_err());
        assert_eq!(
            record(&first.record_path).unwrap()["status"],
            "candidate-only"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn distinct_participants_and_requests_never_share_local_candidates() {
        let root = root();
        let a = reserve(&root, "deployment-1", "alice", "one", b"source", &roles()).unwrap();
        let b = reserve(&root, "deployment-1", "bob", "one", b"source", &roles()).unwrap();
        let c = reserve(&root, "deployment-1", "alice", "two", b"source", &roles()).unwrap();
        let all: BTreeSet<_> = [a, b, c]
            .iter()
            .flat_map(|r| r.ids.values().cloned())
            .collect();
        assert_eq!(all.len(), 9);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn onboarding_subject_and_key_are_distinct_candidates() {
        let root = root();
        let roles = [
            Role {
                label: "subject".into(),
                kind: IdKind::Subject,
            },
            Role {
                label: "keyId".into(),
                kind: IdKind::Key,
            },
        ];
        let saved = reserve(
            &root,
            "deployment-1",
            "sponsor-7",
            "invite-alice",
            b"new public key",
            &roles,
        )
        .unwrap();
        assert_ne!(saved.ids["subject"], saved.ids["keyId"]);
        assert_eq!(
            reserve(
                &root,
                "deployment-1",
                "sponsor-7",
                "invite-alice",
                b"new public key",
                &roles
            )
            .unwrap(),
            saved
        );
        fs::remove_dir_all(root).unwrap();
    }

    // The test binary is launched as a separate process by the parent test.
    #[test]
    fn child_reservation_process() {
        let Ok(root) = std::env::var("MINI_NAMESPACE_TEST_ROOT") else {
            return;
        };
        let participant = std::env::var("MINI_NAMESPACE_TEST_PARTICIPANT").unwrap();
        let request = std::env::var("MINI_NAMESPACE_TEST_REQUEST").unwrap();
        let saved = reserve(
            Path::new(&root),
            "deployment-1",
            &participant,
            &request,
            b"source",
            &roles(),
        )
        .unwrap();
        if let Ok(name) = std::env::var("MINI_NAMESPACE_TEST_BIND") {
            let attempt = Path::new(&root).join("attempts").join(name);
            let source_sha = hex(&Sha256::digest(b"retained birth source"));
            if bind_attempt(&saved, &attempt, &source_sha).is_err() {
                std::process::exit(18);
            }
        }
        if std::env::var_os("MINI_NAMESPACE_TEST_CRASH").is_some() {
            // Reservation is durable; no response reaches the controller.
            std::process::exit(17);
        }
        assert_eq!(saved.ids.len(), 3);
    }

    fn child(root: &Path, participant: &str, request: &str, crash: bool) -> std::process::Child {
        let mut command = Command::new(std::env::current_exe().unwrap());
        command
            .arg("--exact")
            .arg("participant_namespace::tests::child_reservation_process")
            .env("MINI_NAMESPACE_TEST_ROOT", root)
            .env("MINI_NAMESPACE_TEST_PARTICIPANT", participant)
            .env("MINI_NAMESPACE_TEST_REQUEST", request)
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        if crash {
            command.env("MINI_NAMESPACE_TEST_CRASH", "1");
        }
        command.spawn().unwrap()
    }

    #[test]
    fn concurrent_controllers_and_lost_reservation_response() {
        let root = root();
        let mut processes = (0..8)
            .map(|index| child(&root, &format!("person-{index}"), "create", false))
            .collect::<Vec<_>>();
        for process in &mut processes {
            assert!(process.wait().unwrap().success());
        }
        let mut ids = BTreeSet::new();
        for index in 0..8 {
            let saved = reserve(
                &root,
                "deployment-1",
                &format!("person-{index}"),
                "create",
                b"source",
                &roles(),
            )
            .unwrap();
            for id in saved.ids.values() {
                assert!(ids.insert(id.clone()));
            }
        }
        let mut crashed = child(&root, "recovering", "create", true);
        assert_eq!(crashed.wait().unwrap().code(), Some(17));
        let recovered = reserve(
            &root,
            "deployment-1",
            "recovering",
            "create",
            b"source",
            &roles(),
        )
        .unwrap();
        assert!(recovered.record_path.exists());
        for id in recovered.ids.values() {
            assert!(ids.insert(id.clone()));
        }
        assert_eq!(ids.len(), 27);
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn concurrent_exact_request_has_one_durable_assignment() {
        let root = root();
        let mut processes = (0..8)
            .map(|_| child(&root, "alice", "same-request", false))
            .collect::<Vec<_>>();
        for process in &mut processes {
            assert!(process.wait().unwrap().success());
        }
        let saved = reserve(
            &root,
            "deployment-1",
            "alice",
            "same-request",
            b"source",
            &roles(),
        )
        .unwrap();
        let records = fs::read_dir(&root)
            .unwrap()
            .filter_map(|entry| entry.ok())
            .filter(|entry| entry.file_name().to_string_lossy().starts_with("request-"))
            .count();
        assert_eq!(records, 1);
        assert_eq!(
            parse_ids(&record(&saved.record_path).unwrap(), &roles()).unwrap(),
            saved.ids
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn corrupt_collision_refuses_next_reservation() {
        let root = root();
        let a = reserve(&root, "deployment-1", "alice", "one", b"source", &roles()).unwrap();
        let b = reserve(&root, "deployment-1", "bob", "one", b"source", &roles()).unwrap();
        let mut altered = record(&b.record_path).unwrap();
        altered["ids"]["target"] = json!(a.ids["target"]);
        fs::write(&b.record_path, serde_json::to_vec(&altered).unwrap()).unwrap();
        assert!(
            reserve(&root, "deployment-1", "carol", "one", b"source", &roles())
                .unwrap_err()
                .contains("colliding candidate IDs")
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn public_or_symlinked_namespace_root_refuses() {
        let root = root();
        fs::create_dir(&root).unwrap();
        fs::set_permissions(&root, fs::Permissions::from_mode(0o755)).unwrap();
        assert!(
            reserve(&root, "deployment-1", "alice", "one", b"source", &roles())
                .unwrap_err()
                .contains("owner-private directory")
        );
        fs::set_permissions(&root, fs::Permissions::from_mode(0o700)).unwrap();
        let link = root.with_extension("link");
        std::os::unix::fs::symlink(&root, &link).unwrap();
        assert!(
            reserve(&link, "deployment-1", "alice", "one", b"source", &roles())
                .unwrap_err()
                .contains("owner-private directory")
        );
        fs::remove_file(link).unwrap();
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn one_exact_attempt_binding_survives_restart_and_refuses_competitor() {
        let root = root();
        let first = reserve(
            &root,
            "deployment-1",
            "alice",
            "create",
            b"source",
            &roles(),
        )
        .unwrap();
        let attempts = root.join("attempts");
        fs::create_dir(&attempts).unwrap();
        let source_sha = hex(&Sha256::digest(b"retained birth source"));
        let original = attempts.join("create-alice");
        let binding = bind_attempt(&first, &original, &source_sha).unwrap();
        let reopened = reserve(
            &root,
            "deployment-1",
            "alice",
            "create",
            b"source",
            &roles(),
        )
        .unwrap();
        assert_eq!(
            bind_attempt(&reopened, &original, &source_sha).unwrap(),
            binding
        );
        assert!(
            bind_attempt(&reopened, &attempts.join("other"), &source_sha)
                .unwrap_err()
                .contains("already bound to exact attempt")
        );
        assert!(
            bind_attempt(&reopened, &original, &hex(&Sha256::digest(b"changed")))
                .unwrap_err()
                .contains("already bound to exact attempt")
        );
        assert!(
            !original.exists(),
            "binding precedes custody attempt creation"
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn released_binding_lets_the_same_request_bind_a_new_attempt() {
        let root = root();
        let saved = reserve(
            &root,
            "deployment-1",
            "participant-1",
            "create-x",
            b"source",
            &roles(),
        )
        .unwrap();
        let attempts = root.join("attempts");
        fs::create_dir(&attempts).unwrap();
        let attempt = attempts.join("create-x");
        let first = hex(&Sha256::digest(b"first intent"));
        let second = hex(&Sha256::digest(b"second intent"));
        bind_attempt(&saved, &attempt, &first).unwrap();
        assert!(bind_attempt(&saved, &attempt, &second).is_err());
        // A different attempt path cannot release this binding.
        assert!(release_attempt(&saved, &attempts.join("create-y")).is_err());
        let retained = release_attempt(&saved, &attempt).unwrap().unwrap();
        assert!(retained.exists());
        assert!(!is_bound(&saved).unwrap());
        // Nothing left to release.
        assert_eq!(release_attempt(&saved, &attempt).unwrap(), None);
        // The same request keeps its IDs and binds the new intent.
        let again = reserve(
            &root,
            "deployment-1",
            "participant-1",
            "create-x",
            b"source",
            &roles(),
        )
        .unwrap();
        assert_eq!(again.ids, saved.ids);
        bind_attempt(&again, &attempt, &second).unwrap();
        // A second release retains a second record beside the first.
        let next = release_attempt(&again, &attempt).unwrap().unwrap();
        assert_ne!(next, retained);
        assert!(retained.exists() && next.exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn concurrent_controllers_cannot_bind_two_attempts() {
        let root = root();
        let _ = reserve(&root, "deployment-1", "alice", "same", b"source", &roles()).unwrap();
        fs::create_dir(root.join("attempts")).unwrap();
        let mut processes = (0..8)
            .map(|index| {
                let mut command = Command::new(std::env::current_exe().unwrap());
                command
                    .arg("--exact")
                    .arg("participant_namespace::tests::child_reservation_process")
                    .env("MINI_NAMESPACE_TEST_ROOT", &root)
                    .env("MINI_NAMESPACE_TEST_PARTICIPANT", "alice")
                    .env("MINI_NAMESPACE_TEST_REQUEST", "same")
                    .env("MINI_NAMESPACE_TEST_BIND", format!("attempt-{index}"))
                    .stdout(Stdio::null())
                    .stderr(Stdio::null());
                command.spawn().unwrap()
            })
            .collect::<Vec<_>>();
        let mut won = 0;
        let mut refused = 0;
        for process in &mut processes {
            match process.wait().unwrap().code() {
                Some(0) => won += 1,
                Some(18) => refused += 1,
                code => panic!("unexpected namespace binder child exit: {code:?}"),
            }
        }
        assert_eq!((won, refused), (1, 7));
        let reopened =
            reserve(&root, "deployment-1", "alice", "same", b"source", &roles()).unwrap();
        let persisted =
            record(&root.join(format!("binding-{}.json", reopened.request_digest))).unwrap();
        let original = Path::new(persisted["attemptPath"].as_str().unwrap());
        let source_sha = hex(&Sha256::digest(b"retained birth source"));
        assert!(bind_attempt(&reopened, original, &source_sha).is_ok());
        fs::remove_dir_all(root).unwrap();
    }
}
