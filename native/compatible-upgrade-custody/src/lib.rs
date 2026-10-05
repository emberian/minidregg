//! Trusted local root admission for a compatible Mini image transition.
//! This authenticates operator custody and exact pins, not a portable history proof.
use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest, Sha256};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::{
    fs::{self, File, OpenOptions},
    io::{self, Read},
    path::{Component, Path, PathBuf},
};
fn invalid(reason: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason.into())
}
fn hex64(s: &str) -> bool {
    s.len() == 64
        && s.bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
}
fn decimal(s: &str) -> bool {
    !s.is_empty() && (s == "0" || !s.starts_with('0')) && s.bytes().all(|b| b.is_ascii_digit())
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Admission {
    pub protocol: String,
    #[serde(default)]
    pub management_socket: Option<PathBuf>,
    #[serde(default)]
    pub public_socket: Option<PathBuf>,
    pub transaction: PathBuf,
    pub phase: String,
    pub identity: Identity,
    pub source: Candidate,
    pub target: Candidate,
    pub audit: Audit,
    pub config_transition: ConfigTransition,
    pub spk_profiles: Vec<ProfilePin>,
}
#[derive(Deserialize)]
pub struct Identity {
    pub domain: String,
    pub semantics: String,
    pub seed: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Candidate {
    pub manifest: Value,
    pub config_path: PathBuf,
    pub config_sha256: String,
    pub profile: Value,
    pub config: Value,
}
#[derive(Deserialize)]
pub struct Audit {
    source: AuditResult,
    target: AuditResult,
}
#[derive(Deserialize)]
pub struct AuditResult {
    exit: i32,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ConfigTransition {
    changed_fields: Vec<String>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ProfilePin {
    pub path: PathBuf,
    pub sha256: String,
    pub store: String,
    pub host_identity_sha256: String,
}
/// Whether `uid` is the owner a root custody check accepts: uid 0. A
/// `fixture-os` build (native/spk-host/src/os.rs) runs every privileged role
/// as one unprivileged principal, which then also stands in for root.
pub fn root_owner(uid: u32) -> bool {
    #[cfg(feature = "fixture-os")]
    if uid == unsafe { libc::geteuid() } {
        return true;
    }
    uid == 0
}
pub fn canonical(path: &Path) -> bool {
    path.is_absolute()
        && path
            .components()
            .all(|c| matches!(c, Component::RootDir | Component::Normal(_)))
        && path
            .to_str()
            .is_some_and(|p| !p.contains("//") && !p.ends_with('/') && !p.contains("/./"))
}

pub fn root_ancestors(path: &Path) -> io::Result<()> {
    if !canonical(path) {
        return Err(invalid("noncanonical root custody path"));
    }
    let mut prefix = PathBuf::from("/");
    for part in path
        .parent()
        .ok_or_else(|| invalid("missing root parent"))?
        .components()
        .skip(1)
    {
        prefix.push(part);
        let meta = fs::symlink_metadata(&prefix)?;
        if !meta.is_dir() || !root_owner(meta.uid()) || meta.mode() & 0o022 != 0 {
            return Err(invalid(format!(
                "unsafe root custody ancestor: {}",
                prefix.display()
            )));
        }
    }
    Ok(())
}

pub fn root_bytes(path: &Path, max: u64) -> io::Result<Vec<u8>> {
    root_ancestors(path)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || !root_owner(meta.uid())
        || meta.nlink() != 1
        || meta.mode() & 0o022 != 0
        || meta.len() == 0
        || meta.len() > max
    {
        return Err(invalid("root admission/file custody refused"));
    }
    let mut bytes = Vec::new();
    Read::by_ref(&mut file)
        .take(max + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() as u64 != meta.len() {
        return Err(invalid("root file changed while reading"));
    }
    Ok(bytes)
}
pub fn sha(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}
pub fn root_pin(path: &Path, digest: &str) -> io::Result<()> {
    root_ancestors(path)?;
    let meta = fs::symlink_metadata(path)?;
    if !meta.is_file() || !root_owner(meta.uid()) || meta.mode() & 0o022 != 0 || !hex64(digest) {
        return Err(invalid("root image pin custody refused"));
    }
    let mut file = File::open(path)?;
    let mut hash = Sha256::new();
    let mut chunk = [0; 65536];
    loop {
        let n = file.read(&mut chunk)?;
        if n == 0 {
            break;
        }
        hash.update(&chunk[..n]);
    }
    if format!("{:x}", hash.finalize()) != digest {
        return Err(invalid("root image hash differs"));
    }
    Ok(())
}
pub fn image(manifest: &Value, role: &str) -> io::Result<(PathBuf, String)> {
    let path = manifest
        .get(role)
        .and_then(Value::as_str)
        .ok_or_else(|| invalid(format!("manifest lacks {role}")))?;
    let hash = manifest
        .get("sha256")
        .and_then(|v| v.get(role))
        .and_then(Value::as_str)
        .filter(|v| hex64(v))
        .ok_or_else(|| invalid(format!("manifest lacks {role} hash")))?;
    if !canonical(Path::new(path)) {
        return Err(invalid("manifest path is not canonical"));
    }
    Ok((path.into(), hash.into()))
}
fn validate_config_transition(admission: &Admission) -> io::Result<()> {
    let mut fields = admission.config_transition.changed_fields.clone();
    fields.sort();
    if fields != ["signatureBinary", "storageBinary"] {
        return Err(invalid("config transition allowlist refused"));
    }
    if !hex64(&admission.source.config_sha256) || !hex64(&admission.target.config_sha256) {
        return Err(invalid("source/target config hash differs from admission"));
    }
    let mut old = admission.source.config.clone();
    let mut new = admission.target.config.clone();
    for field in ["storageBinary", "signatureBinary"] {
        let role = if field == "storageBinary" {
            "store"
        } else {
            "verifier"
        };
        let (path, _) = image(&admission.target.manifest, role)?;
        if new.get(field).and_then(Value::as_str) != path.to_str() {
            return Err(invalid("target helper differs from manifest"));
        }
        old.as_object_mut()
            .ok_or_else(|| invalid("source config is not an object"))?
            .remove(field)
            .ok_or_else(|| invalid("source config helper absent"))?;
        new.as_object_mut()
            .ok_or_else(|| invalid("target config is not an object"))?
            .remove(field)
            .ok_or_else(|| invalid("target config helper absent"))?;
    }
    if old != new {
        return Err(invalid("compatible config changed a non-helper field"));
    }
    for (field, expected) in [
        ("domain", &admission.identity.domain),
        ("semantics", &admission.identity.semantics),
        ("expectedSeed", &admission.identity.seed),
    ] {
        if !decimal(expected)
            || admission.source.profile.get(field).and_then(Value::as_str) != Some(expected)
            || admission.target.profile.get(field).and_then(Value::as_str) != Some(expected)
        {
            return Err(invalid("compatible profile domain/semantics/seed changed"));
        }
    }
    for (field, expected) in [
        ("domain", &admission.identity.domain),
        ("expectedSeed", &admission.identity.seed),
    ] {
        let value = admission
            .target
            .config
            .get(field)
            .ok_or_else(|| invalid("config namespace absent"))?;
        let value = value
            .as_str()
            .map(str::to_owned)
            .unwrap_or_else(|| value.to_string());
        if &value != expected {
            return Err(invalid("config namespace differs from admission"));
        }
    }
    Ok(())
}

fn validate_topology(admission: &Admission) -> io::Result<()> {
    match (&admission.management_socket, &admission.public_socket) {
        (None, None) => Ok(()),
        (Some(management), Some(public))
            if canonical(management) && canonical(public) && management != public =>
        {
            Ok(())
        }
        _ => Err(invalid(
            "compatible socket topology is incomplete or unsafe",
        )),
    }
}

/// Authenticate retained root evidence without requiring obsolete live images.
pub fn load_evidence(path: &Path) -> io::Result<Admission> {
    let admission: Admission = serde_json::from_slice(&root_bytes(path, 4 * 1024 * 1024)?)?;
    if admission.protocol != "mini-compatible-admission-v1"
        || admission.phase != "kernel-serving-service-stopped"
        || admission.audit.source.exit != 0
        || admission.audit.target.exit != 0
        || path != admission.transaction.join("compatible-admission.json")
    {
        return Err(invalid("compatible admission state refused"));
    }
    validate_topology(&admission)?;
    validate_config_transition(&admission)?;
    Ok(admission)
}

/// Verify current target bytes as well as the root admission.
pub fn load(path: &Path) -> io::Result<Admission> {
    let admission = load_evidence(path)?;
    let bytes = root_bytes(&admission.target.config_path, 1024 * 1024)?;
    if sha(&bytes) != admission.target.config_sha256
        || serde_json::from_slice::<Value>(&bytes)? != admission.target.config
    {
        return Err(invalid("current target config differs from admission"));
    }
    for role in ["host", "store", "verifier"] {
        let (image_path, digest) = image(&admission.target.manifest, role)?;
        root_pin(&image_path, &digest)?;
    }
    Ok(admission)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    fn admission() -> Admission {
        serde_json::from_value(json!({
          "protocol":"mini-compatible-admission-v1", "transaction":"/var/lib/mini/upgrades/t", "phase":"kernel-serving-service-stopped",
          "identity":{"domain":"1","semantics":"2","seed":"3"},
          "source":{"manifest":{},"configPath":"/old","configSha256":"a".repeat(64),"config":{"storageBinary":"/old/store","signatureBinary":"/old/verifier","domain":1,"expectedSeed":3,"secretPath":"/private/key"},"profile":{"domain":"1","semantics":"2","expectedSeed":"3"}},
          "target":{"manifest":{"store":"/new/store","verifier":"/new/verifier","sha256":{"store":"b".repeat(64),"verifier":"c".repeat(64)}},"configPath":"/new","configSha256":"b".repeat(64),"config":{"storageBinary":"/new/store","signatureBinary":"/new/verifier","domain":1,"expectedSeed":3,"secretPath":"/private/key"},"profile":{"domain":"1","semantics":"2","expectedSeed":"3"}},
          "audit":{"source":{"exit":0},"target":{"exit":0}},"configTransition":{"changedFields":["storageBinary","signatureBinary"]},"spkProfiles":[]
        })).unwrap()
    }
    #[test]
    fn only_exact_helper_transition_is_accepted() {
        assert!(validate_config_transition(&admission()).is_ok());
        let mut a = admission();
        a.target.config["secretPath"] = json!("/different");
        assert!(validate_config_transition(&a).is_err());
        let mut a = admission();
        a.target.config["storageBinary"] = json!("/unlisted/store");
        assert!(validate_config_transition(&a).is_err());
        let mut a = admission();
        a.target.profile["expectedSeed"] = json!("4");
        assert!(validate_config_transition(&a).is_err());
        let mut a = admission();
        a.config_transition.changed_fields.push("domain".into());
        assert!(validate_config_transition(&a).is_err());
    }
    #[test]
    fn large_naturals_do_not_collapse_during_equality() {
        let mut a = admission();
        a.source.config["large"] =
            serde_json::from_str("1234567890123456789012345678901234567890").unwrap();
        a.target.config["large"] =
            serde_json::from_str("1234567890123456789012345678901234567891").unwrap();
        assert!(validate_config_transition(&a).is_err());
    }
    #[test]
    fn writable_ancestor_and_traversal_are_refused() {
        assert!(root_ancestors(Path::new("/tmp/compatible-admission.json")).is_err());
        assert!(root_ancestors(Path::new("/var/lib/../admission.json")).is_err());
    }
    #[test]
    fn adopted_socket_topology_is_explicit_paired_and_distinct() {
        let mut a = admission();
        assert!(validate_topology(&a).is_ok());
        a.management_socket = Some("/node/operator/mini.sock".into());
        assert!(validate_topology(&a).is_err());
        a.public_socket = Some("/node/public/mini.sock".into());
        assert!(validate_topology(&a).is_ok());
        a.public_socket = a.management_socket.clone();
        assert!(validate_topology(&a).is_err());
        a.public_socket = Some("/node/../public/mini.sock".into());
        assert!(validate_topology(&a).is_err());
    }
}
