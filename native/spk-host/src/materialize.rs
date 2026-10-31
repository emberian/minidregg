//! Signature-verified SPK archive materialization into a new immutable image.
//! Archive decoding streams through bounded private files; the pinned Bread crate
//! decodes the exact verified manifest. Publication remains atomic and exclusive.

pub use minidregg_spk_package_stream::ImportProfile;
use crate::io_context::IoContext;
use minidregg_spk_package_stream::{self as stream, EntryKind, VerifiedPackage};
use sandstorm_package::SpkManifest;
use sha2::{Digest, Sha256};
use std::ffi::CString;
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::sandbox::open_protected_directory;
use minidregg_spk_rpc::{decode_bridge_config, BridgeConfig};
use serde_json::{json, Value};

/// Standard import bound; operator appliance imports use their explicitly selected profile.
pub const MAX_DECOMPRESSED_PACKAGE_BYTES: usize = stream::Limits::DEFAULT.decoded_bytes as usize;
/// Modes inside the published image root, Sandstorm's (0644/0755/0755).
/// Root owns every entry and the sandbox binds the root read-only; the
/// sandbox still refuses a task-owned or group/world-writable image.
const IMAGE_FILE_MODE: u32 = 0o644;
const IMAGE_EXECUTABLE_MODE: u32 = 0o755;
const IMAGE_DIRECTORY_MODE: u32 = 0o755;

#[derive(Clone)]
pub struct InstalledPackage {
    pub directory: PathBuf,
    pub raw_sha256: String,
    /// Identity inputs from the same signature-verified Bread parse that
    /// produced the immutable image. These are hashes of exact signed bytes,
    /// not a Mini descriptor root or an admission decision.
    pub raw_sha256_bytes: [u8; 32],
    pub raw_length: u64,
    pub signed_manifest_sha256: [u8; 32],
    pub signed_bridge_config_sha256: Option<[u8; 32]>,
    /// Exact member bytes retained from the one signature-verified SPK parse.
    /// The bridge-only descriptor decoder consumes these, never a later image
    /// path or a second package parse.
    pub signed_bridge_config: Option<Vec<u8>>,
    /// Same-parse signed declaration. Never reread it from the extracted image.
    pub signed_data_config: Option<Vec<u8>>,
    pub manifest: SpkManifest,
}

/// Resolve only the immutable PUBLIC registry next to the protected packages
/// namespace. Neither the signed declaration nor any request supplies a host path.
pub(crate) fn open_signed_public_data(package: &InstalledPackage, app_uid: u32)
    -> io::Result<Option<crate::shared_data::SharedDataHandle>> {
    let Some(bytes) = package.signed_data_config.as_deref() else { return Ok(None); };
    let requirement = crate::shared_data::parse_signed_attachment(bytes)?;
    let packages = package.directory.parent().ok_or_else(|| invalid("package namespace absent"))?;
    if packages.file_name().and_then(|name| name.to_str()) != Some("packages") {
        return Err(invalid("public data requires the protected packages namespace"));
    }
    let root = packages.parent().ok_or_else(|| invalid("SPK namespace absent"))?;
    let store = root.join("public-data");
    crate::shared_data::open_published(&store, &requirement, app_uid).map(Some).map_err(|error| {
        io::Error::new(error.kind(), format!("signed public-data {} custody refused: {}", requirement.inventory_sha256_hex(), error))
    })
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn write_tree(
    spk: &VerifiedPackage,
    root: &Path,
    directories: &mut Vec<PathBuf>,
    links: &mut Vec<(PathBuf, String)>,
) -> io::Result<()> {
    for (index, entry) in spk.entries().iter().enumerate() {
        let path = root.join(&entry.path);
        match &entry.kind {
            EntryKind::Directory => {
                fs::DirBuilder::new().mode(0o700).create(&path)?;
                directories.push(path);
            }
            EntryKind::Symlink(target) => links.push((path, target.clone())),
            EntryKind::Regular { executable } => {
                let mut out = OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .mode(0o600)
                    .open(&path).ctx("open", &path)?;
                spk.copy_member(index, &mut out)?;
                out.set_permissions(fs::Permissions::from_mode(if *executable {
                    IMAGE_EXECUTABLE_MODE
                } else {
                    IMAGE_FILE_MODE
                }))?;
            }
        }
    }
    Ok(())
}

fn cleanup_staging(path: &Path) {
    fn make_removable(path: &Path) -> io::Result<()> {
        let metadata = fs::symlink_metadata(&path).ctx("inspect", &path)?;
        if metadata.is_dir() {
            fs::set_permissions(path, fs::Permissions::from_mode(0o700)).ctx("set permissions", &path)?;
            for entry in fs::read_dir(&path).ctx("list", &path)? {
                make_removable(&entry?.path())?;
            }
        }
        Ok(())
    }
    let _ = make_removable(path);
    let _ = fs::remove_dir_all(&path).ctx("remove", &path);
}

fn publish_no_replace(stage: &Path, destination: &Path) -> io::Result<()> {
    let stage = CString::new(stage.as_os_str().as_encoded_bytes())
        .map_err(|_| invalid("NUL in staging path"))?;
    let destination = CString::new(destination.as_os_str().as_encoded_bytes())
        .map_err(|_| invalid("NUL in destination path"))?;
    let result = unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            libc::AT_FDCWD,
            stage.as_ptr(),
            libc::AT_FDCWD,
            destination.as_ptr(),
            libc::RENAME_NOREPLACE,
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn verified_identity(spk: &VerifiedPackage, directory: PathBuf) -> io::Result<InstalledPackage> {
    if let Some(bytes) = &spk.data_config_bytes {
        crate::shared_data::parse_signed_attachment(bytes)?;
    }
    // A package from before bridgeConfig carries no member; it runs under the canonical empty
    // config (spk-rpc `default_bridge_config_bytes`: no permissions, roles, API path or
    // identity capabilities), whose fixed digest binds the descriptor like a signed member's.
    let bridge_config = spk
        .bridge_config_bytes
        .clone()
        .unwrap_or_else(minidregg_spk_rpc::default_bridge_config_bytes);
    let raw_sha256 = spk
        .raw_sha256
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect();
    Ok(InstalledPackage {
        directory,
        raw_sha256,
        raw_sha256_bytes: spk.raw_sha256,
        raw_length: spk.raw_length,
        signed_manifest_sha256: Sha256::digest(&spk.manifest_bytes).into(),
        signed_bridge_config_sha256: Some(Sha256::digest(&bridge_config).into()),
        signed_bridge_config: Some(bridge_config),
        signed_data_config: spk.data_config_bytes.clone(),
        manifest: spk.manifest.clone(),
    })
}

/// The verified identity of one file this process already qualified: the path, the profile and
/// the file's identity (device, inode, length, mode, owner, both times) when it was verified.
type QualifiedKey = (PathBuf, &'static str, (u64, u64, u64, u32, u32, i64, i64, i64, i64));
#[allow(clippy::type_complexity)]
static QUALIFIED: std::sync::Mutex<Vec<(QualifiedKey, InstalledPackage)>> = std::sync::Mutex::new(Vec::new());

fn qualified_key(input: &Path, profile: ImportProfile) -> Option<QualifiedKey> {
    let meta = fs::symlink_metadata(input).ok().filter(|meta| meta.is_file())?;
    Some((input.to_path_buf(), profile.as_str(), (meta.dev(), meta.ino(), meta.len(), meta.mode(), meta.uid(),
        meta.mtime(), meta.mtime_nsec(), meta.ctime(), meta.ctime_nsec())))
}

/// One signature verification per file per process: `grain install` qualifies the staged SPK and
/// then prepares INSTALL from the same file, which re-verified it whole (about 2 s for 37 MB).
/// The result is kept only when the file's identity was the same before and after the
/// verification, and taken only while the path still names that identity; a writer cannot set a
/// ctime back, so any change to the file verifies it again.
fn qualified_identity(input: &Path, parent: &Path, profile: ImportProfile) -> io::Result<InstalledPackage> {
    let before = qualified_key(input, profile);
    if let Some(key) = &before {
        let kept = QUALIFIED.lock().map_err(|_| invalid("qualification cache poisoned"))?;
        if let Some((_, package)) = kept.iter().find(|(kept, _)| kept == key) {
            return Ok(package.clone());
        }
    }
    let spk = stream::verify_in_private_temp_at_with_root_custody(input, parent, profile.limits(), crate::namespace_identity::root_owned)?;
    let verified = verified_identity(&spk, PathBuf::new())?;
    if before.is_some() && qualified_key(input, profile) == before {
        let mut kept = QUALIFIED.lock().map_err(|_| invalid("qualification cache poisoned"))?;
        kept.retain(|(key, _)| key.0 != input);
        kept.push((before.expect("checked"), verified.clone()));
    }
    Ok(verified)
}

/// Parse one signed SPK without publishing an image, using the standard profile.
pub fn qualify_bridge_spk(package: &Path) -> io::Result<(InstalledPackage, BridgeConfig)> {
    qualify_bridge_spk_with_profile(package, ImportProfile::Standard)
}

/// The caller selects this operator policy; no archive member can enlarge it.
pub fn qualify_bridge_spk_with_profile(
    package: &Path,
    profile: ImportProfile,
) -> io::Result<(InstalledPackage, BridgeConfig)> {
    let input = if package.is_absolute() {
        package.to_owned()
    } else {
        std::env::current_dir()?.join(package)
    };
    let parent = input
        .parent()
        .ok_or_else(|| invalid("package parent absent"))?;
    let verified = qualified_identity(&input, parent, profile)?;
    let member = verified
        .signed_bridge_config
        .as_deref()
        .ok_or_else(|| invalid("bridge-only SPK lacks signed config"))?;
    let bridge = decode_bridge_config(member).map_err(invalid)?;
    // saveIdentityCaps (identity_custody; SandstormApi save/restore/drop) and
    // expectAppHooks (the bridge answers getViewInfo through the app's hooks;
    // app-object restore stays unknownToken) are served. The refusal that
    // remains names the bridge-config field, so a survey of real packages can
    // say which Sandstorm facility a package needs.
    if let Some(path) = bridge.api_path.as_deref() {
        if let Err(error) = minidregg_signed_api_path::checked_prefix(path) {
            return Err(invalid(format!(
                "signed bridge requires unsupported physical profile: apiPath {path:?} ({error})"
            )));
        }
    }
    Ok((verified, bridge))
}

/// Exact signed bridge role source consumed by Mini's schema author. This
/// describes verified package metadata; only Mini derives the canonical
/// schema and descriptor roots and admits a lifecycle operation.
pub fn signed_schema_source(bridge: &BridgeConfig, signed_app_version: u32) -> Value {
    json!({
        "type":"minidregg-application-permission-schema-source-v1",
        "version":signed_app_version.to_string(),
        "permissions":bridge.view_info.permissions.iter().map(|permission| {
            json!({"name":permission.name,"obsolete":permission.obsolete})
        }).collect::<Vec<_>>(),
        "roles":bridge.view_info.roles.iter().map(|role| {
            json!({"permissions":role.permissions,"obsolete":role.obsolete,"default":role.default})
        }).collect::<Vec<_>>(),
        "denied":bridge.view_info.denied_permissions,
    })
}

/// Install a package only after its real SPK signature, archive hash, and Bread's
/// manifest parser accept it. `store` must already be an operator-owned protected
/// directory; its private staging child is never visible to an app account.
pub fn materialize_spk(package: &Path, store: &Path, app_uid: u32) -> io::Result<InstalledPackage> {
    materialize_spk_with_profile(package, store, app_uid, ImportProfile::Standard)
}

/// Selected policy is retained outside the untrusted archive root under image custody.
pub fn materialize_spk_with_profile(
    package: &Path,
    store: &Path,
    app_uid: u32,
    profile: ImportProfile,
) -> io::Result<InstalledPackage> {
    materialize_spk_with_scratch(package, store, app_uid, profile, None)
}

/// As above, with the raw and decoded spools of the intake in `scratch` (an operator-owned
/// protected directory on a disk with room for the profile's decoded bound) instead of in `store`.
/// The image is still extracted and published inside `store`, so it must only hold the image.
pub fn materialize_spk_with_scratch(
    package: &Path,
    store: &Path,
    app_uid: u32,
    profile: ImportProfile,
    scratch: Option<&Path>,
) -> io::Result<InstalledPackage> {
    materialize_staged(package, store, app_uid, profile, scratch)
}

fn materialize_staged(
    package: &Path,
    store: &Path,
    app_uid: u32,
    profile: ImportProfile,
    scratch: Option<&Path>,
) -> io::Result<InstalledPackage> {
    let _protected_store = open_protected_directory(store, app_uid, false)?;
    let _protected_scratch = scratch.map(|dir| open_protected_directory(dir, app_uid, false)).transpose()?;
    let limits = profile.limits();
    let input_length = fs::symlink_metadata(&package).ctx("inspect", &package)?.len();
    // Simultaneous raw+decoded spools, extracted image, and retained compressed SPK.
    // This is an available-space preflight, not a disk reservation. With a separate scratch the
    // spools (checked again inside `verify`) leave the store holding the image and the retained SPK.
    let store_need = match scratch {
        None => input_length.saturating_mul(2).saturating_add(limits.decoded_bytes.saturating_mul(2)),
        Some(_) => input_length.saturating_mul(2).saturating_add(limits.decoded_bytes),
    };
    stream::check_workspace(store, store_need, limits)?;
    let spk = stream::verify(package, scratch.unwrap_or(store), limits)?;
    let mut verified = verified_identity(&spk, PathBuf::new())?;
    let store_metadata = fs::symlink_metadata(&store).ctx("inspect", &store)?;
    if !store_metadata.is_dir() || store_metadata.file_type().is_symlink() {
        return Err(invalid("package store is not a real directory"));
    }
    let final_dir = store.join(format!("sha256-{}", verified.raw_sha256));
    if final_dir.exists() || final_dir.is_symlink() {
        return Err(io::Error::new(
            io::ErrorKind::AlreadyExists,
            "package image already installed",
        ));
    }
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|_| invalid("clock before epoch"))?
        .as_nanos();
    let stage = store.join(format!(".spk-stage-{}-{nonce}", std::process::id()));
    fs::DirBuilder::new().mode(0o700).create(&stage)?;
    let installed: io::Result<()> = (|| {
        let root = stage.join("root");
        fs::DirBuilder::new().mode(0o700).create(&root)?;
        let mut directories = vec![root.clone()];
        let mut links = Vec::new();
        write_tree(&spk, &root, &mut directories, &mut links)?;
        for mountpoint in ["var", "tmp", "proc", "dev"] {
            let path = root.join(mountpoint);
            if !path.exists() {
                fs::DirBuilder::new().mode(0o700).create(&path)?;
                directories.push(path);
            }
        }
        for (path, target) in links {
            std::os::unix::fs::symlink(target, path)?;
        }
        let mut stored_spk = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(stage.join("package.spk")).ctx("open", &(stage.join("package.spk")))?;
        spk.copy_raw(&mut stored_spk)?;
        stored_spk.set_permissions(fs::Permissions::from_mode(0o444))?;
        let manifest_json = serde_json::to_vec_pretty(&verified.manifest)
            .map_err(|e| invalid(format!("manifest serialization: {e}")))?;
        let mut manifest_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(stage.join("manifest.json")).ctx("open", &(stage.join("manifest.json")))?;
        manifest_file.write_all(&manifest_json)?;
        manifest_file.set_permissions(fs::Permissions::from_mode(0o444))?;
        let mut policy_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(stage.join("import-policy.json")).ctx("open", &(stage.join("import-policy.json")))?;
        policy_file.write_all(&serde_json::to_vec(&json!({"profile":profile.as_str()}))?)?;
        policy_file.set_permissions(fs::Permissions::from_mode(0o444))?;
        let mut identity_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(stage.join(VERIFIED_IDENTITY)).ctx("open", &(stage.join(VERIFIED_IDENTITY)))?;
        identity_file.write_all(&serde_json::to_vec(&verified_identity_record(&verified))?)?;
        identity_file.set_permissions(fs::Permissions::from_mode(0o444))?;
        for directory in directories.into_iter().rev() {
            fs::set_permissions(&directory, fs::Permissions::from_mode(IMAGE_DIRECTORY_MODE)).ctx("set permissions", &directory)?;
        }
        fs::set_permissions(&stage, fs::Permissions::from_mode(0o555)).ctx("set permissions", &stage)?;
        publish_no_replace(&stage, &final_dir)?;
        Ok(())
    })();
    if installed.is_err() {
        cleanup_staging(&stage);
    }
    installed?;
    verified.directory = final_dir;
    Ok(verified)
}

/// The identity the publishing parse derived, retained beside `package.spk` under the image's
/// own custody (0444 in the 0555 image). Signature verification is a function of the raw bytes,
/// so a wake that re-hashes `package.spk` to the SHA-256 this record and the image name carry
/// holds those same bytes, and the record is that parse's result for them.
const VERIFIED_IDENTITY: &str = "verified-identity.json";
const VERIFIED_IDENTITY_PROTOCOL: &str = "mini-spk-verified-identity-v1";
const MAX_VERIFIED_IDENTITY: u64 = 4 * 1024 * 1024;

fn verified_identity_record(verified: &InstalledPackage) -> Value {
    use crate::canonical::hex;
    json!({
        "protocol":VERIFIED_IDENTITY_PROTOCOL,
        "rawSha256":verified.raw_sha256,
        "rawLength":verified.raw_length,
        "signedManifestSha256":hex(&verified.signed_manifest_sha256),
        "signedBridgeConfig":verified.signed_bridge_config.as_deref().map(hex),
        "signedDataConfig":verified.signed_data_config.as_deref().map(hex),
    })
}

/// The retained identity of a published image, when it has one: `None` for an image published
/// before the record existed (the caller re-verifies the SPK). The record's custody is the
/// manifest's; `package.spk` (the descriptor `package_meta` described) is re-hashed whole and must
/// equal the recorded length and digest and the image's own name.
fn retained_verified_identity(
    image_dir: &Path,
    package_path: &Path,
    package_meta: &fs::Metadata,
) -> io::Result<Option<InstalledPackage>> {
    use crate::canonical::{hex, unhex, unhex_array};
    use std::io::Read;
    let path = image_dir.join(VERIFIED_IDENTITY);
    let meta = match fs::symlink_metadata(&path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
        other => other.ctx("inspect", &path)?,
    };
    if !meta.is_file()
        || meta.nlink() != 1
        || (!crate::namespace_identity::root_owned(&path, &meta) && meta.uid() != unsafe { libc::geteuid() })
        || meta.permissions().mode() & 0o777 != 0o444
        || meta.len() > MAX_VERIFIED_IDENTITY
    {
        return Err(invalid("installed verified identity custody changed"));
    }
    let record: Value = serde_json::from_slice(&fs::read(&path).ctx("read", &path)?)?;
    let text = |key: &str| record.get(key).and_then(Value::as_str);
    let bytes = |key: &str| -> io::Result<Option<Vec<u8>>> {
        match record.get(key) {
            Some(Value::Null) => Ok(None),
            Some(Value::String(value)) => unhex(value).map(Some).ok_or_else(|| invalid(format!("verified identity {key} malformed"))),
            _ => Err(invalid(format!("verified identity {key} absent"))),
        }
    };
    if text("protocol") != Some(VERIFIED_IDENTITY_PROTOCOL) || record.as_object().map(|o| o.len()) != Some(6) {
        return Err(invalid("installed verified identity protocol refused"));
    }
    let raw_sha256 = text("rawSha256").filter(|v| crate::canonical::hex64(v)).ok_or_else(|| invalid("verified identity rawSha256 malformed"))?;
    let raw_length = record.get("rawLength").and_then(Value::as_u64).ok_or_else(|| invalid("verified identity rawLength malformed"))?;
    let signed_manifest_sha256: [u8; 32] = text("signedManifestSha256").and_then(unhex_array).ok_or_else(|| invalid("verified identity signedManifestSha256 malformed"))?;
    let signed_bridge_config = bytes("signedBridgeConfig")?.ok_or_else(|| invalid("verified identity lacks the signed bridge config"))?;
    let signed_data_config = bytes("signedDataConfig")?;
    if image_dir.file_name().and_then(|name| name.to_str()) != Some(format!("sha256-{raw_sha256}").as_str()) {
        return Err(invalid("installed image path differs from signed SPK digest"));
    }
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(package_path)
        .ctx("open", &package_path)?;
    let opened = file.metadata()?;
    if (opened.dev(), opened.ino()) != (package_meta.dev(), package_meta.ino()) || opened.len() != raw_length {
        return Err(invalid("installed SPK custody changed"));
    }
    let mut digest = Sha256::new();
    let mut buffer = vec![0u8; 1024 * 1024];
    let mut length = 0u64;
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        length += count as u64;
        digest.update(&buffer[..count]);
    }
    let raw_sha256_bytes: [u8; 32] = digest.finalize().into();
    if length != raw_length || hex(&raw_sha256_bytes) != raw_sha256 {
        return Err(invalid("installed SPK bytes differ from their verified identity"));
    }
    if let Some(bytes) = &signed_data_config {
        crate::shared_data::parse_signed_attachment(bytes)?;
    }
    let manifest_path = image_dir.join("manifest.json");
    let manifest: SpkManifest = serde_json::from_slice(&fs::read(&manifest_path).ctx("read", &manifest_path)?)?;
    Ok(Some(InstalledPackage {
        directory: image_dir.to_owned(),
        raw_sha256: raw_sha256.to_owned(),
        raw_sha256_bytes,
        raw_length,
        signed_manifest_sha256,
        signed_bridge_config_sha256: Some(Sha256::digest(&signed_bridge_config).into()),
        signed_bridge_config: Some(signed_bridge_config),
        signed_data_config,
        manifest,
    }))
}

/// Reopen an operator-owned, content-addressed image for a resident wake.
/// An image published with its verified identity (`retained_verified_identity`) is re-hashed
/// and takes that identity; an older image is re-verified by the streaming reader in this
/// process, its signed bridge bytes, manifest and raw digest coming from that same parse.
/// Protected immutable image custody is separate from signature verification.
pub fn verify_installed_spk(image_dir: &Path, app_uid: u32) -> io::Result<InstalledPackage> {
    let _protected = open_protected_directory(image_dir, app_uid, false)?;
    let package_path = image_dir.join("package.spk");
    let package_meta = fs::symlink_metadata(&package_path).ctx("inspect", &package_path)?;
    if !package_meta.is_file()
        || package_meta.file_type().is_symlink()
        || package_meta.nlink() != 1
        || (!crate::namespace_identity::root_owned(&package_path, &package_meta) && package_meta.uid() != unsafe { libc::geteuid() })
        || package_meta.permissions().mode() & 0o777 != 0o444
    {
        return Err(invalid("installed SPK custody changed"));
    }
    let profile = retained_import_profile(image_dir)?;
    let verified = match retained_verified_identity(image_dir, &package_path, &package_meta)? {
        Some(verified) => verified,
        None => {
            let store = image_dir
                .parent()
                .ok_or_else(|| invalid("image store parent absent"))?;
            // The image store's custody is `open_protected_directory`'s above (the resident's own
            // rule, walked by descriptor). The stream reader's ancestor walk is not used here: a
            // resident wakes inside its user namespace, where root-owned ancestors of the store
            // (`/var/lib/mini-spk-worlds`, the world) carry the unmapped overflow uid and that walk
            // refused every START on Debian 13 ("scratch parent custody refused", 2026-10-27).
            let spk = stream::verify(&package_path, store, profile.limits())?;
            verified_identity(&spk, image_dir.to_owned())?
        }
    };
    if image_dir.file_name().and_then(|name| name.to_str())
        != Some(format!("sha256-{}", verified.raw_sha256).as_str())
    {
        return Err(invalid(
            "installed image path differs from signed SPK digest",
        ));
    }
    let manifest_path = image_dir.join("manifest.json");
    let manifest_meta = fs::symlink_metadata(&manifest_path).ctx("inspect", &manifest_path)?;
    if !manifest_meta.is_file()
        || manifest_meta.file_type().is_symlink()
        || manifest_meta.nlink() != 1
        || (!crate::namespace_identity::root_owned(&manifest_path, &manifest_meta) && manifest_meta.uid() != unsafe { libc::geteuid() })
        || manifest_meta.permissions().mode() & 0o777 != 0o444
        || manifest_meta.len() > 1024 * 1024
    {
        return Err(invalid("installed manifest custody changed"));
    }
    let recorded: SpkManifest = serde_json::from_slice(&fs::read(&manifest_path).ctx("read", &manifest_path)?)?;
    if recorded != verified.manifest {
        return Err(invalid("installed manifest differs from verified SPK"));
    }
    let root = image_dir.join("root");
    let _root = open_protected_directory(&root, app_uid, false)?;
    Ok(verified)
}

/// Only protected host metadata selects a larger re-verification bound. Legacy images
/// without this metadata retain the standard bound. A package member with this name
/// lives under root/ and is never consulted.
fn retained_import_profile(image_dir: &Path) -> io::Result<ImportProfile> {
    let path = image_dir.join("import-policy.json");
    let metadata = match fs::symlink_metadata(&path) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return Ok(ImportProfile::Standard)
        }
        other => other?,
    };
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.nlink() != 1
        || (!crate::namespace_identity::root_owned(&path, &metadata) && metadata.uid() != unsafe { libc::geteuid() })
        || metadata.permissions().mode() & 0o777 != 0o444
        || metadata.len() > 128
    {
        return Err(invalid("installed import policy custody changed"));
    }
    let value: Value = serde_json::from_slice(&fs::read(&path).ctx("read", &path)?)?;
    let object = value
        .as_object()
        .ok_or_else(|| invalid("invalid import policy"))?;
    if object.len() != 1 {
        return Err(invalid("invalid import policy fields"));
    }
    object
        .get("profile")
        .and_then(Value::as_str)
        .ok_or_else(|| invalid("missing import profile"))?
        .parse()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn materialized_profile_survives_wake_and_archive_cannot_choose_it() {
        let home = std::env::var_os("HOME").expect("test requires protected home directory");
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let scratch = PathBuf::from(home).join(format!(
            ".spk-materialize-test-{}-{nonce}",
            std::process::id()
        ));
        fs::DirBuilder::new().mode(0o700).create(&scratch).unwrap();
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                cleanup_staging(&self.0);
            }
        }
        let _cleanup = Cleanup(scratch.clone());
        let package = scratch.join("input.spk");
        let bytes = sandstorm_package::SpkBuilder::new()
            .manifest_json(r#"{"app_id":"ignored","app_title":"test","app_version":1,"continue_command":{"argv":["/app"]}}"#)
            .file(sandstorm_package::File::executable("app", b"fixture".to_vec()))
            .file(sandstorm_package::File::regular("import-policy.json", b"untrusted policy".to_vec()))
            .file(sandstorm_package::File::regular("minidregg-data.json", br#"{"schema":"minidregg-public-data-v1","inventory_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}"#.to_vec()))
            .pack(&ed25519_dalek::SigningKey::from_bytes(&[9;32]));
        fs::write(&package, &bytes).unwrap();
        let app_uid = unsafe { libc::geteuid() }.wrapping_add(1);
        let installed = materialize_spk_with_profile(
            &package,
            &scratch,
            app_uid,
            ImportProfile::OperatorAppliance,
        )
        .unwrap();
        assert_eq!(
            retained_import_profile(&installed.directory).unwrap(),
            ImportProfile::OperatorAppliance
        );
        assert_eq!(
            fs::read(installed.directory.join("root/app")).unwrap(),
            b"fixture"
        );
        assert_eq!(
            fs::read(installed.directory.join("root/import-policy.json")).unwrap(),
            b"untrusted policy"
        );
        assert_eq!(
            fs::read(installed.directory.join("package.spk")).unwrap(),
            bytes
        );
        let reopened = verify_installed_spk(&installed.directory, app_uid).unwrap();
        assert_eq!(reopened.raw_sha256_bytes, installed.raw_sha256_bytes);
        assert_eq!(reopened.signed_data_config, installed.signed_data_config);
        assert!(reopened.signed_data_config.is_some());
        // A declaration cannot turn an arbitrary materialization directory into a data registry.
        assert!(open_signed_public_data(&reopened, app_uid).is_err());
        assert_eq!(
            reopened.signed_manifest_sha256,
            installed.signed_manifest_sha256
        );
        assert_eq!(
            materialize_spk(&package, &scratch, app_uid)
                .err()
                .unwrap()
                .kind(),
            io::ErrorKind::AlreadyExists
        );
        let policy = installed.directory.join("import-policy.json");
        fs::set_permissions(&policy, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(verify_installed_spk(&installed.directory, app_uid).is_err());
        fs::set_permissions(&installed.directory, fs::Permissions::from_mode(0o755)).unwrap();
        fs::remove_file(&policy).unwrap();
        assert_eq!(
            retained_import_profile(&installed.directory).unwrap(),
            ImportProfile::Standard
        );
        assert!(verify_installed_spk(&installed.directory, app_uid).is_ok());
        std::os::unix::fs::symlink("root/import-policy.json", &policy).unwrap();
        assert!(verify_installed_spk(&installed.directory, app_uid).is_err());
    }

    /// A second qualification of the same file in one process takes the first's result, and a
    /// rewrite of the file (same length, same name) is verified again and refused.
    #[test]
    fn qualification_is_kept_per_file_identity_and_a_rewrite_is_verified_again() {
        let home = std::env::var_os("HOME").expect("test requires protected home directory");
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let scratch = PathBuf::from(home).join(format!(".spk-qualify-test-{}-{nonce}", std::process::id()));
        fs::DirBuilder::new().mode(0o700).create(&scratch).unwrap();
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                cleanup_staging(&self.0);
            }
        }
        let _cleanup = Cleanup(scratch.clone());
        let package = scratch.join("input.spk");
        let bytes = sandstorm_package::SpkBuilder::new()
            .manifest_json(r#"{"app_id":"ignored","app_title":"test","app_version":5,"continue_command":{"argv":["/app"]}}"#)
            .file(sandstorm_package::File::executable("app", b"fixture".to_vec()))
            .pack(&ed25519_dalek::SigningKey::from_bytes(&[6; 32]));
        fs::write(&package, &bytes).unwrap();
        let (first, _) = qualify_bridge_spk(&package).unwrap();
        let (second, _) = qualify_bridge_spk(&package).unwrap();
        assert_eq!(first.raw_sha256, second.raw_sha256);
        assert_eq!(first.signed_bridge_config, second.signed_bridge_config);
        let mut tampered = bytes.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 1;
        fs::write(&package, &tampered).unwrap();
        assert!(qualify_bridge_spk(&package).is_err());
    }

    /// A wake takes the publishing parse's identity only for the very bytes that parse saw: the
    /// retained identity equals a fresh re-verification field for field, a same-length rewrite of
    /// `package.spk` is refused, and so is a record under weaker custody. An image without the
    /// record (published before it existed) is re-verified and yields the same identity.
    #[test]
    fn retained_verified_identity_equals_reverification_and_binds_the_bytes() {
        let home = std::env::var_os("HOME").expect("test requires protected home directory");
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let scratch = PathBuf::from(home).join(format!(".spk-identity-test-{}-{nonce}", std::process::id()));
        fs::DirBuilder::new().mode(0o700).create(&scratch).unwrap();
        struct Cleanup(PathBuf);
        impl Drop for Cleanup {
            fn drop(&mut self) {
                cleanup_staging(&self.0);
            }
        }
        let _cleanup = Cleanup(scratch.clone());
        let package = scratch.join("input.spk");
        let bytes = sandstorm_package::SpkBuilder::new()
            .manifest_json(r#"{"app_id":"ignored","app_title":"test","app_version":3,"continue_command":{"argv":["/app"]}}"#)
            .file(sandstorm_package::File::executable("app", b"fixture".to_vec()))
            .file(sandstorm_package::File::regular("minidregg-data.json", br#"{"schema":"minidregg-public-data-v1","inventory_sha256":"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"}"#.to_vec()))
            .pack(&ed25519_dalek::SigningKey::from_bytes(&[7; 32]));
        fs::write(&package, &bytes).unwrap();
        let app_uid = unsafe { libc::geteuid() }.wrapping_add(1);
        let installed = materialize_spk(&package, &scratch, app_uid).unwrap();
        let dir = installed.directory.clone();
        let record = dir.join(VERIFIED_IDENTITY);
        assert!(record.is_file());
        let fields = |p: &InstalledPackage| {
            (p.directory.clone(), p.raw_sha256.clone(), p.raw_sha256_bytes, p.raw_length, p.signed_manifest_sha256,
                p.signed_bridge_config_sha256, p.signed_bridge_config.clone(), p.signed_data_config.clone(), p.manifest.clone())
        };
        let retained = verify_installed_spk(&dir, app_uid).unwrap();
        // The legacy path: the same image without its record is re-verified by the stream reader.
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o755)).unwrap();
        let kept = fs::read(&record).unwrap();
        fs::remove_file(&record).unwrap();
        let reverified = verify_installed_spk(&dir, app_uid).unwrap();
        assert!(fields(&retained) == fields(&reverified));
        // Back under its custody, the record is taken; under 0644 it is refused.
        fs::write(&record, &kept).unwrap();
        fs::set_permissions(&record, fs::Permissions::from_mode(0o644)).unwrap();
        assert!(verify_installed_spk(&dir, app_uid).is_err());
        fs::set_permissions(&record, fs::Permissions::from_mode(0o444)).unwrap();
        assert!(fields(&verify_installed_spk(&dir, app_uid).unwrap()) == fields(&reverified));
        // One flipped byte of package.spk, same length and same custody: refused by digest.
        let spk = dir.join("package.spk");
        let mut tampered = bytes.clone();
        let last = tampered.len() - 1;
        tampered[last] ^= 1;
        fs::remove_file(&spk).unwrap();
        fs::write(&spk, &tampered).unwrap();
        fs::set_permissions(&spk, fs::Permissions::from_mode(0o444)).unwrap();
        let refused = verify_installed_spk(&dir, app_uid).err().unwrap();
        assert!(refused.to_string().contains("differ from their verified identity"), "{refused}");
        // A whole other published image (its own package, record and tree, each self-consistent)
        // swapped in under this image's name is refused: its digest is not the name.
        let other_input = scratch.join("other.spk");
        fs::write(&other_input, sandstorm_package::SpkBuilder::new()
            .manifest_json(r#"{"app_id":"ignored","app_title":"other","app_version":4,"continue_command":{"argv":["/app"]}}"#)
            .file(sandstorm_package::File::executable("app", b"other".to_vec()))
            .pack(&ed25519_dalek::SigningKey::from_bytes(&[8; 32]))).unwrap();
        let other = materialize_spk(&other_input, &scratch, app_uid).unwrap();
        assert!(verify_installed_spk(&other.directory, app_uid).is_ok());
        fs::rename(&dir, scratch.join("set-aside")).unwrap();
        fs::rename(&other.directory, &dir).unwrap();
        let swapped = verify_installed_spk(&dir, app_uid).err().unwrap();
        assert!(swapped.to_string().contains("image path differs from signed SPK digest"), "{swapped}");
    }
}
