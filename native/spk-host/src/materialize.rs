//! Signature-verified SPK archive materialization into a new immutable image.
//! Package decoding comes only from the pinned Bread `sandstorm-package` crate.

use sandstorm_package::{File as SpkFile, FileContent, Spk, SpkManifest};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::ffi::CString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::sandbox::open_protected_directory;
use minidregg_spk_rpc::{decode_bridge_config, BridgeConfig};
use serde_json::{json, Value};

const MAX_SPK_BYTES: u64 = 256 * 1024 * 1024;
/// The decompressed-package bound handed to Bread's parser in place of its
/// 256 MiB default. Measured 2026-10-01 (SPK-APPS): 4 of 10 market packages
/// decompress past 256 MiB (TT-RSS 298 MiB, Etherpad 341 MiB, Davros 477 MiB,
/// Wekan 525 MiB) and were refused `TooLarge`. The parse holds the plain
/// stream and the decoded archive at once, about 2.2x the decompressed size
/// (Wekan: 1.17 GB RSS, 16 s), so `spk-ingest` runs this with MemoryMax=2G.
/// An xz bomb is still refused at this bound, before signature work.
pub const MAX_DECOMPRESSED_PACKAGE_BYTES: usize = 768 * 1024 * 1024;
const MAX_FILES: usize = 100_000;
const MAX_DEPTH: usize = 64;
const MAX_SIGNED_BRIDGE_CONFIG_BYTES: usize = 64 * 1024;

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
    pub manifest: SpkManifest,
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn valid_name(name: &str) -> io::Result<()> {
    if name.is_empty()
        || name == "."
        || name == ".."
        || name.contains('/')
        || name.as_bytes().contains(&0)
    {
        return Err(invalid("invalid archive path component"));
    }
    Ok(())
}

fn valid_link(parent: &Path, target: &str) -> io::Result<()> {
    if target.is_empty() || target.as_bytes().contains(&0) {
        return Err(invalid("empty or NUL symlink target"));
    }
    // Absolute symlinks are common in real SPKs (e.g. libc.so -> /lib/...). In
    // the eventual sandbox they start at the package root. We never follow them
    // while materializing on the host, and reject any lexical escape above root.
    let mut depth = if target.starts_with('/') {
        0
    } else {
        parent.components().count()
    };
    for component in target.trim_start_matches('/').split('/') {
        match component {
            "" | "." => {}
            ".." if depth > 0 => depth -= 1,
            ".." => return Err(invalid("symlink target escapes package root")),
            _ => depth += 1,
        }
    }
    Ok(())
}

fn validate_tree(
    files: &[SpkFile],
    parent: &Path,
    depth: usize,
    count: &mut usize,
) -> io::Result<()> {
    if depth > MAX_DEPTH {
        return Err(invalid("archive nesting limit exceeded"));
    }
    let mut names = HashSet::new();
    for file in files {
        *count += 1;
        if *count > MAX_FILES {
            return Err(invalid("archive file count limit exceeded"));
        }
        valid_name(&file.name)?;
        if !names.insert(&file.name) {
            return Err(invalid("duplicate archive entry"));
        }
        match &file.content {
            FileContent::Directory(children) => {
                validate_tree(children, &parent.join(&file.name), depth + 1, count)?;
            }
            FileContent::Symlink(target) => valid_link(parent, target)?,
            FileContent::Regular(_) | FileContent::Executable(_) => {}
        }
    }
    if parent.as_os_str().is_empty() {
        for reserved in ["var", "tmp", "proc", "dev"] {
            if let Some(entry) = files.iter().find(|f| f.name == reserved) {
                if !matches!(entry.content, FileContent::Directory(_)) {
                    return Err(invalid(format!(
                        "{reserved} mountpoint is not a real directory"
                    )));
                }
            }
        }
    }
    Ok(())
}

fn write_tree(
    files: &[SpkFile],
    parent: &Path,
    directories: &mut Vec<PathBuf>,
    links: &mut Vec<(PathBuf, String)>,
) -> io::Result<()> {
    for entry in files {
        let path = parent.join(&entry.name);
        match &entry.content {
            FileContent::Directory(children) => {
                fs::DirBuilder::new().mode(0o700).create(&path)?;
                directories.push(path.clone());
                write_tree(children, &path, directories, links)?;
            }
            FileContent::Regular(bytes) | FileContent::Executable(bytes) => {
                let mut output = OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .mode(0o600)
                    .open(&path)?;
                output.write_all(bytes)?;
                let mode = if matches!(entry.content, FileContent::Executable(_)) {
                    0o555
                } else {
                    0o444
                };
                output.set_permissions(fs::Permissions::from_mode(mode))?;
                output.sync_all()?;
            }
            FileContent::Symlink(target) => links.push((path, target.clone())),
        }
    }
    Ok(())
}

fn sync_directory(path: &Path) -> io::Result<()> {
    File::open(path)?.sync_all()
}

fn cleanup_staging(path: &Path) {
    fn make_removable(path: &Path) -> io::Result<()> {
        let metadata = fs::symlink_metadata(path)?;
        if metadata.is_dir() {
            fs::set_permissions(path, fs::Permissions::from_mode(0o700))?;
            for entry in fs::read_dir(path)? {
                make_removable(&entry?.path())?;
            }
        }
        Ok(())
    }
    let _ = make_removable(path);
    let _ = fs::remove_dir_all(path);
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

fn bounded_spk(path: &Path) -> io::Result<Vec<u8>> {
    let file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)?;
    let metadata = file.metadata()?;
    if !metadata.is_file() || metadata.len() == 0 || metadata.len() > MAX_SPK_BYTES {
        return Err(invalid("SPK input is not a bounded regular file"));
    }
    let mut raw = Vec::with_capacity(metadata.len() as usize);
    file.take(MAX_SPK_BYTES + 1).read_to_end(&mut raw)?;
    if raw.len() as u64 > MAX_SPK_BYTES || raw.len() as u64 != metadata.len() {
        return Err(invalid("SPK input changed while reading"));
    }
    Ok(raw)
}

/// Return the signed tree and all descriptor inputs from one Bread parse.
/// Later schema decoding consumes the retained signed member, not a second
/// lookup in the extracted image.
fn verified_identity(raw: &[u8], directory: PathBuf) -> io::Result<(Spk, InstalledPackage)> {
    let raw_sha256_bytes: [u8; 32] = Sha256::digest(raw).into();
    let mut raw_sha256 = String::with_capacity(64);
    for byte in raw_sha256_bytes {
        raw_sha256.push_str(&format!("{byte:02x}"));
    }
    let raw_length = raw.len() as u64;
    let spk = Spk::parse_with_limit(raw, MAX_DECOMPRESSED_PACKAGE_BYTES)
        .map_err(|e| invalid(format!("SPK verification failed: {e}")))?;
    let manifest =
        SpkManifest::from_spk(&spk).map_err(|e| invalid(format!("SPK manifest failed: {e}")))?;
    let signed_manifest_sha256: [u8; 32] = Sha256::digest(
        spk.archive
            .find("sandstorm-manifest")
            .ok_or_else(|| invalid("verified SPK lacks signed manifest bytes"))?,
    )
    .into();
    let signed_bridge_config = spk
        .archive
        .find("sandstorm-http-bridge-config")
        .map(|bytes| {
            if bytes.is_empty() || bytes.len() > MAX_SIGNED_BRIDGE_CONFIG_BYTES {
                return Err(invalid(
                    "signed bridge config exceeds supported profile bound",
                ));
            }
            Ok(bytes.to_vec())
        })
        .transpose()?;
    let signed_bridge_config_sha256 = signed_bridge_config
        .as_ref()
        .map(|bytes| -> [u8; 32] { Sha256::digest(bytes).into() });
    let mut count = 0;
    validate_tree(&spk.archive.files, Path::new(""), 0, &mut count)?;
    Ok((
        spk,
        InstalledPackage {
            directory,
            raw_sha256,
            raw_sha256_bytes,
            raw_length,
            signed_manifest_sha256,
            signed_bridge_config_sha256,
            signed_bridge_config,
            manifest,
        },
    ))
}

/// Parse one signed SPK without publishing an image. The caller must run this
/// decoder inside a bounded offline service: Bread's XZ block allocation is
/// not bounded by the final archive size. A later INSTALL must materialize the
/// same raw SHA-256 and compare its retained signed members again.
pub fn qualify_bridge_spk(package: &Path) -> io::Result<(InstalledPackage, BridgeConfig)> {
    let raw = bounded_spk(package)?;
    let (_, verified) = verified_identity(&raw, PathBuf::new())?;
    let member = verified
        .signed_bridge_config
        .as_deref()
        .ok_or_else(|| invalid("bridge-only SPK lacks signed config"))?;
    let bridge = decode_bridge_config(member).map_err(invalid)?;
    // Each refusal names the bridge-config field, so a survey of real
    // packages can say which Sandstorm facility a package needs.
    if bridge.save_identity_caps {
        return Err(invalid(
            "signed bridge requires unsupported physical profile: saveIdentityCaps",
        ));
    }
    if bridge.expect_app_hooks {
        return Err(invalid(
            "signed bridge requires unsupported physical profile: expectAppHooks",
        ));
    }
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

/// Install a package only after Bread's real SPK signature, archive hash, and
/// manifest parser accept it. `store` must already be an operator-owned protected
/// directory; its private staging child is never visible to an app account.
pub fn materialize_spk(package: &Path, store: &Path, app_uid: u32) -> io::Result<InstalledPackage> {
    let raw = bounded_spk(package)?;
    let (spk, mut verified) = verified_identity(&raw, PathBuf::new())?;

    let _protected_store = open_protected_directory(store, app_uid, false)?;
    let store_metadata = fs::symlink_metadata(store)?;
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
        write_tree(&spk.archive.files, &root, &mut directories, &mut links)?;
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
            .open(stage.join("package.spk"))?;
        stored_spk.write_all(&raw)?;
        stored_spk.set_permissions(fs::Permissions::from_mode(0o444))?;
        stored_spk.sync_all()?;
        let manifest_json = serde_json::to_vec_pretty(&verified.manifest)
            .map_err(|e| invalid(format!("manifest serialization: {e}")))?;
        let mut manifest_file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(stage.join("manifest.json"))?;
        manifest_file.write_all(&manifest_json)?;
        manifest_file.set_permissions(fs::Permissions::from_mode(0o444))?;
        manifest_file.sync_all()?;
        for directory in directories.into_iter().rev() {
            fs::set_permissions(&directory, fs::Permissions::from_mode(0o555))?;
            sync_directory(&directory)?;
        }
        fs::set_permissions(&stage, fs::Permissions::from_mode(0o555))?;
        sync_directory(&stage)?;
        publish_no_replace(&stage, &final_dir)?;
        sync_directory(store)?;
        Ok(())
    })();
    if installed.is_err() {
        cleanup_staging(&stage);
    }
    installed?;
    verified.directory = final_dir;
    Ok(verified)
}

/// Reopen an operator-owned, content-addressed image for a resident wake.
/// Bread verifies the one retained `package.spk` again in this new process;
/// its signed bridge bytes, manifest and raw digest come from that same parse.
/// Protected immutable image custody is separate from signature verification.
pub fn verify_installed_spk(image_dir: &Path, app_uid: u32) -> io::Result<InstalledPackage> {
    let _protected = open_protected_directory(image_dir, app_uid, false)?;
    let package_path = image_dir.join("package.spk");
    let package_meta = fs::symlink_metadata(&package_path)?;
    if !package_meta.is_file()
        || package_meta.file_type().is_symlink()
        || package_meta.nlink() != 1
        || (package_meta.uid() != 0 && package_meta.uid() != unsafe { libc::geteuid() })
        || package_meta.permissions().mode() & 0o777 != 0o444
    {
        return Err(invalid("installed SPK custody changed"));
    }
    let raw = bounded_spk(&package_path)?;
    let (_, verified) = verified_identity(&raw, image_dir.to_owned())?;
    if image_dir.file_name().and_then(|name| name.to_str())
        != Some(format!("sha256-{}", verified.raw_sha256).as_str())
    {
        return Err(invalid(
            "installed image path differs from signed SPK digest",
        ));
    }
    let manifest_path = image_dir.join("manifest.json");
    let manifest_meta = fs::symlink_metadata(&manifest_path)?;
    if !manifest_meta.is_file()
        || manifest_meta.file_type().is_symlink()
        || manifest_meta.nlink() != 1
        || (manifest_meta.uid() != 0 && manifest_meta.uid() != unsafe { libc::geteuid() })
        || manifest_meta.permissions().mode() & 0o777 != 0o444
        || manifest_meta.len() > 1024 * 1024
    {
        return Err(invalid("installed manifest custody changed"));
    }
    let recorded: SpkManifest = serde_json::from_slice(&fs::read(manifest_path)?)?;
    if recorded != verified.manifest {
        return Err(invalid("installed manifest differs from verified SPK"));
    }
    let root = image_dir.join("root");
    let _root = open_protected_directory(&root, app_uid, false)?;
    Ok(verified)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_archive_escape_and_mountpoint_substitution() {
        assert!(valid_name("../escape").is_err());
        assert!(valid_name(".").is_err());
        assert!(valid_link(Path::new(""), "../escape").is_err());
        assert!(valid_link(Path::new("a"), "../../escape").is_err());
        assert!(valid_link(Path::new("a"), "../inside").is_ok());
        assert!(valid_link(Path::new("a"), "/lib/libc.so").is_ok());
        assert!(valid_link(Path::new("a"), "/../../escape").is_err());
        let files = vec![SpkFile {
            name: "var".into(),
            content: FileContent::Symlink("elsewhere".into()),
            mtime_ns: 0,
        }];
        assert!(validate_tree(&files, Path::new(""), 0, &mut 0).is_err());
    }
}
