//! Signature-verified SPK archive materialization into a new immutable image.
//! Package decoding comes only from the pinned Bread `sandstorm-package` crate.

use sandstorm_package::{File as SpkFile, FileContent, Spk, SpkManifest};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::ffi::CString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use crate::sandbox::open_protected_directory;

const MAX_SPK_BYTES: u64 = 256 * 1024 * 1024;
const MAX_FILES: usize = 100_000;
const MAX_DEPTH: usize = 64;

pub struct InstalledPackage {
    pub directory: PathBuf,
    pub raw_sha256: String,
    pub manifest: SpkManifest,
}

fn invalid(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn valid_name(name: &str) -> io::Result<()> {
    if name.is_empty() || name == "." || name == ".." || name.contains('/')
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
    let mut depth = if target.starts_with('/') { 0 } else { parent.components().count() };
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

fn validate_tree(files: &[SpkFile], parent: &Path, depth: usize, count: &mut usize) -> io::Result<()> {
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
                    return Err(invalid(format!("{reserved} mountpoint is not a real directory")));
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
                let mode = if matches!(entry.content, FileContent::Executable(_)) { 0o555 } else { 0o444 };
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

/// Install a package only after Bread's real SPK signature, archive hash, and
/// manifest parser accept it. `store` must already be an operator-owned protected
/// directory; its private staging child is never visible to an app account.
pub fn materialize_spk(package: &Path, store: &Path, app_uid: u32) -> io::Result<InstalledPackage> {
    let mut package_file = OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(package)?;
    let metadata = package_file.metadata()?;
    if !metadata.is_file() || metadata.len() > MAX_SPK_BYTES {
        return Err(invalid("SPK input is not a bounded regular file"));
    }
    let mut raw = Vec::with_capacity(metadata.len() as usize);
    package_file.read_to_end(&mut raw)?;
    if raw.len() as u64 > MAX_SPK_BYTES {
        return Err(invalid("SPK input grew past limit"));
    }
    let raw_sha256 = format!("{:x}", Sha256::digest(&raw));
    let spk = Spk::parse(&raw).map_err(|e| invalid(format!("SPK verification failed: {e}")))?;
    let manifest = SpkManifest::from_spk(&spk)
        .map_err(|e| invalid(format!("SPK manifest failed: {e}")))?;
    let mut count = 0;
    validate_tree(&spk.archive.files, Path::new(""), 0, &mut count)?;

    let _protected_store = open_protected_directory(store, app_uid, false)?;
    let store_metadata = fs::symlink_metadata(store)?;
    if !store_metadata.is_dir() || store_metadata.file_type().is_symlink() {
        return Err(invalid("package store is not a real directory"));
    }
    let final_dir = store.join(format!("sha256-{raw_sha256}"));
    if final_dir.exists() || final_dir.is_symlink() {
        return Err(io::Error::new(io::ErrorKind::AlreadyExists, "package image already installed"));
    }
    let nonce = SystemTime::now().duration_since(UNIX_EPOCH)
        .map_err(|_| invalid("clock before epoch"))?.as_nanos();
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
        let mut stored_spk = OpenOptions::new().write(true).create_new(true).mode(0o600)
            .open(stage.join("package.spk"))?;
        stored_spk.write_all(&raw)?;
        stored_spk.set_permissions(fs::Permissions::from_mode(0o444))?;
        stored_spk.sync_all()?;
        let manifest_json = serde_json::to_vec_pretty(&manifest)
            .map_err(|e| invalid(format!("manifest serialization: {e}")))?;
        let mut manifest_file = OpenOptions::new().write(true).create_new(true).mode(0o600)
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
    Ok(InstalledPackage { directory: final_dir, raw_sha256, manifest })
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
