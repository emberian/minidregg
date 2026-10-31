//! Root-observed persistent /var identity for the resident START profile.
//! These bytes are physical evidence, never Mini launch authority by themselves.

use crate::io_context::IoContext;
use std::fs::{self, OpenOptions};
use std::io::{self, Read};
use std::os::fd::RawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::time::{Duration, SystemTime};
use crate::canonical::{decimal_u64 as decimal, hex64 as hex32};

/// The witness frame. The Lean kernel checks only that a witness begins with
/// `DREGG/SPK-VAR-CUSTODY/v1`; the suffix names the directory-and-project layout
/// (deploy/spk-host/VOLUMES.md). A `v2` rename is owed to the next Lean batch.
const TAG: &str = "DREGG/SPK-VAR-CUSTODY/v1+projdir";
const MAX_WITNESS: u64 = 4096;
const FRESHNESS: Duration = Duration::from_secs(120);
const FUTURE_TOLERANCE: Duration = Duration::from_secs(5);

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn value<'a>(line: &'a str, key: &str) -> io::Result<&'a str> {
    line.strip_prefix(key)
        .ok_or_else(|| invalid("volume witness field order refused"))
}

/// Where a Store's volumes live: the broker's grains root and the Store key.
/// Volume directory and witness names are `<store>-<resource>` below the root.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct VolumeSite {
    pub(crate) grains_root: PathBuf,
    pub(crate) store: String,
}

impl VolumeSite {
    pub(crate) fn new(grains_root: &Path, store: &str) -> io::Result<Self> {
        if !grains_root.is_absolute()
            || !crate::canonical::lower_hex_of(&store, 8)
        {
            return Err(invalid("volume site refused"));
        }
        Ok(Self {
            grains_root: grains_root.to_path_buf(),
            store: store.to_owned(),
        })
    }

    fn name(&self, resource: u64) -> String {
        format!("{}-{resource}", self.store)
    }

    pub(crate) fn mount(&self, resource: u64) -> PathBuf {
        self.grains_root.join("vars").join(self.name(resource))
    }

    fn witness(&self, resource: u64) -> PathBuf {
        self.grains_root
            .join("attest")
            .join(format!("{}.witness", self.name(resource)))
    }
}

#[derive(Debug)]
pub(crate) struct VolumeWitness {
    pub(crate) bytes: Vec<u8>,
    pub(crate) deployment_id: String,
    pub(crate) host_id: String,
    pub(crate) resource: u64,
    pub(crate) volume_id: String,
    pub(crate) app_uid: u32,
    pub(crate) quota_bytes: u64,
    pub(crate) mount: PathBuf,
    pub(crate) project_id: u32,
    pub(crate) directory_inode: u64,
    site: VolumeSite,
    file_dev: u64,
    file_ino: u64,
}

impl VolumeWitness {
    fn parse(bytes: Vec<u8>, site: &VolumeSite) -> io::Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_WITNESS as usize || bytes.last() != Some(&b'\n') {
            return Err(invalid("volume witness framing refused"));
        }
        let text =
            std::str::from_utf8(&bytes).map_err(|_| invalid("volume witness UTF-8 refused"))?;
        if text.bytes().any(|b| b == 0 || b == b'\r') {
            return Err(invalid("volume witness control byte refused"));
        }
        let lines: Vec<_> = text.trim_end_matches('\n').split('\n').collect();
        if lines.len() != 11 || lines[0] != TAG || text.ends_with("\n\n") {
            return Err(invalid("volume witness field count or tag refused"));
        }
        let deployment_id = value(lines[1], "deployment_id=")?.to_owned();
        let host_id = value(lines[2], "host_id=")?.to_owned();
        if !hex32(&deployment_id) || !hex32(&host_id) {
            return Err(invalid("volume witness identity refused"));
        }
        let resource = decimal(value(lines[3], "resource=")?)
            .filter(|n| *n > 0)
            .ok_or_else(|| invalid("volume witness resource refused"))?;
        let volume_id = value(lines[4], "volume_id=")?.to_owned();
        if !hex32(&volume_id) {
            return Err(invalid("volume witness source volume ID refused"));
        }
        let app_uid = decimal(value(lines[5], "app_uid=")?)
            .and_then(|n| u32::try_from(n).ok())
            .filter(|n| *n > 0)
            .ok_or_else(|| invalid("volume witness app UID refused"))?;
        let quota_bytes = decimal(value(lines[6], "quota_bytes=")?)
            .filter(|n| *n >= 64 * 1024 * 1024 && *n <= 16 * 1024 * 1024 * 1024)
            .ok_or_else(|| invalid("volume witness quota refused"))?;
        let project_id = decimal(value(lines[7], "project_id=")?)
            .and_then(|n| u32::try_from(n).ok())
            .filter(|n| *n > 0)
            .ok_or_else(|| invalid("volume witness project refused"))?;
        if !matches!(value(lines[8], "fs_type=")?, "ext4" | "xfs") {
            return Err(invalid("volume witness filesystem type refused"));
        }
        let directory_inode = decimal(value(lines[9], "directory_inode=")?)
            .filter(|n| *n > 0)
            .ok_or_else(|| invalid("volume witness directory inode refused"))?;
        let mount = value(lines[10], "directory=")?.to_owned();
        if Path::new(&mount) != site.mount(resource) {
            return Err(invalid("volume witness directory refused"));
        }
        Ok(Self {
            bytes,
            deployment_id,
            host_id,
            resource,
            volume_id,
            app_uid,
            quota_bytes,
            mount: PathBuf::from(mount),
            project_id,
            directory_inode: directory_inode,
            site: site.clone(),
            file_dev: 0,
            file_ino: 0,
        })
    }

    pub(crate) fn compare_open_mount(&self, persistent_var_fd: RawFd) -> io::Result<()> {
        let path_meta = fs::symlink_metadata(&self.mount).ctx("inspect", &self.mount)?;
        if !path_meta.is_dir()
            || !crate::os::app_owner(path_meta.uid(), self.app_uid)
            || path_meta.permissions().mode() & 0o777 != 0o700
        {
            return Err(invalid("attested /var mount path identity drift"));
        }
        let mut fd_stat = unsafe { std::mem::zeroed::<libc::stat>() };
        if unsafe { libc::fstat(persistent_var_fd, &mut fd_stat) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if fd_stat.st_dev != path_meta.dev() || fd_stat.st_ino != path_meta.ino() {
            return Err(invalid("preopened /var differs from attested mount"));
        }
        if fd_stat.st_ino != self.directory_inode {
            return Err(invalid("preopened /var is not the attested directory inode"));
        }
        Ok(())
    }

    /// For a descriptor opened for reading (the helper's own attestation check; the resident's O_PATH
    /// descriptor onto the app-private directory cannot be asked for its project). The open `/var`
    /// carries the attested project, with inheritance: the kernel's own record
    /// that this directory's blocks and inodes are charged to the bounded project.
    pub(crate) fn compare_open_project(&self, persistent_var_fd: RawFd) -> io::Result<()> {
        let (project, inherit) = crate::os::var_project(persistent_var_fd)?;
        if project != self.project_id || !inherit {
            return Err(invalid("preopened /var is not in the attested project"));
        }
        Ok(())
    }

    pub(crate) fn recheck_handoff(&self) -> io::Result<()> {
        let fresh = read_root_witness(&self.site, self.resource, false)?;
        if fresh.file_dev != self.file_dev
            || fresh.file_ino != self.file_ino
            || fresh.bytes != self.bytes
        {
            return Err(invalid("root volume attestation changed during START"));
        }
        Ok(())
    }
}

fn root_chain(path: &Path) -> io::Result<()> {
    if !path.is_absolute() {
        return Err(invalid("attestation path must be absolute"));
    }
    let mut prefix = PathBuf::from("/");
    for part in path.components().skip(1) {
        let Component::Normal(name) = part else {
            return Err(invalid("attestation path contains dot component"));
        };
        prefix.push(name);
        let meta = fs::symlink_metadata(&prefix).ctx("inspect", &prefix)?;
        if !meta.is_dir() || !crate::namespace_identity::root_owned(&prefix, &meta) || meta.permissions().mode() & 0o022 != 0 {
            return Err(invalid("attestation directory custody refused"));
        }
    }
    Ok(())
}

fn read_root_witness(
    site: &VolumeSite,
    resource: u64,
    require_recent: bool,
) -> io::Result<VolumeWitness> {
    if resource == 0 || resource > 999_999_999_999_999_999 {
        return Err(invalid("attestation resource outside supported profile"));
    }
    let path = site.witness(resource);
    root_chain(path.parent().ok_or_else(|| invalid("witness path"))?)?;
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(&path).ctx("open", &path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || !crate::namespace_identity::root_owned(&path, &meta)
        || meta.nlink() != 1
        || meta.permissions().mode() & 0o777 != 0o644
        || meta.len() == 0
        || meta.len() > MAX_WITNESS
    {
        return Err(invalid("root volume attestation file identity refused"));
    }
    if require_recent {
        let modified = meta.modified()?;
        let now = SystemTime::now();
        if now
            .duration_since(modified)
            .is_ok_and(|age| age > FRESHNESS)
            || modified
                .duration_since(now)
                .is_ok_and(|ahead| ahead > FUTURE_TOLERANCE)
        {
            return Err(invalid("root volume attestation not fresh"));
        }
    }
    let mut bytes = Vec::with_capacity(meta.len() as usize);
    file.by_ref()
        .take(MAX_WITNESS + 1)
        .read_to_end(&mut bytes)?;
    let after = file.metadata()?;
    if bytes.len() as u64 != meta.len()
        || after.dev() != meta.dev()
        || after.ino() != meta.ino()
        || after.len() != meta.len()
        || after.mtime() != meta.mtime()
        || after.mtime_nsec() != meta.mtime_nsec()
        || after.ctime() != meta.ctime()
        || after.ctime_nsec() != meta.ctime_nsec()
    {
        return Err(invalid("root volume attestation changed while read"));
    }
    let mut witness = VolumeWitness::parse(bytes, site)?;
    if witness.resource != resource {
        return Err(invalid("root volume attestation resource mismatch"));
    }
    witness.file_dev = meta.dev();
    witness.file_ino = meta.ino();
    Ok(witness)
}

/// The caller supplies only Mini-checked identifiers and private config pins.
/// The handoff is the broker's root-owned witness below the grains root; every
/// ancestor of it is checked root-owned and not group/world writable.
pub(crate) fn read_attested_volume(
    site: &VolumeSite,
    resource: u64,
    app_uid: u32,
    quota_bytes: u64,
    expected_deployment_id: &str,
    expected_host_id: &str,
    expected_source_volume_id: &str,
) -> io::Result<VolumeWitness> {
    let witness = read_root_witness(site, resource, true)?;
    if witness.app_uid != app_uid
        || witness.quota_bytes != quota_bytes
        || witness.deployment_id != expected_deployment_id
        || witness.host_id != expected_host_id
        || witness.volume_id != expected_source_volume_id
    {
        return Err(invalid(
            "root volume attestation differs from fixed resident pins",
        ));
    }
    Ok(witness)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example() -> Vec<u8> {
        format!("{TAG}\ndeployment_id={}\nhost_id={}\nresource=8401\nvolume_id={}\napp_uid=2401\nquota_bytes=67108864\nproject_id=1000123456\nfs_type=ext4\ndirectory_inode=7654\ndirectory=/var/lib/mini/grains/vars/0123456789abcdef-8401\n", "a".repeat(64), "b".repeat(64), "c".repeat(64)).into_bytes()
    }

    fn site() -> VolumeSite {
        VolumeSite::new(Path::new("/var/lib/mini/grains"), "0123456789abcdef").unwrap()
    }

    /// The attested-start boundary (`PreparedResident::start_attested`): the
    /// directory held open for fd5 must be the attested mount, by device and
    /// inode, with the app's ownership and mode. Each tamper is refused by name.
    #[test]
    fn compare_open_mount_refuses_a_replaced_or_loosened_mount_by_name() {
        use std::os::fd::AsRawFd;
        use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
        let root = std::env::temp_dir().join(format!(
            "spk-attested-mount-{}-{}",
            std::process::id(),
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()
        ));
        fs::DirBuilder::new().mode(0o700).create(&root).unwrap();
        let mount = root.join("var");
        fs::DirBuilder::new().mode(0o700).create(&mount).unwrap();
        let mut witness = VolumeWitness::parse(example(), &site()).unwrap();
        witness.app_uid = unsafe { libc::geteuid() };
        witness.mount = mount.clone();
        witness.directory_inode = fs::metadata(&mount).unwrap().ino();
        let held = fs::File::open(&mount).unwrap();
        witness.compare_open_mount(held.as_raw_fd()).unwrap();
        // Loosened: the mount is no longer the app's private directory.
        fs::set_permissions(&mount, fs::Permissions::from_mode(0o755)).unwrap();
        let loosened = witness.compare_open_mount(held.as_raw_fd()).unwrap_err();
        assert_eq!(loosened.to_string(), "attested /var mount path identity drift");
        fs::set_permissions(&mount, fs::Permissions::from_mode(0o700)).unwrap();
        witness.compare_open_mount(held.as_raw_fd()).unwrap();
        // Replaced: a fresh directory under the attested path, while fd5 still
        // holds the one that was verified (another inode).
        fs::rename(&mount, root.join("var.moved")).unwrap();
        fs::DirBuilder::new().mode(0o700).create(&mount).unwrap();
        let replaced = witness.compare_open_mount(held.as_raw_fd()).unwrap_err();
        assert_eq!(replaced.to_string(), "preopened /var differs from attested mount");
        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn stable_witness_parses_exact_root_profile() {
        let parsed = VolumeWitness::parse(example(), &site()).unwrap();
        assert_eq!(parsed.resource, 8401);
        assert_eq!(parsed.volume_id, "c".repeat(64));
        assert_eq!(parsed.bytes, example());
    }

    #[test]
    fn witness_refuses_path_and_field_ambiguity() {
        let mut wrong = String::from_utf8(example()).unwrap();
        wrong = wrong.replace("abcdef-8401", "abcdef-8402");
        assert!(VolumeWitness::parse(wrong.into_bytes(), &site()).is_err());
        let mut wrong = example();
        wrong.extend_from_slice(b"\n");
        assert!(VolumeWitness::parse(wrong, &site()).is_err());
        // Another Store's volume of the same resource is not this Store's.
        let other = VolumeSite::new(Path::new("/var/lib/mini/grains"), "fedcba9876543210").unwrap();
        assert!(VolumeWitness::parse(example(), &other).is_err());
    }

    #[test]
    fn witness_refuses_a_filesystem_without_project_quota_and_a_loop_era_layout() {
        let text = String::from_utf8(example()).unwrap();
        assert!(VolumeWitness::parse(text.replace("fs_type=ext4", "fs_type=zfs").into_bytes(), &site()).is_err());
        assert!(VolumeWitness::parse(text.replace("project_id=1000123456", "project_id=0").into_bytes(), &site()).is_err());
        // The loop-era 13-line layout and its tag are not this witness.
        let old = "DREGG/SPK-VAR-CUSTODY/v1\nbacking=/x.ext4\nbacking_fs=ext4:c254723a-a9b4-42d9-9f90-e08822823add\n";
        assert!(VolumeWitness::parse(old.as_bytes().to_vec(), &site()).is_err());
    }

    #[test]
    fn the_tag_keeps_the_prefix_the_lean_kernel_checks() {
        assert!(TAG.starts_with("DREGG/SPK-VAR-CUSTODY/v1"));
    }
}
