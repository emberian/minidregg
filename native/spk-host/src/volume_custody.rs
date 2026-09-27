//! Root-observed persistent /var identity for the resident START profile.
//! These bytes are physical evidence, never Mini launch authority by themselves.

#![allow(dead_code)] // Connected only after source-qualified v3 START routes.

use std::fs::{self, OpenOptions};
use std::io::{self, Read};
use std::os::fd::RawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::time::{Duration, SystemTime};

const TAG: &str = "DREGG/SPK-VAR-CUSTODY/v1";
const MAX_WITNESS: u64 = 4096;
const FRESHNESS: Duration = Duration::from_secs(120);
const FUTURE_TOLERANCE: Duration = Duration::from_secs(5);

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}

fn decimal(text: &str) -> Option<u64> {
    if text.is_empty()
        || (text.len() > 1 && text.starts_with('0'))
        || !text.bytes().all(|b| b.is_ascii_digit())
    {
        return None;
    }
    text.parse().ok()
}

fn hex32(text: &str) -> bool {
    text.len() == 64
        && text
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

fn uuid(text: &str) -> bool {
    let bytes = text.as_bytes();
    bytes.len() == 36
        && bytes.iter().enumerate().all(|(i, b)| {
            if matches!(i, 8 | 13 | 18 | 23) {
                *b == b'-'
            } else {
                b.is_ascii_hexdigit() && !b.is_ascii_uppercase()
            }
        })
}

fn stable_backing_fs(text: &str) -> bool {
    if let Some(id) = text
        .strip_prefix("ext4:")
        .or_else(|| text.strip_prefix("btrfs:"))
    {
        uuid(id)
    } else if let Some(id) = text.strip_prefix("zfs:") {
        decimal(id).is_some_and(|number| number > 0)
    } else {
        false
    }
}

fn value<'a>(line: &'a str, key: &str) -> io::Result<&'a str> {
    line.strip_prefix(key)
        .ok_or_else(|| invalid("volume witness field order refused"))
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
    pub(crate) backing_inode: u64,
    pub(crate) backing_fs: String,
    pub(crate) image_ext4_uuid: String,
    pub(crate) mount: PathBuf,
    file_dev: u64,
    file_ino: u64,
}

impl VolumeWitness {
    fn parse(bytes: Vec<u8>) -> io::Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_WITNESS as usize || bytes.last() != Some(&b'\n') {
            return Err(invalid("volume witness framing refused"));
        }
        let text =
            std::str::from_utf8(&bytes).map_err(|_| invalid("volume witness UTF-8 refused"))?;
        if text.bytes().any(|b| b == 0 || b == b'\r') {
            return Err(invalid("volume witness control byte refused"));
        }
        let lines: Vec<_> = text.trim_end_matches('\n').split('\n').collect();
        if lines.len() != 13 || lines[0] != TAG || text.ends_with("\n\n") {
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
        let backing = value(lines[7], "backing=")?;
        let expected_backing = format!("/var/lib/minidregg/spk/images/{resource}.ext4");
        if backing != expected_backing {
            return Err(invalid("volume witness backing path refused"));
        }
        let backing_fs = value(lines[8], "backing_fs=")?.to_owned();
        let backing_inode = decimal(value(lines[9], "backing_inode=")?)
            .filter(|n| *n > 0)
            .ok_or_else(|| invalid("volume witness backing inode refused"))?;
        let backing_size = decimal(value(lines[10], "backing_size=")?)
            .ok_or_else(|| invalid("volume witness backing size refused"))?;
        let image_ext4_uuid = value(lines[11], "image_ext4_uuid=")?.to_owned();
        let mount = value(lines[12], "mount=")?.to_owned();
        let expected_mount = format!("/var/lib/minidregg/spk/vars/{resource}");
        if backing_size != quota_bytes
            || !stable_backing_fs(&backing_fs)
            || !uuid(&image_ext4_uuid)
            || mount != expected_mount
        {
            return Err(invalid("volume witness filesystem mapping refused"));
        }
        Ok(Self {
            bytes,
            deployment_id,
            host_id,
            resource,
            volume_id,
            app_uid,
            quota_bytes,
            backing_inode,
            backing_fs,
            image_ext4_uuid,
            mount: PathBuf::from(mount),
            file_dev: 0,
            file_ino: 0,
        })
    }

    pub(crate) fn compare_open_mount(&self, persistent_var_fd: RawFd) -> io::Result<()> {
        let path_meta = fs::symlink_metadata(&self.mount)?;
        if !path_meta.is_dir()
            || path_meta.uid() != self.app_uid
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
        Ok(())
    }

    pub(crate) fn recheck_handoff(&self) -> io::Result<()> {
        let fresh = read_root_witness(self.resource, false)?;
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
        let meta = fs::symlink_metadata(&prefix)?;
        if !meta.is_dir() || meta.uid() != 0 || meta.permissions().mode() & 0o022 != 0 {
            return Err(invalid("attestation directory custody refused"));
        }
    }
    Ok(())
}

fn read_root_witness(resource: u64, require_recent: bool) -> io::Result<VolumeWitness> {
    if resource == 0 || resource > 999_999_999_999_999_999 {
        return Err(invalid("attestation resource outside supported profile"));
    }
    let parent = Path::new("/run/minidregg/spk/volume-attest");
    root_chain(parent)?;
    let path = parent.join(format!("{resource}.witness"));
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC)
        .open(path)?;
    let meta = file.metadata()?;
    if !meta.is_file()
        || meta.uid() != 0
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
    let mut witness = VolumeWitness::parse(bytes)?;
    if witness.resource != resource {
        return Err(invalid("root volume attestation resource mismatch"));
    }
    witness.file_dev = meta.dev();
    witness.file_ino = meta.ino();
    Ok(witness)
}

/// The caller supplies only Mini-checked identifiers and private config pins.
/// This reads the fixed root-owned handoff, not a caller-selected path.
pub(crate) fn read_attested_volume(
    resource: u64,
    app_uid: u32,
    quota_bytes: u64,
    expected_deployment_id: &str,
    expected_host_id: &str,
    expected_source_volume_id: &str,
) -> io::Result<VolumeWitness> {
    let witness = read_root_witness(resource, true)?;
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
        format!("{TAG}\ndeployment_id={}\nhost_id={}\nresource=8401\nvolume_id={}\napp_uid=2401\nquota_bytes=67108864\nbacking=/var/lib/minidregg/spk/images/8401.ext4\nbacking_fs=ext4:c254723a-a9b4-42d9-9f90-e08822823add\nbacking_inode=7654\nbacking_size=67108864\nimage_ext4_uuid=12345678-1234-1234-1234-123456789abc\nmount=/var/lib/minidregg/spk/vars/8401\n", "a".repeat(64), "b".repeat(64), "c".repeat(64)).into_bytes()
    }

    #[test]
    fn stable_witness_parses_exact_root_profile() {
        let parsed = VolumeWitness::parse(example()).unwrap();
        assert_eq!(parsed.resource, 8401);
        assert_eq!(parsed.volume_id, "c".repeat(64));
        assert_eq!(parsed.backing_inode, 7654);
        assert_eq!(parsed.bytes, example());
    }

    #[test]
    fn witness_refuses_path_and_field_ambiguity() {
        let mut wrong = String::from_utf8(example()).unwrap();
        wrong = wrong.replace("images/8401.ext4", "images/8402.ext4");
        assert!(VolumeWitness::parse(wrong.into_bytes()).is_err());
        let mut wrong = example();
        wrong.extend_from_slice(b"\n");
        assert!(VolumeWitness::parse(wrong).is_err());
    }

    #[test]
    fn zfs_dataset_guid_is_stable_backing_identity() {
        let text = String::from_utf8(example()).unwrap().replace(
            "backing_fs=ext4:c254723a-a9b4-42d9-9f90-e08822823add",
            "backing_fs=zfs:2533678408435541861",
        );
        assert!(VolumeWitness::parse(text.into_bytes()).is_ok());
        assert!(!stable_backing_fs("zfs:0"));
        assert!(!stable_backing_fs("zfs:tank"));
    }
}
