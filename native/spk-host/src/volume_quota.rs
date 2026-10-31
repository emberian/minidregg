//! The kernel interface of a project-quota volume directory: the project id and
//! inherit flag of a directory (`FS_IOC_{GET,SET}FSXATTR`), the block and inode
//! limits of a project (`quotactl_fd`: no block-device node is needed, which a
//! container lacks), and the bound a directory reports through `statfs`.
//! Every call takes an open descriptor; nothing here resolves a path.
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, RawFd};

const FS_IOC_FSGETXATTR: libc::c_ulong = 0x801c_581f;
const FS_IOC_FSSETXATTR: libc::c_ulong = 0x401c_5820;
pub(crate) const FS_XFLAG_PROJINHERIT: u32 = 0x200;

const SYS_QUOTACTL_FD: libc::c_long = 443;
const Q_GETQUOTA: u32 = 0x80_0007;
const Q_SETQUOTA: u32 = 0x80_0008;
const PRJQUOTA: u32 = 2;
const QIF_BLIMITS: u32 = 1;
const QIF_ILIMITS: u32 = 4;
const QIF_LIMITS: u32 = QIF_BLIMITS | QIF_ILIMITS;

pub(crate) const EXT4_MAGIC: i64 = 0xEF53;
pub(crate) const XFS_MAGIC: i64 = 0x5846_5342;

/// Bytes of disk quota per inode, the `mkfs.ext4` ratio the old per-volume images had.
pub(crate) const BYTES_PER_INODE: u64 = 16384;

#[repr(C)]
#[derive(Clone, Copy, Default)]
struct FsXattr {
    xflags: u32,
    extsize: u32,
    nextents: u32,
    projid: u32,
    cowextsize: u32,
    pad: [u8; 8],
}

/// `struct if_dqblk`; block limits are in 1024-byte units.
#[repr(C)]
#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) struct DqBlk {
    pub bhardlimit: u64,
    pub bsoftlimit: u64,
    pub curspace: u64,
    pub ihardlimit: u64,
    pub isoftlimit: u64,
    pub curinodes: u64,
    pub btime: u64,
    pub itime: u64,
    pub valid: u32,
}

/// Project id and inherit flag of the object `fd` names.
pub(crate) fn project_of(fd: RawFd) -> io::Result<(u32, bool)> {
    // The resident holds its `/var` as an O_PATH descriptor (opened component by component without
    // following links), and ioctl refuses those with EBADF. Re-open the very same inode through
    // /proc/self/fd for the read; fstatfs/fstatvfs elsewhere accept O_PATH as it is.
    let path = std::ffi::CString::new(format!("/proc/self/fd/{fd}")).expect("no NUL");
    let real = unsafe { libc::open(path.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_CLOEXEC) };
    if real < 0 { return Err(io::Error::last_os_error()); }
    let real = unsafe { std::os::fd::OwnedFd::from_raw_fd(real) };
    let mut x = FsXattr::default();
    if unsafe { libc::ioctl(real.as_raw_fd(), FS_IOC_FSGETXATTR as _, &mut x as *mut FsXattr) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok((x.projid, x.xflags & FS_XFLAG_PROJINHERIT != 0))
}

/// Give the directory `fd` project `projid` with inheritance. Needs privilege in
/// the init user namespace; the kernel refuses it elsewhere.
pub(crate) fn set_project(fd: RawFd, projid: u32) -> io::Result<()> {
    let mut x = FsXattr::default();
    if unsafe { libc::ioctl(fd, FS_IOC_FSGETXATTR as _, &mut x as *mut FsXattr) } != 0 {
        return Err(io::Error::last_os_error());
    }
    x.projid = projid;
    x.xflags |= FS_XFLAG_PROJINHERIT;
    if unsafe { libc::ioctl(fd, FS_IOC_FSSETXATTR as _, &x as *const FsXattr) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn quotactl(fd: RawFd, cmd: u32, id: u32, block: &mut DqBlk) -> io::Result<()> {
    let qcmd = (cmd << 8) | (PRJQUOTA & 0xff);
    let rc = unsafe {
        libc::syscall(SYS_QUOTACTL_FD, fd as libc::c_uint, qcmd as libc::c_uint, id as libc::c_uint, block as *mut DqBlk)
    };
    if rc != 0 { return Err(io::Error::last_os_error()); }
    Ok(())
}

/// The project's accounting and limits. `ESRCH` means project quota is not
/// enabled on the filesystem; `ENOSYS` a kernel older than 5.14.
pub(crate) fn get_quota(fd: RawFd, projid: u32) -> io::Result<DqBlk> {
    let mut block = DqBlk::default();
    quotactl(fd, Q_GETQUOTA, projid, &mut block)?;
    Ok(block)
}

/// Set equal hard and soft block limits (`bytes`, a multiple of 1024) and an
/// inode limit on the project.
pub(crate) fn set_limits(fd: RawFd, projid: u32, bytes: u64, inodes: u64) -> io::Result<()> {
    let mut block = DqBlk {
        bhardlimit: bytes / 1024,
        bsoftlimit: bytes / 1024,
        ihardlimit: inodes,
        isoftlimit: inodes,
        valid: QIF_LIMITS,
        ..DqBlk::default()
    };
    quotactl(fd, Q_SETQUOTA, projid, &mut block)
}

/// The limits that mean "this project id is unused": cleared at teardown.
pub(crate) fn clear_limits(fd: RawFd, projid: u32) -> io::Result<()> {
    set_limits(fd, projid, 0, 0)
}

/// Whether the kernel shows the project as claimed: any usage or any limit.
pub(crate) fn in_use(block: &DqBlk) -> bool {
    block.curspace != 0 || block.curinodes != 0 || block.bhardlimit != 0 || block.bsoftlimit != 0
        || block.ihardlimit != 0 || block.isoftlimit != 0
}

/// Filesystem type magic of `fd`.
pub(crate) fn fs_magic(fd: RawFd) -> io::Result<i64> {
    let mut s = unsafe { std::mem::zeroed::<libc::statfs>() };
    if unsafe { libc::fstatfs(fd, &mut s) } != 0 { return Err(io::Error::last_os_error()); }
    Ok(s.f_type as i64)
}

pub(crate) fn fs_name(magic: i64) -> Option<&'static str> {
    match magic { EXT4_MAGIC => Some("ext4"), XFS_MAGIC => Some("xfs"), _ => None }
}

/// The size `statfs` reports for the object `fd` names, in bytes. For a
/// directory with the inherit flag on a filesystem with project limits this is
/// the project limit (when it is below the filesystem size).
pub(crate) fn reported_bytes(fd: RawFd) -> io::Result<u128> {
    let mut s = unsafe { std::mem::zeroed::<libc::statvfs>() };
    if unsafe { libc::fstatvfs(fd, &mut s) } != 0 { return Err(io::Error::last_os_error()); }
    Ok((s.f_blocks as u128) * (s.f_frsize as u128))
}

/// Is this process in the initial user namespace? The kernel changes a project id (`chattr -p`,
/// FS_IOC_FSSETXATTR with fsx_projid) only there, so a container run with a user namespace
/// (`systemd-nspawn -U`, rootless runtimes) cannot create a bounded volume whatever it is bound to.
pub(crate) fn in_init_user_namespace(map: &str) -> bool {
    let mut lines = map.lines().filter(|l| !l.trim().is_empty());
    matches!((lines.next().map(|l| l.split_whitespace().collect::<Vec<_>>()), lines.next()),
        (Some(f), None) if f == ["0", "0", "4294967295"])
}

/// Refuse, by name, a filesystem that cannot hold a bounded volume.
pub(crate) fn require_project_quota(fd: RawFd) -> io::Result<&'static str> {
    if let Ok(map) = std::fs::read_to_string("/proc/self/uid_map") {
        if !in_init_user_namespace(&map) {
            return Err(io::Error::new(io::ErrorKind::PermissionDenied,
                "volume-helper: running in a user namespace (/proc/self/uid_map is not the identity map): the kernel lets only the initial user namespace set a project id, so no quota-bounded volume can be made here; run this container without a user namespace (not nspawn -U) with the project-quota directory bound in"));
        }
    }
    let magic = fs_magic(fd)?;
    let Some(name) = fs_name(magic) else {
        return Err(io::Error::new(io::ErrorKind::Unsupported, format!(
            "volume-helper: grains root is on filesystem type {magic:#x}, which has no project quota: put /var/lib/mini-spk-worlds on ext4 (mkfs.ext4 -O quota,project, mount -o prjquota) or xfs (mount -o prjquota); in a container, bind-mount such a host directory there")));
    };
    match get_quota(fd, 0) {
        Ok(_) => Ok(name),
        Err(e) if e.raw_os_error() == Some(libc::ESRCH) => Err(io::Error::new(io::ErrorKind::Unsupported, format!(
            "volume-helper: grains root is on {name} without project quota enabled: mount it with -o prjquota (ext4 also needs tune2fs -O quota,project -Q prjquota)"))),
        Err(e) if e.raw_os_error() == Some(libc::ENOSYS) => Err(io::Error::new(io::ErrorKind::Unsupported,
            "volume-helper: kernel lacks quotactl_fd (Linux 5.14 or newer required)")),
        Err(e) if e.raw_os_error() == Some(libc::EPERM) => Err(io::Error::new(io::ErrorKind::PermissionDenied,
            "volume-helper: no privilege for project quota (CAP_SYS_ADMIN in the init user namespace required)")),
        Err(e) => Err(e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn struct_layouts_match_the_kernel_abi() {
        assert_eq!(std::mem::size_of::<FsXattr>(), 28);
        assert_eq!(std::mem::size_of::<DqBlk>(), 72);
        // _IOR('X',31,28 bytes) and _IOW('X',32,28 bytes)
        assert_eq!(FS_IOC_FSGETXATTR, (2 << 30) | (28 << 16) | ((b'X' as u64) << 8) | 31);
        assert_eq!(FS_IOC_FSSETXATTR, (1 << 30) | (28 << 16) | ((b'X' as u64) << 8) | 32);
    }

    #[test]
    fn an_unused_project_has_no_usage_and_no_limit() {
        assert!(!in_use(&DqBlk::default()));
        assert!(in_use(&DqBlk { curspace: 1, ..DqBlk::default() }));
        assert!(in_use(&DqBlk { ihardlimit: 1, ..DqBlk::default() }));
    }

    #[test]
    fn only_the_identity_uid_map_is_the_init_user_namespace() {
        assert!(in_init_user_namespace("         0          0 4294967295\n"));
        assert!(!in_init_user_namespace("         0      65536      65536\n"));
        assert!(!in_init_user_namespace("0 0 1\n"));
        assert!(!in_init_user_namespace("0 0 4294967295\n1000 1000 1\n"));
    }

    #[test]
    fn the_filesystem_names_are_exactly_ext4_and_xfs() {
        assert_eq!(fs_name(EXT4_MAGIC), Some("ext4"));
        assert_eq!(fs_name(XFS_MAGIC), Some("xfs"));
        assert_eq!(fs_name(0x2fc1_2fc1), None); // zfs
        assert_eq!(fs_name(0x794c_7630), None); // overlayfs
    }
}
