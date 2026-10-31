//! Linux custody boundary. The broker and resident run as the operator; the
//! resident/worker switch only mapped namespace identities and drop every cap.
//! Host-root volume operations are called by the installed one-shot helper.
//! `fixture-os` remains disposable modeled receiving, never a release route.
use crate::io_context::IoContext;

pub(crate) use minidregg_compatible_upgrade_custody::root_owner;

#[cfg(feature = "fixture-os")]
pub(crate) use crate::fixture_os::{
    app_owner, cgroup_events, child_assume_app_identity, drop_to_identity,
    holds_exactly_identity,
    pid_cgroup, runtime_units, self_cgroup, systemctl, var_filesystem, var_project,
};
#[cfg(not(feature = "fixture-os"))]
pub(crate) use real::{
    app_owner, cgroup_events, child_assume_app_identity, drop_to_identity,
    holds_exactly_identity,
    pid_cgroup, runtime_units, self_cgroup, systemctl, var_filesystem, var_project,
};

#[cfg(not(feature = "fixture-os"))]
mod real {
    #[repr(C)]
    struct CapHeader {
        version: u32,
        pid: libc::c_int,
    }

    #[repr(C)]
    #[derive(Clone, Copy)]
    struct CapData {
        effective: u32,
        permitted: u32,
        inheritable: u32,
    }

    /// Async-signal-safe: clear the effective, permitted and inheritable sets
    /// (called in the forked gate child after the UID switch).
    fn clear_capabilities() -> bool {
        const LINUX_CAPABILITY_VERSION_3: u32 = 0x2008_0522;
        let header = CapHeader {
            version: LINUX_CAPABILITY_VERSION_3,
            pid: 0,
        };
        let data = [CapData {
            effective: 0,
            permitted: 0,
            inheritable: 0,
        }; 2];
        unsafe { libc::syscall(libc::SYS_capset, &header as *const CapHeader, data.as_ptr()) == 0 }
    }

    use std::io;
    use std::os::fd::RawFd;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    /// Whether a file owned by `uid` is owned by the app account `app_uid`.
    pub(crate) fn app_owner(uid: u32, app_uid: u32) -> bool {
        uid == app_uid
    }

    /// Where the broker renders runtime units.
    pub(crate) fn runtime_units() -> PathBuf {
        PathBuf::from(format!("/run/user/{}/systemd/user",unsafe{libc::geteuid()}))
    }

    /// The unit manager's command-line client; callers add every argument.
    pub(crate) fn systemctl() -> Command {
        Command::new("/usr/bin/systemctl")
    }

    /// `/proc/self/cgroup`.
    pub(crate) fn self_cgroup() -> io::Result<String> {
        std::fs::read_to_string("/proc/self/cgroup")
    }

    /// `/proc/<pid>/cgroup`.
    pub(crate) fn pid_cgroup(pid: u32) -> io::Result<String> {
        std::fs::read_to_string(format!("/proc/{pid}/cgroup"))
    }

    /// `/sys/fs/cgroup/<group>/cgroup.events`; `NotFound` once the group is gone.
    pub(crate) fn cgroup_events(group: &str) -> io::Result<String> {
        std::fs::read_to_string(
            Path::new("/sys/fs/cgroup")
                .join(group.trim_start_matches('/'))
                .join("cgroup.events"),
        )
    }

    /// The persistent `/var` at `path` (held open as `var_fd`, its parent as `parent_fd`, both
    /// O_PATH descriptors): whether it is bounded by a project quota, and the size `statfs` reports
    /// for it. A directory with the inherit flag under a project limit reports that limit as its
    /// filesystem size, so it is bounded exactly when it reports less than its parent's filesystem.
    /// (The project id itself is not read here: the resident runs as the operator, who cannot open
    /// the app-private directory for the ioctl. The witness pins the directory's inode and the
    /// helper, as root, set and verified its project.)
    pub(crate) fn var_filesystem(
        _path: &Path,
        parent_fd: RawFd,
        var_fd: RawFd,
    ) -> io::Result<(bool, u128)> {
        // The volume must be a directory of its parent's filesystem: a bind mount of another
        // (smaller) filesystem at /var reports a small size too.
        let (mut var_stat, mut parent_stat) = (unsafe { std::mem::zeroed::<libc::stat>() }, unsafe { std::mem::zeroed::<libc::stat>() });
        if unsafe { libc::fstat(var_fd, &mut var_stat) } != 0 || unsafe { libc::fstat(parent_fd, &mut parent_stat) } != 0 {
            return Err(io::Error::last_os_error());
        }
        if var_stat.st_dev != parent_stat.st_dev {
            return Err(io::Error::new(io::ErrorKind::InvalidData, "persistent /var is on another filesystem than its parent"));
        }
        let var = crate::volume_quota::reported_bytes(var_fd)?;
        let parent = crate::volume_quota::reported_bytes(parent_fd)?;
        Ok((var < parent, var))
    }

    /// The project id and inherit flag of the open `/var`.
    pub(crate) fn var_project(var_fd: RawFd) -> io::Result<(u32, bool)> {
        crate::volume_quota::project_of(var_fd)
    }

    fn capability_sets_zero() -> io::Result<bool> {
        use crate::io_context::IoContext;
        let status = std::fs::read_to_string("/proc/thread-self/status").ctx("read", &"/proc/thread-self/status")?;
        for field in ["CapInh:", "CapPrm:", "CapEff:", "CapBnd:", "CapAmb:"] {
            let value = status
                .lines()
                .find_map(|x| x.strip_prefix(field))
                .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "capability set absent"))?;
            if u64::from_str_radix(value.trim(), 16)
                .map_err(|_| io::Error::new(io::ErrorKind::InvalidInput, "capability set invalid"))?
                != 0
            {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Whether this thread is exactly `uid`/`gid` (real, effective, saved),
    /// with no supplementary groups, no_new_privs set and every capability set
    /// empty.
    pub(crate) fn holds_exactly_identity(uid: u32, gid: u32) -> io::Result<bool> {
        let (mut u0, mut u1, mut u2) = (0, 0, 0);
        let (mut g0, mut g1, mut g2) = (0, 0, 0);
        Ok(unsafe { libc::getresuid(&mut u0, &mut u1, &mut u2) } == 0
            && unsafe { libc::getresgid(&mut g0, &mut g1, &mut g2) } == 0
            && [u0, u1, u2] == [uid; 3]
            && [g0, g1, g2] == [gid; 3]
            && unsafe { libc::getgroups(0, std::ptr::null_mut()) } == 0
            && unsafe { libc::prctl(libc::PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) } == 1
            && capability_sets_zero()?)
    }

    /// Become exactly the mapped `uid`/`gid`: empty bounding set, no_new_privs,
    /// no supplementary groups, no capabilities, not dumpable.
    pub(crate) fn drop_to_identity(uid: u32, gid: u32) -> io::Result<()> {
        // Dropping bounding bits does not remove currently permitted SETID
        // before the switch.
        for cap in 0..64 {
            if unsafe { libc::prctl(libc::PR_CAPBSET_DROP, cap, 0, 0, 0) } != 0 {
                let e = io::Error::last_os_error();
                if e.raw_os_error() != Some(libc::EINVAL) {
                    return Err(e);
                }
            }
        }
        if unsafe { libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) } != 0
            || (unsafe { libc::getgroups(0, std::ptr::null_mut()) } != 0
                && unsafe { libc::setgroups(0, std::ptr::null()) } != 0)
            || unsafe { libc::setresgid(gid, gid, gid) } != 0
            || unsafe { libc::setresuid(uid, uid, uid) } != 0
            || unsafe { libc::prctl(libc::PR_CAP_AMBIENT, libc::PR_CAP_AMBIENT_CLEAR_ALL, 0, 0, 0) } != 0
            || !clear_capabilities()
            || unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 0, 0, 0, 0) } != 0
        {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }

    /// In the forked launch child, before exec: become exactly `uid`/`gid` with
    /// no supplementary groups and no capabilities. Async-signal-safe; false
    /// refuses the exec.
    pub(crate) unsafe fn child_assume_app_identity(uid: u32, gid: u32) -> bool {
        if libc::geteuid() != uid || libc::getegid() != gid {
            // Only the root audit harness switches here. The production app
            // worker has already assumed this exact identity, cleared every
            // capability/group and checked no_new_privs before parsing.
            if libc::setgroups(0, std::ptr::null()) != 0
                || libc::setresgid(gid, gid, gid) != 0
                || libc::setresuid(uid, uid, uid) != 0
            {
                return false;
            }
            // A non-root caller keeps its capability sets across a change
            // between two non-root UIDs; clear all of them so bubblewrap starts
            // with none.
            if libc::prctl(libc::PR_CAP_AMBIENT, libc::PR_CAP_AMBIENT_CLEAR_ALL, 0, 0, 0) != 0
                || !clear_capabilities()
            {
                return false;
            }
        }
        libc::geteuid() == uid && libc::getegid() == gid
    }
}

#[cfg(all(test, not(feature = "fixture-os"), target_os = "linux"))]
mod var_filesystem_tests {
    use std::os::fd::AsRawFd;

    #[test]
    fn a_volume_on_another_filesystem_than_its_parent_is_refused() {
        let root = std::fs::File::open("/").unwrap();
        // The same directory as its own parent is not bounded (it reports its parent's size).
        let (bounded, size) = super::var_filesystem(std::path::Path::new("/"), root.as_raw_fd(), root.as_raw_fd()).unwrap();
        assert!(!bounded && size > 0);
        // tmpfs under a parent on another filesystem: refused by name, whatever size it reports.
        if let Ok(shm) = std::fs::File::open("/dev/shm") {
            let root_dev = std::os::unix::fs::MetadataExt::dev(&root.metadata().unwrap());
            let shm_dev = std::os::unix::fs::MetadataExt::dev(&shm.metadata().unwrap());
            if root_dev != shm_dev {
                let refusal = super::var_filesystem(std::path::Path::new("/dev/shm"), root.as_raw_fd(), shm.as_raw_fd()).unwrap_err();
                assert!(refusal.to_string().contains("another filesystem"), "{refusal}");
            }
        }
    }
}
