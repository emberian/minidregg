//! Linux custody boundary. The broker and resident run as the operator; the
//! resident/worker switch only mapped namespace identities and drop every cap.
//! Host-root volume operations are called by the installed one-shot helper.
//! `fixture-os` remains disposable modeled receiving, never a release route.

pub(crate) use minidregg_compatible_upgrade_custody::root_owner;

#[cfg(feature = "fixture-os")]
pub(crate) use crate::fixture_os::{
    app_owner, cgroup_events, child_assume_app_identity, drop_to_identity,
    holds_exactly_identity,
    pid_cgroup, runtime_units, self_cgroup, systemctl, var_filesystem,
    executes_as_app,
};
#[cfg(not(feature = "fixture-os"))]
pub(crate) use real::{
    app_owner, cgroup_events, child_assume_app_identity, drop_to_identity,
    holds_exactly_identity,
    pid_cgroup, runtime_units, self_cgroup, systemctl, var_filesystem,
    executes_as_app,
};

#[cfg(not(feature = "fixture-os"))]
mod real {
    /// Whether a file (owner, group, mode) is executable by the app identity the
    /// spawn switches to: its owner, group or other execute bit.
    pub(crate) fn executes_as_app(owner: u32, group: u32, mode: u32, app_uid: u32, app_gid: u32) -> bool {
        crate::spawn_gate::execute_mode_permits(owner, group, mode, app_uid, app_gid)
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

    /// The persistent `/var` at `path` (held open as `var_fd`, its parent as
    /// `parent_fd`): whether it is a filesystem mounted apart from its parent,
    /// and that filesystem's total bytes.
    pub(crate) fn var_filesystem(
        _path: &Path,
        parent_fd: RawFd,
        var_fd: RawFd,
    ) -> io::Result<(bool, u128)> {
        let stat = |fd: RawFd| -> io::Result<libc::stat> {
            let mut stat = unsafe { std::mem::zeroed::<libc::stat>() };
            if unsafe { libc::fstat(fd, &mut stat) } != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(stat)
        };
        let separate = stat(parent_fd)?.st_dev != stat(var_fd)?.st_dev;
        let mut volume = unsafe { std::mem::zeroed::<libc::statvfs>() };
        if unsafe { libc::fstatvfs(var_fd, &mut volume) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok((separate, (volume.f_blocks as u128) * (volume.f_frsize as u128)))
    }

    fn capability_sets_zero() -> io::Result<bool> {
        let status = std::fs::read_to_string("/proc/thread-self/status")?;
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
            || !crate::setid_bound::clear_capabilities()
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
                || !crate::setid_bound::clear_capabilities()
            {
                return false;
            }
        }
        libc::geteuid() == uid && libc::getegid() == gid
    }
}
