//! The volume directory of one grain: a project-quota directory on the host
//! filesystem (deploy/spk-host/VOLUMES.md is the statement this answers to).
//! Create, verify, attest and destroy; every step is relative to a descriptor
//! and `O_NOFOLLOW`, so no name inside a grain-written tree is ever resolved.
use super::*;
use super::volume_custody::Dir;
use crate::volume_quota as quota;
use super::volume_custodian as custodian;

pub(crate) const TAG: &str = "DREGG/SPK-VAR-CUSTODY/v1+projdir";
/// Project ids are drawn from [BASE, BASE + 2^28): clear of ids an operator uses by hand.
pub(super) const PROJECT_BASE: u32 = 1_000_000_000;
pub(super) const PROJECT_PROBES: u32 = 256;
const MAX_DEPTH: usize = 4096;

/// Image bytes of an export of a `size_mib` volume: room for the ext4 metadata of a full volume.
pub(crate) fn export_image_bytes(size_mib: u64) -> u64 {
    let quota = size_mib * 1024 * 1024;
    quota + quota / 8 + 8 * 1024 * 1024
}

fn refuse(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::PermissionDenied, message.into())
}

pub(super) fn cstr(name: &str) -> io::Result<CString> {
    if name.is_empty() || matches!(name, "." | "..") || name.contains('/') {
        return Err(invalid("volume component refused"));
    }
    CString::new(name).map_err(|_| invalid("NUL volume component"))
}

pub(super) fn stat_at(dir: RawFd, name: &CStr) -> io::Result<Option<libc::stat>> {
    let mut s = unsafe { std::mem::zeroed::<libc::stat>() };
    if unsafe { libc::fstatat(dir, name.as_ptr(), &mut s, libc::AT_SYMLINK_NOFOLLOW) } != 0 {
        let e = io::Error::last_os_error();
        if e.raw_os_error() == Some(libc::ENOENT) { return Ok(None); }
        return Err(e);
    }
    Ok(Some(s))
}

pub(super) fn open_dir_at(dir: RawFd, name: &CStr) -> io::Result<File> {
    let fd = unsafe { libc::openat(dir, name.as_ptr(), libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC) };
    if fd < 0 { return Err(io::Error::last_os_error()); }
    Ok(unsafe { File::from_raw_fd(fd) })
}

fn is_dir(s: &libc::stat) -> bool { s.st_mode & libc::S_IFMT == libc::S_IFDIR }

/// The names in the directory `fd` (a duplicate is read; `fd` keeps its offset).
fn names(fd: RawFd) -> io::Result<Vec<CString>> {
    let dup = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if dup < 0 { return Err(io::Error::last_os_error()); }
    let dir = unsafe { libc::fdopendir(dup) };
    if dir.is_null() { let e = io::Error::last_os_error(); unsafe { libc::close(dup) }; return Err(e); }
    // The duplicate shares the directory offset with `fd`: read from the start, every time.
    unsafe { libc::rewinddir(dir) };
    let mut out = Vec::new();
    loop {
        unsafe { *libc::__errno_location() = 0 };
        let entry = unsafe { libc::readdir(dir) };
        if entry.is_null() {
            let e = io::Error::last_os_error();
            unsafe { libc::closedir(dir) };
            if e.raw_os_error() != Some(0) { return Err(e); }
            return Ok(out);
        }
        let name = unsafe { CStr::from_ptr((*entry).d_name.as_ptr()) };
        if name.to_bytes() != b"." && name.to_bytes() != b".." { out.push(name.to_owned()); }
    }
}

/// Visit every entry below the directory `fd`, depth first, never following a link and never
/// leaving the filesystem of the root. `f(parent, name, stat, depth)` runs for each entry before
/// its children; `after_dir` for a directory after them.
fn walk(
    fd: RawFd,
    dev: u64,
    depth: usize,
    visit: &mut dyn FnMut(RawFd, &CStr, &libc::stat) -> io::Result<()>,
    after_dir: &mut dyn FnMut(RawFd, &CStr) -> io::Result<()>,
) -> io::Result<()> {
    if depth > MAX_DEPTH { return Err(invalid("volume tree deeper than the walk bound")); }
    for name in names(fd)? {
        let Some(s) = stat_at(fd, &name)? else { continue };
        if s.st_dev as u64 != dev { return Err(invalid("volume tree crosses a filesystem")); }
        visit(fd, &name, &s)?;
        if is_dir(&s) {
            let child = open_dir_at(fd, &name)?;
            let cs = child.metadata()?;
            if cs.dev() != s.st_dev as u64 || cs.ino() != s.st_ino as u64 {
                return Err(invalid("volume tree entry switched during the walk"));
            }
            walk(child.as_raw_fd(), dev, depth + 1, visit, after_dir)?;
            drop(child);
            after_dir(fd, &name)?;
        }
    }
    Ok(())
}

fn raise_fd_limit() {
    let mut l = libc::rlimit { rlim_cur: 0, rlim_max: 0 };
    if unsafe { libc::getrlimit(libc::RLIMIT_NOFILE, &mut l) } == 0 {
        l.rlim_cur = l.rlim_max.min(MAX_DEPTH as libc::rlim_t * 2 + 256);
        unsafe { libc::setrlimit(libc::RLIMIT_NOFILE, &l) };
    }
}

/// Remove everything below `fd`, descriptor-relative.
pub(super) fn remove_contents(fd: RawFd) -> io::Result<()> {
    raise_fd_limit();
    let dev = File::from(dup(fd)?).metadata()?.dev();
    walk(
        fd,
        dev,
        0,
        &mut |parent, name, s| {
            if is_dir(s) { return Ok(()); }
            if unsafe { libc::unlinkat(parent, name.as_ptr(), 0) } != 0 { return Err(io::Error::last_os_error()); }
            Ok(())
        },
        &mut |parent, name| {
            if unsafe { libc::unlinkat(parent, name.as_ptr(), libc::AT_REMOVEDIR) } != 0 { return Err(io::Error::last_os_error()); }
            Ok(())
        },
    )
}

/// Make every entry below `fd` the grain's: `lchown` of anything else.
fn own_contents(fd: RawFd, uid: u32) -> io::Result<()> {
    raise_fd_limit();
    let dev = File::from(dup(fd)?).metadata()?.dev();
    walk(
        fd,
        dev,
        0,
        &mut |parent, name, s| {
            if s.st_uid != uid || s.st_gid != uid {
                if unsafe { libc::fchownat(parent, name.as_ptr(), uid, uid, libc::AT_SYMLINK_NOFOLLOW) } != 0 { return Err(io::Error::last_os_error()); }
            }
            Ok(())
        },
        &mut |_, _| Ok(()),
    )
}

/// (entries, bytes of regular files, newest ctime in ns) of the tree below `fd`: what a capture
/// compares before and after it copies.
pub(super) fn fingerprint(fd: RawFd) -> io::Result<(u64, u64, i128)> {
    raise_fd_limit();
    let dev = File::from(dup(fd)?).metadata()?.dev();
    let (mut count, mut bytes, mut newest) = (0u64, 0u64, 0i128);
    walk(
        fd,
        dev,
        0,
        &mut |_, _, s| {
            count += 1;
            if s.st_mode & libc::S_IFMT == libc::S_IFREG { bytes += s.st_size as u64; }
            newest = newest.max(s.st_ctime as i128 * 1_000_000_000 + s.st_ctime_nsec as i128);
            newest = newest.max(s.st_mtime as i128 * 1_000_000_000 + s.st_mtime_nsec as i128);
            Ok(())
        },
        &mut |_, _| Ok(()),
    )?;
    Ok((count, bytes, newest))
}

fn dup(fd: RawFd) -> io::Result<OwnedFd> {
    let d = unsafe { libc::fcntl(fd, libc::F_DUPFD_CLOEXEC, 3) };
    if d < 0 { return Err(io::Error::last_os_error()); }
    Ok(unsafe { OwnedFd::from_raw_fd(d) })
}

use std::ffi::CStr;
use std::os::fd::RawFd;

/// What a registered volume is, from the root-owned registration.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Registration {
    pub app_uid: u32,
    pub size_mib: u64,
    pub deployment_id: String,
    pub host_id: String,
    pub volume_id: String,
    pub project_id: u32,
}

impl Registration {
    pub(crate) fn text(&self) -> String {
        format!("app_uid={}\nsize_mib={}\ndeployment_id={}\nhost_id={}\nvolume_id={}\nproject_id={}\n",
            self.app_uid, self.size_mib, self.deployment_id, self.host_id, self.volume_id, self.project_id)
    }
    pub(crate) fn parse(text: &str) -> io::Result<Self> {
        let lines: Vec<&str> = text.strip_suffix('\n').unwrap_or("\u{0}").split('\n').collect();
        if lines.len() != 6 { return Err(refuse("volume-helper: registration shape refused")); }
        let field = |i: usize, key: &str| lines[i].strip_prefix(key).ok_or_else(|| refuse("volume-helper: registration field order refused"));
        let num = |s: &str| -> io::Result<u64> {
            if s.is_empty() || s.len() > 10 || s.starts_with('0') || !s.bytes().all(|b| b.is_ascii_digit()) { return Err(refuse("volume-helper: registration number refused")); }
            s.parse().map_err(|_| refuse("volume-helper: registration number refused"))
        };
        let r = Self {
            app_uid: u32::try_from(num(field(0, "app_uid=")?)?).map_err(|_| refuse("volume-helper: registration uid refused"))?,
            size_mib: num(field(1, "size_mib=")?)?,
            deployment_id: field(2, "deployment_id=")?.to_owned(),
            host_id: field(3, "host_id=")?.to_owned(),
            volume_id: field(4, "volume_id=")?.to_owned(),
            project_id: u32::try_from(num(field(5, "project_id=")?)?).map_err(|_| refuse("volume-helper: registration project refused"))?,
        };
        if !hex64(&r.deployment_id) || !hex64(&r.host_id) || !hex64(&r.volume_id) || r.project_id < PROJECT_BASE {
            return Err(refuse("volume-helper: registration identity refused"));
        }
        Ok(r)
    }
}

fn read_registration_named(volumes: &Dir, name: &str) -> io::Result<Option<Registration>> {
    let leaf = format!("{name}.conf");
    let c = cstr(&leaf)?;
    let Some(s) = stat_at(volumes.0.as_raw_fd(), &c)? else { return Ok(None) };
    if s.st_mode & libc::S_IFMT != libc::S_IFREG || s.st_uid != 0 || s.st_nlink != 1 || s.st_mode & 0o7777 != 0o600 || s.st_size > 4096 {
        return Err(refuse("volume-helper: registration custody refused"));
    }
    let f = volumes.read_root(&leaf)?;
    let mut text = String::new();
    f.take(4097).read_to_string(&mut text)?;
    Registration::parse(&text).map(Some)
}

/// A registered volume opened for capture.
pub(super) struct Target {
    pub dir: File,
    pub app_uid: u32,
    pub size_mib: u64,
}

/// The registered volume `name`, opened without following anything, with the grain's ownership
/// and project checked. Used by the capture, which names a volume by its registration only.
pub(super) fn capture_target(root: &Path, name: &str) -> io::Result<Target> {
    let grains = Dir::absolute(root, &[0])?;
    let volumes = grains.directory("volumes", &[0])?;
    let vars = grains.directory("vars", &[0])?;
    let reg = read_registration_named(&volumes, name)?.ok_or_else(|| refuse("volume-helper: volume registration absent"))?;
    let dir = open_dir_at(vars.0.as_raw_fd(), &cstr(name)?).map_err(|_| refuse("volume-helper: volume directory missing or symlinked"))?;
    let m = dir.metadata()?;
    if m.uid() != reg.app_uid || m.mode() & 0o7777 != 0o700 || m.dev() != vars.0.metadata()?.dev() {
        return Err(refuse("volume-helper: volume directory owner, mode or filesystem drift"));
    }
    let (project, inherit) = quota::project_of(dir.as_raw_fd())?;
    if project != reg.project_id || !inherit { return Err(refuse("volume-helper: volume project drift")); }
    Ok(Target { dir, app_uid: reg.app_uid, size_mib: reg.size_mib })
}

/// The coordinates a verb names; everything else is read from root-owned state.
pub(crate) struct Volume<'a> {
    pub root: &'a Path,
    pub store: &'a str,
    pub grain: &'a str,
    pub app_uid: u32,
    pub size_mib: u64,
    pub volume_id: &'a str,
    pub deployment_id: &'a str,
    pub host_id: &'a str,
    /// The host-side custodian's socket when this helper runs inside a user namespace, where the
    /// kernel will not let it set a project id or a quota. `None`: do it here (init namespace).
    pub custodian: Option<&'a Path>,
}

/// What `verify` observed about the live directory.
pub(crate) struct Observed {
    pub project_id: u32,
    pub fs_type: &'static str,
    pub inode: u64,
    pub dev: u64,
    pub path: PathBuf,
}

pub(super) fn deterministic_project(name: &str, probe: u32) -> u32 {
    let digest = Sha256::digest(format!("mini-spk-volume-project/v1\0{name}").as_bytes());
    let h = u32::from_be_bytes([digest[0], digest[1], digest[2], digest[3]]) & 0x0fff_ffff;
    PROJECT_BASE + (h.wrapping_add(probe)) % (1 << 28)
}

impl Volume<'_> {
    fn name(&self) -> String { volume_name(self.store, self.grain) }
    fn quota_bytes(&self) -> u64 { self.size_mib * 1024 * 1024 }
    pub(crate) fn path(&self) -> PathBuf { self.root.join("vars").join(self.name()) }

    fn layout(&self, create: bool) -> io::Result<(Dir, Dir, Dir, Dir)> {
        let grains = Dir::absolute(self.root, &[0])?;
        let sub = |name: &str, mode: u32| -> io::Result<Dir> {
            let c = cstr(name)?;
            if create && stat_at(grains.0.as_raw_fd(), &c)?.is_none() {
                if unsafe { libc::mkdirat(grains.0.as_raw_fd(), c.as_ptr(), mode) } != 0 { return Err(io::Error::last_os_error()); }
                let d = grains.directory(name, &[0])?;
                if unsafe { libc::fchmod(d.0.as_raw_fd(), mode) } != 0 { return Err(io::Error::last_os_error()); }
                return Ok(d);
            }
            let d = grains.directory(name, &[0])?;
            if d.0.metadata()?.mode() & 0o7777 != mode { return Err(refuse(format!("volume-helper: {name} directory mode drift"))); }
            Ok(d)
        };
        // `vars` is traversable by the grains (0711); `volumes` is root's.
        let volumes = sub("volumes", 0o700)?;
        let vars = sub("vars", 0o711)?;
        let attest = sub("attest", 0o755)?;
        Ok((grains, volumes, vars, attest))
    }

    fn read_registration(&self, volumes: &Dir) -> io::Result<Option<Registration>> {
        read_registration_named(volumes, &self.name())
    }

    /// The registration, which must exist and equal the request on every field the request names.
    pub(crate) fn registered(&self) -> io::Result<Registration> {
        let (_, volumes, _, _) = self.layout(false)?;
        let r = self.read_registration(&volumes)?.ok_or_else(|| refuse("volume-helper: volume registration absent"))?;
        if r.app_uid != self.app_uid || r.size_mib != self.size_mib || r.deployment_id != self.deployment_id
            || r.host_id != self.host_id || r.volume_id != self.volume_id {
            return Err(refuse("volume-helper: exact registration differs from request"));
        }
        Ok(r)
    }

    /// Claim a project id: the first of a deterministic probe sequence that the kernel shows
    /// unused. Held under the host-wide claim lock by the caller.
    fn claim_project(&self, vars: &Dir) -> io::Result<u32> {
        for probe in 0..PROJECT_PROBES {
            let id = deterministic_project(&self.name(), probe);
            if !quota::in_use(&quota::get_quota(vars.0.as_raw_fd(), id)?) { return Ok(id); }
        }
        Err(refuse("volume-helper: no unused project id in the probe sequence"))
    }

    fn claim_lock(&self) -> io::Result<File> {
        let parent = self.root.parent().ok_or_else(|| invalid("grains root has no parent"))?;
        let dir = Dir::absolute(parent, &[0])?;
        let c = cstr(".project-claim.lock")?;
        let fd = unsafe { libc::openat(dir.0.as_raw_fd(), c.as_ptr(), libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC, 0o600) };
        if fd < 0 { return Err(io::Error::last_os_error()); }
        let f = unsafe { File::from_raw_fd(fd) };
        let m = f.metadata()?;
        if !m.is_file() || m.uid() != 0 || m.nlink() != 1 || m.mode() & 0o777 != 0o600 { return Err(refuse("volume-helper: project claim lock custody refused")); }
        if unsafe { libc::flock(f.as_raw_fd(), libc::LOCK_EX) } != 0 { return Err(io::Error::last_os_error()); }
        Ok(f)
    }

    /// Whether the directory is present (a registered volume that a status inventory lists).
    pub(crate) fn present(&self) -> io::Result<bool> {
        let vars = Dir::absolute(self.root, &[0])?.directory("vars", &[0])?;
        Ok(stat_at(vars.0.as_raw_fd(), &cstr(&self.name())?)?.is_some())
    }

    /// Everything G1 to G4 says of the live directory, re-read from the kernel.
    pub(crate) fn verify(&self) -> io::Result<Observed> {
        let reg = self.registered()?;
        let vars = Dir::absolute(self.root, &[0])?.directory("vars", &[0])?;
        let name = self.name();
        let c = cstr(&name)?;
        let s = stat_at(vars.0.as_raw_fd(), &c)?.ok_or_else(|| refuse("volume-helper: volume directory absent"))?;
        let dir = open_dir_at(vars.0.as_raw_fd(), &c).map_err(|_| refuse("volume-helper: volume directory missing or symlinked"))?;
        let m = dir.metadata()?;
        if m.dev() != s.st_dev as u64 || m.ino() != s.st_ino as u64 { return Err(refuse("volume-helper: volume directory switched")); }
        if m.uid() != self.app_uid || m.mode() & 0o7777 != 0o700 { return Err(refuse("volume-helper: volume directory owner or mode drift")); }
        if m.dev() != vars.0.metadata()?.dev() { return Err(refuse("volume-helper: volume directory is on another filesystem than vars")); }
        let fs_type = self.require_quota_fs(dir.as_raw_fd())?;
        let (project, inherit) = quota::project_of(dir.as_raw_fd())?;
        if project != reg.project_id || !inherit {
            return Err(refuse(format!("volume-helper: volume project drift: directory has project {project} inherit={inherit}, registered {}", reg.project_id)));
        }
        let limits = self.limits_of(dir.as_raw_fd(), project)?;
        let bytes = self.quota_bytes();
        if limits.bhardlimit != bytes / 1024 || limits.bsoftlimit != bytes / 1024
            || limits.ihardlimit != bytes / quota::BYTES_PER_INODE || limits.isoftlimit != bytes / quota::BYTES_PER_INODE {
            return Err(refuse("volume-helper: volume quota drift"));
        }
        let reported = quota::reported_bytes(dir.as_raw_fd())?;
        if reported == 0 || reported > bytes as u128 { return Err(refuse("volume-helper: volume reports a size beyond its quota")); }
        Ok(Observed { project_id: project, fs_type, inode: m.ino(), dev: m.dev(), path: self.path() })
    }

    /// The kernel's project-quota requirement for the filesystem under `fd`. With a custodian the
    /// kernel-privileged checks are its (it refuses to start or to create without them); here only
    /// the filesystem type, which any namespace can read.
    fn require_quota_fs(&self, fd: RawFd) -> io::Result<&'static str> {
        if self.custodian.is_none() { return quota::require_project_quota(fd); }
        quota::fs_name(quota::fs_magic(fd)?).ok_or_else(|| refuse("volume-helper: grains root is not on ext4 or xfs"))
    }

    /// The project's limits as the kernel holds them: read here, or by the custodian when this
    /// process cannot (`quotactl` needs the init user namespace).
    fn limits_of(&self, fd: RawFd, project: u32) -> io::Result<quota::DqBlk> {
        match self.custodian {
            None => quota::get_quota(fd, project),
            Some(socket) => {
                let r = custodian::usage(socket, &self.name())?;
                if r.get("project")? != project as u64 { return Err(refuse("volume-helper: custodian names another project")); }
                Ok(quota::DqBlk { bhardlimit: r.get("bhard_kib")?, bsoftlimit: r.get("bsoft_kib")?,
                    ihardlimit: r.get("ihard")?, isoftlimit: r.get("isoft")?, curspace: r.get("cur_bytes")?, curinodes: r.get("cur_inodes")?, ..quota::DqBlk::default() })
            }
        }
    }

    fn witness_text(&self, o: &Observed) -> String {
        format!("{TAG}\ndeployment_id={}\nhost_id={}\nresource={}\nvolume_id={}\napp_uid={}\nquota_bytes={}\nproject_id={}\nfs_type={}\ndirectory_inode={}\ndirectory_dev={}\ndirectory={}\n",
            self.deployment_id, self.host_id, self.grain, self.volume_id, self.app_uid, self.quota_bytes(),
            o.project_id, o.fs_type, o.inode, o.dev, o.path.display())
    }

    /// Publish the root-written witness the resident checks. Re-observed before and after the
    /// atomic rename: a drift in between removes it.
    pub(crate) fn attest(&self) -> io::Result<()> {
        let first = self.verify()?;
        let text = self.witness_text(&first);
        if text.len() > 4096 { return Err(refuse("volume-helper: volume witness exceeds the Mini bound")); }
        let (_, _, _, attest) = self.layout(false)?;
        let leaf = format!("{}.witness", self.name());
        let tmp = format!(".witness.{}.{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).map_err(|_| invalid("clock"))?.as_nanos());
        let (ct, cl) = (cstr(&tmp)?, cstr(&leaf)?);
        let fd = unsafe { libc::openat(attest.0.as_raw_fd(), ct.as_ptr(), libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC, 0o644) };
        if fd < 0 { return Err(io::Error::last_os_error()); }
        let mut f = unsafe { File::from_raw_fd(fd) };
        let result = (|| -> io::Result<()> {
            unsafe { libc::fchmod(f.as_raw_fd(), 0o644) };
            f.write_all(text.as_bytes())?;
            if self.witness_text(&self.verify()?) != text { return Err(refuse("volume-helper: volume custody drift before publication")); }
            if unsafe { libc::renameat(attest.0.as_raw_fd(), ct.as_ptr(), attest.0.as_raw_fd(), cl.as_ptr()) } != 0 { return Err(io::Error::last_os_error()); }
            Ok(())
        })();
        if result.is_err() { unsafe { libc::unlinkat(attest.0.as_raw_fd(), ct.as_ptr(), 0) }; }
        result?;
        if self.witness_text(&self.verify()?) != text {
            unsafe { libc::unlinkat(attest.0.as_raw_fd(), cl.as_ptr(), 0) };
            return Err(refuse("volume-helper: volume custody drift after publication"));
        }
        Ok(())
    }

    /// Create the volume: claim a project, make and bound the directory, import, register.
    /// A failure removes everything this call made.
    pub(crate) fn create(&self, import: Option<&Path>) -> io::Result<()> {
        if !(64..=16384).contains(&self.size_mib) { return Err(refuse("volume-helper: volume quota refused")); }
        let (_, volumes, vars, _) = self.layout(true)?;
        self.require_quota_fs(vars.0.as_raw_fd())?;
        let name = self.name();
        let c = cstr(&name)?;
        if self.read_registration(&volumes)?.is_some() { return Err(refuse("volume-helper: volume registration already exists")); }
        if stat_at(vars.0.as_raw_fd(), &c)?.is_some() { return Err(refuse("volume-helper: volume directory already exists; refusing overwrite")); }
        let (project, _claim) = match self.custodian {
            // The custodian makes the directory, bounds it, and hands it over owned by the grain.
            Some(socket) => (custodian::create(socket, &name, self.size_mib, self.app_uid)?.get("project")? as u32, None),
            None => { let lock = self.claim_lock()?; (self.claim_project(&vars)?, Some(lock)) }
        };
        let made = std::cell::Cell::new(false);
        let limited = std::cell::Cell::new(false);
        let result = (|| -> io::Result<()> {
            let dir = if self.custodian.is_some() {
                made.set(true);
                open_dir_at(vars.0.as_raw_fd(), &c)?
            } else {
                if unsafe { libc::mkdirat(vars.0.as_raw_fd(), c.as_ptr(), 0o700) } != 0 { return Err(io::Error::last_os_error()); }
                made.set(true);
                let dir = open_dir_at(vars.0.as_raw_fd(), &c)?;
                if unsafe { libc::fchown(dir.as_raw_fd(), self.app_uid, self.app_uid) } != 0 { return Err(io::Error::last_os_error()); }
                if unsafe { libc::fchmod(dir.as_raw_fd(), 0o700) } != 0 { return Err(io::Error::last_os_error()); }
                quota::set_project(dir.as_raw_fd(), project)?;
                limited.set(true);
                let bytes = self.quota_bytes();
                quota::set_limits(dir.as_raw_fd(), project, bytes, bytes / quota::BYTES_PER_INODE)?;
                dir
            };
            if let Some(image) = import {
                self.import_tree(&vars, image)?;
                // The copy carries the image root's owner and mode onto the directory: restore them.
                if unsafe { libc::fchown(dir.as_raw_fd(), self.app_uid, self.app_uid) } != 0 { return Err(io::Error::last_os_error()); }
                if unsafe { libc::fchmod(dir.as_raw_fd(), 0o700) } != 0 { return Err(io::Error::last_os_error()); }
            }
            own_contents(dir.as_raw_fd(), self.app_uid)?;
            let reg = Registration { app_uid: self.app_uid, size_mib: self.size_mib, deployment_id: self.deployment_id.to_owned(),
                host_id: self.host_id.to_owned(), volume_id: self.volume_id.to_owned(), project_id: project };
            self.write_registration(&volumes, &reg)
        })();
        if let Some(image) = import { let _ = fs::remove_file(image); }
        if result.is_err() {
            // The registration is written last: with none, nothing of this call may remain.
            if let Some(socket) = self.custodian {
                let _ = custodian::destroy(socket, &name);
            } else if made.get() {
                if let Ok(dir) = open_dir_at(vars.0.as_raw_fd(), &c) {
                    let _ = remove_contents(dir.as_raw_fd());
                    if limited.get() { let _ = quota::clear_limits(dir.as_raw_fd(), project); }
                }
                unsafe { libc::unlinkat(vars.0.as_raw_fd(), c.as_ptr(), libc::AT_REMOVEDIR) };
            }
        }
        result
    }

    fn write_registration(&self, volumes: &Dir, reg: &Registration) -> io::Result<()> {
        let leaf = format!("{}.conf", self.name());
        let tmp = format!(".volume.{}.{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).map_err(|_| invalid("clock"))?.as_nanos());
        let (ct, cl) = (cstr(&tmp)?, cstr(&leaf)?);
        let fd = unsafe { libc::openat(volumes.0.as_raw_fd(), ct.as_ptr(), libc::O_WRONLY | libc::O_CREAT | libc::O_EXCL | libc::O_NOFOLLOW | libc::O_CLOEXEC, 0o600) };
        if fd < 0 { return Err(io::Error::last_os_error()); }
        let mut f = unsafe { File::from_raw_fd(fd) };
        let result = (|| -> io::Result<()> {
            unsafe { libc::fchmod(f.as_raw_fd(), 0o600) };
            f.write_all(reg.text().as_bytes())?;
            // No-replace: a registration that appeared meanwhile is never overwritten.
            if unsafe { libc::linkat(volumes.0.as_raw_fd(), ct.as_ptr(), volumes.0.as_raw_fd(), cl.as_ptr(), 0) } != 0 { return Err(io::Error::last_os_error()); }
            Ok(())
        })();
        unsafe { libc::unlinkat(volumes.0.as_raw_fd(), ct.as_ptr(), 0) };
        result?;
        Ok(())
    }

    /// Operator-supplied image bytes: never mounted. e2fsprogs parses them in userspace as the
    /// grain's uid with no privilege and copies the tree into the (quota-bounded) directory.
    fn import_tree(&self, vars: &Dir, image: &Path) -> io::Result<()> {
        let stage_name = format!(".import-{}", self.name());
        let cs = cstr(&stage_name)?;
        if stat_at(vars.0.as_raw_fd(), &cs)?.is_some() { return Err(refuse("volume-helper: import stage already exists")); }
        let m = fs::symlink_metadata(image).ctx("inspect", image)?;
        if !m.is_file() || m.uid() != 0 || m.nlink() != 1 || m.mode() & 0o7777 != 0o600
            || m.len() == 0 || m.len() > export_image_bytes(self.size_mib) {
            return Err(refuse("volume-helper: import image identity or size refused"));
        }
        if unsafe { libc::mkdirat(vars.0.as_raw_fd(), cs.as_ptr(), 0o700) } != 0 { return Err(io::Error::last_os_error()); }
        let stage = self.root.join("vars").join(&stage_name);
        let result = (|| -> io::Result<()> {
            let sd = open_dir_at(vars.0.as_raw_fd(), &cs)?;
            if unsafe { libc::fchown(sd.as_raw_fd(), self.app_uid, self.app_uid) } != 0 { return Err(io::Error::last_os_error()); }
            let copy = stage.join("untrusted.ext4");
            fs::copy(image, &copy).ctx("copy", image)?;
            let f = File::open(&copy).ctx("open", &copy)?;
            if unsafe { libc::fchown(f.as_raw_fd(), self.app_uid, self.app_uid) } != 0 { return Err(io::Error::last_os_error()); }
            if unsafe { libc::fchmod(f.as_raw_fd(), 0o400) } != 0 { return Err(io::Error::last_os_error()); }
            drop(f);
            let uid = self.app_uid.to_string();
            let reader = |program: &str, args: &[&str]| -> io::Result<std::process::Output> {
                Command::new("/usr/bin/setpriv")
                    .args([&format!("--reuid={uid}"), &format!("--regid={uid}"), "--clear-groups", "--no-new-privs", "--inh-caps=-all", "--bounding-set=-all", "--", program])
                    .args(args).current_dir(&stage).env_clear().env("PATH", "/usr/sbin:/usr/bin:/sbin:/bin").stdin(Stdio::null()).output()
            };
            let kind = reader("/usr/sbin/blkid", &["-p", "-s", "TYPE", "-o", "value", "--", "untrusted.ext4"])?;
            if !kind.status.success() || String::from_utf8_lossy(&kind.stdout).trim() != "ext4" { return Err(refuse("volume-helper: import image is not ext4")); }
            if !reader("/usr/sbin/e2fsck", &["-fn", "--", "untrusted.ext4"])?.status.success() { return Err(refuse("volume-helper: import image fails e2fsck")); }
            let dest = self.path();
            let dump = reader("/usr/sbin/debugfs", &["-R", &format!("rdump / {}", dest.display()), "untrusted.ext4"])?;
            let log = format!("{}{}", String::from_utf8_lossy(&dump.stdout), String::from_utf8_lossy(&dump.stderr));
            // debugfs reports a write that ran out of room as a message and still exits 0: a copy
            // that hit the quota is a truncated tree, never an import.
            let out_of_room = log.lines().any(|l| { let l = l.to_ascii_lowercase(); l.contains("quota exceeded") || l.contains("no space left") || l.contains("file too large") });
            if !dump.status.success() || out_of_room {
                return Err(refuse(format!("volume-helper: import tree copy failed: {}", log.trim())));
            }
            Ok(())
        })();
        if let Ok(sd) = open_dir_at(vars.0.as_raw_fd(), &cs) { let _ = remove_contents(sd.as_raw_fd()); }
        unsafe { libc::unlinkat(vars.0.as_raw_fd(), cs.as_ptr(), libc::AT_REMOVEDIR) };
        result
    }

    /// Remove the volume. Every step tolerates the work already done, so an interrupted destroy
    /// is finished by running it again; the registration goes last.
    pub(crate) fn destroy(&self) -> io::Result<()> {
        let reg = self.registered()?;
        let (_, volumes, vars, attest) = self.layout(false)?;
        let name = self.name();
        let c = cstr(&name)?;
        let ignore = |rc: libc::c_int| -> io::Result<()> {
            if rc != 0 { let e = io::Error::last_os_error(); if e.raw_os_error() != Some(libc::ENOENT) { return Err(e); } }
            Ok(())
        };
        ignore(unsafe { libc::unlinkat(attest.0.as_raw_fd(), cstr(&format!("{name}.witness"))?.as_ptr(), 0) })?;
        if let Some(socket) = self.custodian {
            custodian::destroy(socket, &name)?;
        } else { match open_dir_at(vars.0.as_raw_fd(), &c) {
            Ok(dir) => {
                let m = dir.metadata()?;
                if m.uid() != self.app_uid { return Err(refuse("volume-helper: destroy refuses a directory the grain does not own")); }
                if m.dev() != vars.0.metadata()?.dev() { return Err(refuse("volume-helper: destroy refuses a directory on another filesystem")); }
                remove_contents(dir.as_raw_fd())?;
                quota::clear_limits(dir.as_raw_fd(), reg.project_id)?;
                drop(dir);
                ignore(unsafe { libc::unlinkat(vars.0.as_raw_fd(), c.as_ptr(), libc::AT_REMOVEDIR) })?;
            }
            Err(e) if e.raw_os_error() == Some(libc::ENOENT) => {}
            Err(_) => return Err(refuse("volume-helper: volume directory is not a plain directory")),
        } }
        ignore(unsafe { libc::unlinkat(volumes.0.as_raw_fd(), cstr(&format!("{name}.conf"))?.as_ptr(), 0) })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::fs::symlink;

    struct Scratch(PathBuf);
    impl Scratch {
        fn new() -> Self {
            let p = std::env::temp_dir().join(format!("mini-volume-dir-{}-{}", std::process::id(), SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
            fs::create_dir(&p).unwrap();
            Self(p)
        }
    }
    impl Drop for Scratch { fn drop(&mut self) { let _ = fs::remove_dir_all(&self.0); } }

    fn registration() -> Registration {
        Registration { app_uid: 165536, size_mib: 64, deployment_id: "a".repeat(64), host_id: "b".repeat(64), volume_id: "c".repeat(64), project_id: 1_000_000_007 }
    }

    #[test]
    fn registration_round_trips_and_refuses_every_ambiguity() {
        let r = registration();
        assert_eq!(Registration::parse(&r.text()).unwrap(), r);
        for bad in [
            r.text().replace("project_id=1000000007\n", ""),                         // the loop-era five-line registration
            r.text().replace("project_id=1000000007", "project_id=7"),                // below the project range
            r.text().replace("size_mib=64", "size_mib=064"),                          // non-canonical number
            r.text() + "\n",                                                          // trailing blank line
            r.text().replace("app_uid=165536\nsize_mib=64", "size_mib=64\napp_uid=165536"), // field order
            r.text().replace(&"a".repeat(64), &"A".repeat(64)),                       // upper-case hex
        ] {
            assert!(Registration::parse(&bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn project_ids_are_deterministic_in_range_and_distinct_per_volume() {
        let a = deterministic_project("0123456789abcdef-9101", 0);
        assert_eq!(a, deterministic_project("0123456789abcdef-9101", 0));
        assert_ne!(a, deterministic_project("0123456789abcdef-9102", 0));
        assert_ne!(a, deterministic_project("0123456789abcdef-9101", 1));
        for probe in 0..PROJECT_PROBES { let id = deterministic_project("fedcba9876543210-1", probe); assert!((PROJECT_BASE..PROJECT_BASE + (1 << 28)).contains(&id)); }
    }

    #[test]
    fn export_images_hold_a_full_volume_and_its_metadata() {
        assert_eq!(export_image_bytes(64), 64 * 1048576 + 8 * 1048576 + 8 * 1048576);
        assert!(export_image_bytes(16384) > 16384 * 1048576);
    }

    #[test]
    fn removal_never_follows_a_link_out_of_the_tree() {
        let s = Scratch::new();
        let victim = s.0.join("victim");
        fs::create_dir(&victim).unwrap();
        fs::write(victim.join("sentinel"), b"keep").unwrap();
        let tree = s.0.join("tree");
        fs::create_dir_all(tree.join("a/b/c")).unwrap();
        fs::write(tree.join("a/b/file"), b"x").unwrap();
        symlink(&victim, tree.join("a/link-to-victim")).unwrap();
        symlink("../../victim", tree.join("a/b/relative-link")).unwrap();
        symlink(&victim.join("sentinel"), tree.join("link-to-file")).unwrap();
        fs::hard_link(victim.join("sentinel"), tree.join("hard")).unwrap();
        let dir = File::open(&tree).unwrap();
        remove_contents(dir.as_raw_fd()).unwrap();
        assert!(fs::read_dir(&tree).unwrap().next().is_none());
        assert_eq!(fs::read(victim.join("sentinel")).unwrap(), b"keep");
    }

    #[test]
    fn a_walk_that_meets_a_swapped_directory_stops() {
        // The tree entry is a symlink to a directory by the time it is opened: the open refuses.
        let s = Scratch::new();
        fs::create_dir(s.0.join("real")).unwrap();
        symlink(s.0.join("real"), s.0.join("link")).unwrap();
        let dir = File::open(&s.0).unwrap();
        assert!(open_dir_at(dir.as_raw_fd(), &cstr("link").unwrap()).is_err());
        assert!(open_dir_at(dir.as_raw_fd(), &cstr("real").unwrap()).is_ok());
        assert!(cstr("../x").is_err() && cstr("a/b").is_err() && cstr("").is_err());
    }

    #[test]
    fn the_fingerprint_moves_with_any_change_to_the_tree() {
        let s = Scratch::new();
        fs::create_dir_all(s.0.join("d")).unwrap();
        fs::write(s.0.join("d/f"), b"one").unwrap();
        let dir = File::open(&s.0).unwrap();
        let base = fingerprint(dir.as_raw_fd()).unwrap();
        assert_eq!(base, fingerprint(dir.as_raw_fd()).unwrap());
        fs::write(s.0.join("d/f"), b"three").unwrap();
        let changed = fingerprint(dir.as_raw_fd()).unwrap();
        assert_ne!(base, changed);
        fs::write(s.0.join("d/g"), b"").unwrap();
        assert_ne!(changed, fingerprint(dir.as_raw_fd()).unwrap());
    }

    // ---- physical: a real project-quota filesystem, root only (testing/journeys/volume-quota-physical.sh)

    const STORE: &str = "2222222222222222";
    const OPERATOR: u32 = 64999;
    fn physical_root() -> PathBuf {
        assert_eq!(unsafe { libc::geteuid() }, 0, "explicit root disposable receiver only");
        let root = PathBuf::from(std::env::var_os("MINI_VOLUME_QUOTA_ROOT").expect("explicit owned grains root"));
        assert!(root.to_string_lossy().starts_with("/var/lib/mini-spk-volume-test-"));
        root
    }
    fn volume<'a>(root: &'a Path, grain: &'static str, uid: u32, mib: u64) -> Volume<'a> {
        Volume { root, store: STORE, grain, app_uid: uid, size_mib: mib, volume_id: &"d".repeat(64).leak()[..], deployment_id: &"a".repeat(64).leak()[..], host_id: &"b".repeat(64).leak()[..], custodian: None }
    }
    fn as_app(uid: u32, script: &str) -> std::process::Output {
        Command::new("/usr/bin/setpriv").args([&format!("--reuid={uid}"), &format!("--regid={uid}"), "--clear-groups", "--", "/bin/sh", "-c", script])
            .env_clear().env("PATH", "/usr/bin:/bin").output().unwrap()
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs"]
    fn physical_create_attest_and_resident_checks_agree() {
        let root = physical_root();
        let v = volume(&root, "9101", 165536, 64);
        v.create(None).unwrap();
        v.attest().unwrap();
        let o = v.verify().unwrap();
        assert!(matches!(o.fs_type, "ext4" | "xfs"));
        // The directory is the grain's, private, and bounded exactly by the class.
        let dir = File::open(v.path()).unwrap();
        let m = dir.metadata().unwrap();
        assert_eq!((m.uid(), m.mode() & 0o7777), (165536, 0o700));
        assert_eq!(quota::reported_bytes(dir.as_raw_fd()).unwrap(), 64 * 1048576);
        // What the resident reads: the witness, and the open descriptor against it.
        let site = crate::volume_custody::VolumeSite::new(&root, STORE).unwrap();
        let w = crate::volume_custody::read_attested_volume(&site, 9101, 165536, 64 * 1048576, &"a".repeat(64), &"b".repeat(64), &"d".repeat(64)).unwrap();
        w.compare_open_mount(dir.as_raw_fd()).unwrap();
        w.compare_open_project(dir.as_raw_fd()).unwrap();
        assert_eq!(w.project_id, o.project_id);
        // The resident's view: the volume against its parent (`vars`) on the same filesystem.
        let parent = File::open(root.join("vars")).unwrap();
        let (separate, total) = crate::os::var_filesystem(&v.path(), parent.as_raw_fd(), dir.as_raw_fd()).unwrap();
        assert!(separate && total == 64 * 1048576);
        // A directory that is not under a project limit reports its parent's size: not bounded.
        let (bounded, _) = crate::os::var_filesystem(&root.join("vars"), parent.as_raw_fd(), parent.as_raw_fd()).unwrap();
        assert!(!bounded);
        // A repeated create is refused; the registration is exact.
        assert!(v.create(None).is_err());
        let mut other = volume(&root, "9101", 165536, 128);
        assert!(other.registered().is_err());
        other.size_mib = 64;
        other.registered().unwrap();
        v.destroy().unwrap();
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs"]
    fn physical_the_kernel_bounds_bytes_and_inodes_and_grains_cannot_link() {
        let root = physical_root();
        let a = volume(&root, "9201", 165537, 64);
        let b = volume(&root, "9202", 165538, 64);
        a.create(None).unwrap();
        b.create(None).unwrap();
        let (pa, pb) = (a.verify().unwrap().project_id, b.verify().unwrap().project_id);
        assert_ne!(pa, pb);
        // G1 bytes: a grain's own writes stop at the quota.
        let dd = as_app(165537, &format!("dd if=/dev/zero of={}/big bs=1M count=80 2>&1", a.path().display()));
        assert!(String::from_utf8_lossy(&dd.stdout).contains("quota"), "{}", String::from_utf8_lossy(&dd.stdout));
        let used = fingerprint(File::open(a.path()).unwrap().as_raw_fd()).unwrap().1;
        assert!(used <= 64 * 1048576, "{used}");
        // G1 inodes.
        let many = as_app(165538, &format!("cd {} && i=0; while [ $i -lt 6000 ]; do ( : > f$i ) 2>/dev/null || exit 3; i=$((i+1)); done", b.path().display()));
        assert_eq!(many.status.code(), Some(3));
        let entries = fingerprint(File::open(b.path()).unwrap().as_raw_fd()).unwrap().0;
        assert!(entries <= 64 * 1048576 / quota::BYTES_PER_INODE, "{entries}");
        // G2: the neighbour is untouched by either, and no link or rename crosses the projects.
        fs::write(a.path().join("secret"), b"a").unwrap();
        assert_eq!(fs::hard_link(a.path().join("secret"), b.path().join("alias")).unwrap_err().raw_os_error(), Some(libc::EXDEV));
        assert_eq!(fs::rename(a.path().join("secret"), b.path().join("moved")).unwrap_err().raw_os_error(), Some(libc::EXDEV));
        assert!(!as_app(165538, &format!("cat {}/secret", a.path().display())).status.success());
        a.verify().unwrap();
        b.verify().unwrap();
        a.destroy().unwrap();
        b.destroy().unwrap();
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs"]
    fn physical_planted_links_and_a_swapped_directory_never_escape() {
        let root = physical_root();
        let victim = root.join("victim");
        fs::create_dir(&victim).unwrap();
        fs::write(victim.join("sentinel"), b"keep").unwrap();
        let v = volume(&root, "9301", 165539, 64);
        v.create(None).unwrap();
        let plant = as_app(165539, &format!("cd {} && ln -s {} dirlink && ln -s /etc/shadow filelink && ln -s ../../../../victim up && mkdir -p d/e && ln -s {} d/e/deep && mkfifo fifo", v.path().display(), victim.display(), victim.display()));
        assert!(plant.status.success(), "{}", String::from_utf8_lossy(&plant.stderr));
        // G3: the directory itself swapped for a link is refused by every verb.
        let moved = root.join("vars").join("moved-aside");
        fs::rename(v.path(), &moved).unwrap();
        symlink(&victim, v.path()).unwrap();
        assert!(v.verify().is_err() && v.attest().is_err());
        fs::remove_file(v.path()).unwrap();
        fs::rename(&moved, v.path()).unwrap();
        v.verify().unwrap();
        // Ownership repair uses lchown and teardown unlinks: the victim is untouched by both.
        own_contents(File::open(v.path()).unwrap().as_raw_fd(), 165539).unwrap();
        let before = fs::metadata(victim.join("sentinel")).unwrap();
        v.destroy().unwrap();
        let after = fs::metadata(victim.join("sentinel")).unwrap();
        assert_eq!((before.uid(), before.gid(), before.ino()), (after.uid(), after.gid(), after.ino()));
        assert_eq!(fs::read(victim.join("sentinel")).unwrap(), b"keep");
        // G5: nothing of the volume remains, and its project id is free again.
        assert!(!v.path().exists());
        assert!(!root.join("volumes").join(format!("{STORE}-9301.conf")).exists());
        assert!(!root.join("attest").join(format!("{STORE}-9301.witness")).exists());
        let vars = File::open(root.join("vars")).unwrap();
        assert!(!quota::in_use(&quota::get_quota(vars.as_raw_fd(), deterministic_project(&format!("{STORE}-9301"), 0)).unwrap()));
        fs::remove_dir_all(&victim).unwrap();
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs"]
    fn physical_an_interrupted_destroy_and_a_failed_create_leave_nothing_behind() {
        let root = physical_root();
        let v = volume(&root, "9401", 165540, 64);
        v.create(None).unwrap();
        fs::write(v.path().join("f"), b"x").unwrap();
        // Destroy died after removing the directory: the registration remains, and a rerun finishes.
        remove_contents(File::open(v.path()).unwrap().as_raw_fd()).unwrap();
        fs::remove_dir(v.path()).unwrap();
        assert!(v.verify().is_err());
        v.destroy().unwrap();
        assert!(!root.join("volumes").join(format!("{STORE}-9401.conf")).exists());
        // A create that fails (an import that does not exist) removes its directory and claims nothing.
        let bad = volume(&root, "9402", 165541, 64);
        assert!(bad.create(Some(&root.join("volumes").join(".import-absent"))).is_err());
        assert!(!bad.path().exists() && bad.registered().is_err());
        assert!(!root.join("vars").join(format!(".import-{STORE}-9402")).exists());
    }

    fn mke2fs_tree(tree: &Path, image: &Path, mib: u64) {
        let f = File::create(image).unwrap();
        f.set_len(mib * 1048576).unwrap();
        let out = Command::new("/usr/sbin/mke2fs").args(["-q", "-t", "ext4", "-F", "-d"]).arg(tree).arg(image).output().unwrap();
        assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs"]
    fn physical_import_and_export_round_trip_a_tree_without_following_anything() {
        let root = physical_root();
        volume(&root, "9500", 165541, 64).layout(true).unwrap();
        let src = root.join("import-src");
        fs::create_dir_all(src.join("sub")).unwrap();
        fs::write(src.join("sub/data"), b"kept").unwrap();
        fs::write(src.join("suid"), b"setuid").unwrap();
        fs::set_permissions(src.join("suid"), fs::Permissions::from_mode(0o4755)).unwrap();
        symlink("/etc/shadow", src.join("escape")).unwrap();
        let image = root.join("volumes").join(".import-staged");
        mke2fs_tree(&src, &image, 64);
        fs::set_permissions(&image, fs::Permissions::from_mode(0o600)).unwrap();
        let v = volume(&root, "9501", 165542, 64);
        v.create(Some(&image)).unwrap();
        v.verify().unwrap();
        assert!(!image.exists(), "the staged import is consumed");
        assert_eq!(fs::read(v.path().join("sub/data")).unwrap(), b"kept");
        assert_eq!(fs::read_link(v.path().join("escape")).unwrap(), Path::new("/etc/shadow"));
        assert_eq!(fs::metadata(v.path().join("suid")).unwrap().mode() & 0o7777, 0o755, "the setuid bit does not cross");
        assert_eq!(fs::metadata(v.path().join("sub/data")).unwrap().uid(), 165542);
        // Export the volume: a clean ext4 image holding the same tree, the link kept as a link.
        let exports = root.join(STORE);
        fs::create_dir_all(&exports).unwrap();
        fs::set_permissions(&exports, fs::Permissions::from_mode(0o700)).unwrap();
        std::os::unix::fs::chown(&exports, Some(OPERATOR), Some(OPERATOR)).unwrap();
        let reply = super::volume_custody::export(&root, STORE, "9501", OPERATOR, OPERATOR).unwrap();
        assert_eq!(reply["e2fsck"], "clean");
        let listing = reply["rootListing"].to_string();
        assert!(listing.contains("escape") && listing.contains("sub") && listing.contains("suid"), "{listing}");
        let exported = PathBuf::from(reply["image"].as_str().unwrap());
        assert!(!root.join("vars").join(format!(".export-{STORE}-9501")).exists(), "the capture stage is removed");
        // The export imports into a second grain's volume: the round trip.
        let staged = root.join("volumes").join(".import-staged2");
        fs::copy(&exported, &staged).unwrap();
        fs::set_permissions(&staged, fs::Permissions::from_mode(0o600)).unwrap();
        let w = volume(&root, "9502", 165543, 64);
        w.create(Some(&staged)).unwrap();
        assert_eq!(fs::read(w.path().join("sub/data")).unwrap(), b"kept");
        assert_eq!(fs::read_link(w.path().join("escape")).unwrap(), Path::new("/etc/shadow"));
        // An import that does not fit the quota fails with the quota and leaves nothing.
        let big = root.join("import-big");
        fs::create_dir_all(&big).unwrap();
        let mut blob = File::create(big.join("blob")).unwrap();
        let chunk = vec![7u8; 1048576];
        for _ in 0..66 { blob.write_all(&chunk).unwrap(); }
        let big_image = root.join("volumes").join(".import-big");
        mke2fs_tree(&big, &big_image, 80);
        fs::set_permissions(&big_image, fs::Permissions::from_mode(0o600)).unwrap();
        let small = volume(&root, "9503", 165544, 64);
        let error = small.create(Some(&big_image)).unwrap_err().to_string();
        assert!(error.contains("import tree copy failed"), "{error}");
        assert!(!small.path().exists() && small.registered().is_err() && !big_image.exists());
        v.destroy().unwrap();
        w.destroy().unwrap();
        fs::remove_dir_all(&src).unwrap();
        fs::remove_dir_all(&big).unwrap();
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs"]
    fn physical_the_custodian_makes_bounds_reports_and_removes_and_the_helper_follows_it() {
        let root = physical_root();
        let socket = root.parent().unwrap().join("custodian.sock");
        // Uid base 0: no shift on this rig; the range covers the test uids.
        let custodian = super::super::volume_custodian::Custodian::open(&root, 0, 1_000_000).unwrap();
        { let socket = socket.clone(); std::thread::spawn(move || { let _ = custodian.serve(&socket, 0); }); }
        for _ in 0..100 { if socket.exists() { break; } std::thread::sleep(Duration::from_millis(50)); }
        let ask = |line: &str| -> String {
            let mut c = UnixStream::connect(&socket).unwrap();
            c.write_all(format!("{line}\n").as_bytes()).unwrap();
            let mut r = String::new();
            BufReader::new(c).read_line(&mut r).unwrap();
            r
        };
        let id = format!("{STORE}-9201");
        // Refusals are named; none of them touched anything.
        assert!(ask(&format!("MINI-VOLUME/1 usage {id}")).starts_with("REFUSED absent"));
        assert!(ask(&format!("MINI-VOLUME/1 destroy {id}")).starts_with("OK removed=0"));
        assert!(ask(&format!("MINI-VOLUME/1 create {id} 63 165536")).starts_with("REFUSED bad-size"));
        assert!(ask(&format!("MINI-VOLUME/1 create {id} 64 0")).starts_with("REFUSED bad-request"));
        assert!(ask(&format!("MINI-VOLUME/1 create {id} 64 2000000")).starts_with("REFUSED bad-uid"));
        assert!(ask("MINI-VOLUME/1 create ../../etc-9 64 165536").starts_with("REFUSED bad-id"));
        assert!(!root.join("vars").join(&id).exists());
        // Created: bounded before it is handed out, owned by the grain, private.
        let r = ask(&format!("MINI-VOLUME/1 create {id} 64 165536"));
        assert!(r.starts_with("OK project="), "{r}");
        assert!(ask(&format!("MINI-VOLUME/1 create {id} 64 165536")).starts_with("REFUSED exists"));
        let path = root.join("vars").join(&id);
        let m = fs::metadata(&path).unwrap();
        assert_eq!((m.uid(), m.mode() & 0o7777), (165536, 0o700));
        let u = ask(&format!("MINI-VOLUME/1 usage {id}"));
        assert!(u.contains(&format!("bhard_kib={}", 64 * 1024)) && u.contains("uid=165536"), "{u}");
        let full = as_app(165536, &format!("dd if=/dev/zero of={}/f bs=1M count=80 2>&1; true", path.display()));
        assert!(String::from_utf8_lossy(&full.stdout).to_lowercase().contains("quota"), "{full:?}");
        // A directory that is not a custodian volume is never touched by destroy or usage.
        fs::create_dir(root.join("vars").join(format!("{STORE}-9202"))).unwrap();
        assert!(ask(&format!("MINI-VOLUME/1 destroy {STORE}-9202")).starts_with("REFUSED not-a-volume"));
        assert!(root.join("vars").join(format!("{STORE}-9202")).exists());
        fs::remove_dir(root.join("vars").join(format!("{STORE}-9202"))).unwrap();
        // The helper, pointed at the custodian, does what it does locally.
        let mut v = volume(&root, "9203", 165537, 64);
        v.custodian = Some(&socket);
        v.create(None).unwrap();
        v.attest().unwrap();
        v.verify().unwrap();
        v.destroy().unwrap();
        assert!(!v.path().exists());
        // Destroy is idempotent and leaves nothing: the name, and the project's limit.
        assert!(ask(&format!("MINI-VOLUME/1 destroy {id}")).starts_with("OK removed=1"));
        assert!(ask(&format!("MINI-VOLUME/1 destroy {id}")).starts_with("OK removed=0"));
        assert!(!path.exists());
    }

    #[test]
    #[ignore = "physical: root on a prjquota ext4 or xfs with cgroup2"]
    fn physical_export_freezes_a_running_grain_thaws_it_and_refuses_a_stray_process() {
        use std::os::unix::process::CommandExt;
        let root = physical_root();
        volume(&root, "9600", 165541, 64).layout(true).unwrap();
        let v = volume(&root, "9601", 165545, 64);
        v.create(None).unwrap();
        fs::write(v.path().join("f"), b"data").unwrap();
        let exports = root.join(STORE);
        fs::create_dir_all(&exports).unwrap();
        fs::set_permissions(&exports, fs::Permissions::from_mode(0o700)).unwrap();
        std::os::unix::fs::chown(&exports, Some(OPERATOR), Some(OPERATOR)).unwrap();
        let base = PathBuf::from(format!("/sys/fs/cgroup/user.slice/user-{OPERATOR}.slice/user@{OPERATOR}.service"));
        let unit = base.join(format!("s{STORE}-mini-grains-S.slice/mini-spk-s{STORE}-a9601-g1.service"));
        fs::create_dir_all(&unit).unwrap();
        let mut inside = Command::new("/usr/bin/sleep").arg("1000").uid(165545).gid(165545).spawn().unwrap();
        fs::write(unit.join("cgroup.procs"), inside.id().to_string()).unwrap();
        let events = |p: &Path| fs::read_to_string(p.join("cgroup.events")).unwrap();
        let reply = super::volume_custody::export(&root, STORE, "9601", OPERATOR, OPERATOR).unwrap();
        assert_eq!(reply["e2fsck"], "clean");
        assert!(events(&unit).contains("frozen 0"), "the grain is thawed after the capture");
        assert!(!root.join("volume-custody/freezes").join(format!("{STORE}-9601.json")).exists());
        assert!(inside.try_wait().unwrap().is_none(), "the grain's process survived the freeze");
        // A process of the grain's uid outside every frozen cgroup: the capture would not be consistent.
        let mut stray = Command::new("/usr/bin/sleep").arg("1000").uid(165545).gid(165545).spawn().unwrap();
        let error = super::volume_custody::export(&root, STORE, "9601", OPERATOR, OPERATOR).unwrap_err().to_string();
        assert!(error.contains("outside the frozen cgroups"), "{error}");
        assert!(events(&unit).contains("frozen 0"), "a refused capture thaws what it froze");
        assert!(!root.join("volume-custody/freezes").join(format!("{STORE}-9601.json")).exists());
        let _ = stray.kill(); let _ = stray.wait();
        let _ = inside.kill(); let _ = inside.wait();
        for dir in [unit.clone(), unit.parent().unwrap().to_owned(), base.clone(), base.parent().unwrap().to_owned()] {
            for _ in 0..50 { if fs::remove_dir(&dir).is_ok() { break } std::thread::sleep(Duration::from_millis(20)); }
        }
        v.destroy().unwrap();
    }
}
