//! Join a mapped user namespace before parsing resident bytes. bubblewrap
//! creates it (the one sandboxing binary a host provides; on a host that confines
//! unprivileged namespace creation, its AppArmor-profiled copy is the permitted
//! creator); this process writes the broker-selected operator/app identities and an
//! optional root-registered controller identity into it from
//! outside and then joins it, staying the unit MainPID. Both resident and worker
//! later drop all capability sets.
use std::fs::{self, File, Metadata, OpenOptions};
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;
use std::collections::BTreeMap;
// Bootstrap deliberately inspects only the fixed world SPK namespace. No archive
// or resident JSON is parsed before isolation. Finalized packages contribute their
// retained metadata, not every executable-image file; public revisions contribute
// their complete bounded metadata tree. Kernel FD limits can impose a lower bound.
const MAX_CUSTODY_HANDLES: usize = 131_072;
const MAX_CUSTODY_PATH_BYTES: usize = 32 * 1024 * 1024;
const MAX_CUSTODY_DEPTH: usize = 32;
struct Pin { file: File, original: Metadata }
struct Provenance {
    paths: BTreeMap<PathBuf, std::sync::Arc<Pin>>,
    inodes: BTreeMap<(u64,u64), std::sync::Arc<Pin>>,
    path_bytes: usize,
}
impl Provenance {
    fn new() -> Self { Self { paths:BTreeMap::new(), inodes:BTreeMap::new(), path_bytes:0 } }
}
static ROOTS: OnceLock<Provenance> = OnceLock::new();
fn refused(s: &str)->io::Error { io::Error::new(io::ErrorKind::PermissionDenied,s) }
fn stable(meta: &Metadata) -> (u64,u64,u32,u64,u64,i64,i64,i64,i64) {
    (meta.dev(),meta.ino(),meta.mode(),meta.nlink(),meta.len(),meta.mtime(),meta.mtime_nsec(),meta.ctime(),meta.ctime_nsec())
}
fn unchanged(pin: &Pin, observed: &Metadata) -> bool {
    let Ok(current) = pin.file.metadata() else { return false; };
    stable(&current) == stable(&pin.original) && stable(observed) == stable(&pin.original)
        && (current.uid(),current.gid()) == (observed.uid(),observed.gid())
}
/// Exact pre-namespace owner/group, only for the same unchanged held inode.
/// Once bootstrap has captured custody, an unknown inode is never blessed by
/// its namespace-visible UID (including the ambiguous overflow UID/GID).
pub(crate) fn original_owner(observed: &Metadata) -> Option<(u32,u32)> {
    match ROOTS.get() {
        Some(roots) => roots.inodes.get(&(observed.dev(),observed.ino()))
            .filter(|pin| unchanged(pin,observed)).map(|pin|(pin.original.uid(),pin.original.gid())),
        None if observed.uid()==0 || observed.uid()==unsafe{libc::geteuid()} => Some((observed.uid(),observed.gid())),
        None => None,
    }
}
/// Root in the initial namespace is unmapped inside the resident namespace.
/// Retained handles carry its verified provenance, never the overflow UID.
pub(crate) fn root_owned(path: &Path, observed: &Metadata) -> bool {
    if ROOTS.get().is_none() && crate::os::root_owner(observed.uid()) { return true; }
    ROOTS.get().and_then(|roots|roots.paths.get(path)).is_some_and(|pin| {
        pin.original.uid()==0 && unchanged(pin,observed)
    })
}
fn host_trusted(meta: &Metadata) -> bool {
    !meta.file_type().is_symlink() && meta.mode()&0o022==0
        && (meta.uid()==0 || meta.uid()==unsafe{libc::geteuid()})
}
fn protected_handle(path: &Path) -> io::Result<File> {
    use std::ffi::CString;
    use std::os::unix::ffi::OsStrExt;
    use std::path::Component;
    if !path.is_absolute() { return Err(refused("bootstrap custody path must be absolute")); }
    let mut current=OpenOptions::new().read(true).custom_flags(libc::O_PATH|libc::O_DIRECTORY|libc::O_CLOEXEC).open("/")?;
    let components:Vec<_>=path.components().skip(1).collect();
    for (index,component) in components.iter().enumerate() {
        if !host_trusted(&current.metadata()?) { return Err(refused("bootstrap custody ancestor belongs to another principal or is writable")); }
        let Component::Normal(name)=component else { return Err(refused("bootstrap custody path not normalized")); };
        let name=CString::new(name.as_bytes()).map_err(|_|refused("bootstrap custody path contains NUL"))?;
        let flags=libc::O_PATH|libc::O_NOFOLLOW|libc::O_CLOEXEC|if index+1<components.len(){libc::O_DIRECTORY}else{0};
        let fd=unsafe{libc::openat(current.as_raw_fd(),name.as_ptr(),flags)};
        if fd<0 { return Err(io::Error::last_os_error()); }
        current=unsafe{File::from_raw_fd(fd)};
    }
    let meta=current.metadata()?;
    if !host_trusted(&meta) || (!meta.is_dir() && !meta.is_file()) {
        return Err(refused("bootstrap custody entry belongs to another principal, is writable, or is not regular"));
    }
    Ok(current)
}
fn remember(path: &Path, roots: &mut Provenance) -> io::Result<()> {
    if roots.paths.contains_key(path) { return Ok(()); }
    let count=roots.paths.len();
    let bytes=path.as_os_str().len();
    if count>=MAX_CUSTODY_HANDLES || bytes>MAX_CUSTODY_PATH_BYTES.saturating_sub(roots.path_bytes) {
        return Err(refused("bootstrap custody handle/path bound exceeded"));
    }
    let file=protected_handle(path)?;
    let original=file.metadata()?;
    let pin=std::sync::Arc::new(Pin {file,original});
    if let Some(previous)=roots.inodes.get(&(pin.original.dev(),pin.original.ino())) {
        if !unchanged(previous,&pin.original) { return Err(refused("bootstrap custody inode changed")); }
    }
    roots.inodes.insert((pin.original.dev(),pin.original.ino()),pin.clone());
    roots.paths.insert(path.to_owned(),pin);
    roots.path_bytes+=bytes;
    Ok(())
}
fn finalized_name(name: &str) -> bool {
    name.strip_prefix("sha256-").is_some_and(|hash| hash.len()==64 && hash.bytes().all(|b|b.is_ascii_digit()||(b'a'..=b'f').contains(&b)))
}
fn public_tree(path: &Path, roots: &mut Provenance, depth: usize) -> io::Result<()> {
    if depth>MAX_CUSTODY_DEPTH { return Err(refused("bootstrap public-data tree depth exceeded")); }
    remember(path,roots)?;
    if roots.paths[path].original.is_dir() {
        for entry in fs::read_dir(path)? {
            public_tree(&entry?.path(),roots,depth+1)?;
        }
    }
    Ok(())
}
fn remember_spk_namespace(world: &Path, roots: &mut Provenance) -> io::Result<()> {
    let namespace=world.join("spk");
    match fs::symlink_metadata(&namespace) {
        Err(error) if error.kind()==io::ErrorKind::NotFound => return Ok(()),
        result => { result?; }
    }
    for ancestor in namespace.ancestors() { remember(ancestor,roots)?; }
    for kind in ["packages","public-data"] {
        let store=namespace.join(kind);
        match fs::symlink_metadata(&store) {
            Err(error) if error.kind()==io::ErrorKind::NotFound => continue,
            result => { result?; }
        }
        remember(&store,roots)?;
        let mut seen=0;
        for entry in fs::read_dir(&store)? {
            seen+=1;
            if seen>MAX_CUSTODY_HANDLES { return Err(refused("bootstrap publication listing bound exceeded")); }
            let entry=entry?;
            if !entry.file_name().to_str().is_some_and(finalized_name) { continue; }
            let publication=entry.path();
            if kind=="public-data" { public_tree(&publication,roots,0)?; }
            else {
                remember(&publication,roots)?;
                for name in ["package.spk","manifest.json","import-policy.json","root"] {
                    let path=publication.join(name);
                    match fs::symlink_metadata(&path) {
                        Err(error) if error.kind()==io::ErrorKind::NotFound => continue,
                        result => { result?; }
                    }
                    remember(&path,roots)?;
                }
            }
        }
    }
    Ok(())
}
pub(crate) fn prepare_root_handles(config: &Path, root: &Path, store: &str, grain: &str) -> io::Result<()> {
    let mut roots=Provenance::new();
    for path in config.ancestors().skip(1) { remember(path,&mut roots)?; }
    let witness=root.join("attest").join(format!("{store}-{grain}.witness"));
    for path in witness.ancestors() { remember(path,&mut roots)?; }
    remember_spk_namespace(root,&mut roots)?;
    let controller=root.join("controller");
    match fs::symlink_metadata(&controller) {
        Err(e) if e.kind()==io::ErrorKind::NotFound => {},
        result => { result?; remember(&controller,&mut roots)?; }
    }
    ROOTS.set(roots).map_err(|_|refused("namespace root provenance initialized twice"))
}

/// Only the root-installed world's receipt can add a controller identity.
/// Its UID is already delegated to the operator; this is not isolation from
/// that trusted operator. Neither dropped resident nor app retains switch caps.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ControllerIdentity { uid: u32, gid: u32 }
#[derive(serde::Deserialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
struct ControllerReceipt {
    protocol: String, store: String, deployment_id: String, host_id: String,
    operator_uid: u32, operator_gid: u32, controller_uid: u32, controller_gid: u32,
    account: String,
}
static CONTROLLER: OnceLock<Option<ControllerIdentity>> = OnceLock::new();
fn receipt_identity(r: &ControllerReceipt, registry: &crate::volume_helper::Registry) -> io::Result<ControllerIdentity> {
    let valid = |id: u32| id>=65536 && id<u32::MAX;
    if r.protocol!="mini-spk-controller-namespace-v1" || r.store!=registry.store
        || r.deployment_id!=registry.deployment_id || r.host_id!=registry.host_id
        || r.operator_uid!=registry.operator_uid || r.operator_gid!=registry.operator_gid
        || r.account!=format!("mini-c-{}",registry.store)
        || !valid(r.controller_uid) || !valid(r.controller_gid)
        || r.controller_uid==registry.operator_uid || r.controller_gid==registry.operator_gid
        || registry.app_uids.contains(&r.controller_uid) || registry.app_uids.contains(&r.controller_gid)
    { return Err(refused("registered controller namespace identity differs from world")); }
    Ok(ControllerIdentity {uid:r.controller_uid,gid:r.controller_gid})
}
fn account_matches(name: &str, home: &Path, identity: ControllerIdentity) -> io::Result<()> {
    use std::ffi::{CString,CStr};
    let name=CString::new(name).map_err(|_|refused("controller account name"))?;
    let mut bytes=vec![0 as libc::c_char;16384];
    let mut entry:libc::passwd=unsafe{std::mem::zeroed()};
    let mut result=std::ptr::null_mut();
    let code=unsafe{libc::getpwnam_r(name.as_ptr(),&mut entry,bytes.as_mut_ptr(),bytes.len(),&mut result)};
    if code!=0 || result.is_null() || entry.pw_dir.is_null() || entry.pw_shell.is_null()
        || entry.pw_uid!=identity.uid || entry.pw_gid!=identity.gid
        || unsafe{CStr::from_ptr(entry.pw_dir)}.to_bytes()!=home.as_os_str().as_encoded_bytes()
        || unsafe{CStr::from_ptr(entry.pw_shell)}.to_bytes()!=b"/usr/sbin/nologin"
    { return Err(refused("registered controller passwd identity differs")); }
    let mut group:libc::group=unsafe{std::mem::zeroed()};
    let mut result=std::ptr::null_mut();
    let code=unsafe{libc::getgrnam_r(name.as_ptr(),&mut group,bytes.as_mut_ptr(),bytes.len(),&mut result)};
    if code!=0 || result.is_null() || group.gr_gid!=identity.gid
        || (!group.gr_mem.is_null() && !unsafe{*group.gr_mem}.is_null())
    { return Err(refused("registered controller private group differs")); }
    Ok(())
}
pub(crate) fn load_registered_controller(registry: &crate::volume_helper::Registry) -> io::Result<Option<ControllerIdentity>> {
    let directory=registry.grains_root.join("controller");
    match fs::symlink_metadata(&directory) {
        Err(e) if e.kind()==io::ErrorKind::NotFound => return Ok(None),
        result => { result?; }
    }
    // An existing partial allocation without its completed receipt refuses.
    let path=directory.join("namespace.json");
    minidregg_compatible_upgrade_custody::root_ancestors(&path)?;
    let mut file=OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW|libc::O_CLOEXEC|libc::O_NONBLOCK).open(&path)?;
    let before=file.metadata()?;
    if !before.is_file() || before.uid()!=0 || before.nlink()!=1 || before.mode()&0o7777!=0o644
        || before.len()==0 || before.len()>4096 {
        return Err(refused("registered controller namespace receipt custody refused"));
    }
    let mut bytes=Vec::new();
    Read::by_ref(&mut file).take(4097).read_to_end(&mut bytes)?;
    let after=file.metadata()?;
    let named=fs::symlink_metadata(&path)?;
    if bytes.len() as u64!=before.len() || stable(&before)!=stable(&after)
        || stable(&before)!=stable(&named) || (before.dev(),before.ino(),before.uid(),before.gid())!=(named.dev(),named.ino(),named.uid(),named.gid()) {
        return Err(refused("registered controller receipt changed while read"));
    }
    let receipt:ControllerReceipt=serde_json::from_slice(&bytes)?;
    let identity=receipt_identity(&receipt,registry)?;
    account_matches(&receipt.account,&directory.join("home"),identity)?;
    Ok(Some(identity))
}
pub(crate) fn require_registered_controller(uid:u32) -> io::Result<()> {
    if CONTROLLER.get().and_then(|v|*v).is_some_and(|c|c.uid==uid) { Ok(()) }
    else { Err(refused("agent controller UID is not the root-registered mapped identity")) }
}

/// The physical bubblewrap binaries a host may provide (deploy/grain-host/resolve-bwrap):
/// the AppArmor-profiled copy a host restricting unprivileged user namespaces ships, and
/// the distro binary. The namespace and the app sandbox are made by the same binary.
pub(crate) const PHYSICAL_BWRAPS: [&str; 2] = ["/usr/local/libexec/mini-grain-bwrap", "/usr/bin/bwrap"];
/// A deployed physical bwrap: one of PHYSICAL_BWRAPS, a root-owned non-writable
/// executable regular file whose bytes have the pinned SHA-256.
pub(crate) fn pinned_bwrap(path: &Path, sha256: &str) -> io::Result<()> {
    use sha2::{Digest, Sha256};
    if !PHYSICAL_BWRAPS.iter().any(|b| Path::new(b) == path) {
        return Err(refused("namespace bwrap is not a deployed physical bwrap"));
    }
    let m = fs::symlink_metadata(path)?;
    if !m.file_type().is_file() || m.uid() != 0 || m.mode() & 0o022 != 0 || m.mode() & 0o111 == 0 {
        return Err(refused("namespace bwrap must be a root-owned non-writable executable"));
    }
    let mut f = OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC).open(path)?;
    let held = f.metadata()?;
    if (held.dev(), held.ino()) != (m.dev(), m.ino()) {
        return Err(refused("namespace bwrap changed while pinned"));
    }
    let mut bytes = Vec::new();
    f.read_to_end(&mut bytes)?;
    if sha256.len() != 64 || format!("{:x}", Sha256::digest(&bytes)) != sha256 {
        return Err(refused("namespace bwrap SHA-256 differs from its pin"));
    }
    Ok(())
}
fn map(program: &str, pid: u32, operator: u32, app: u32, controller: Option<u32>) -> io::Result<()> {
    eprintln!("namespace-map helper={program} pid={pid} operator={operator} app={app}");
    let mut args=vec![pid.to_string(), operator.to_string(), operator.to_string(), "1".into(), app.to_string(), app.to_string(), "1".into()];
    if let Some(uid)=controller { args.extend([uid.to_string(),uid.to_string(),"1".into()]); }
    let status = Command::new(program)
        .args(args)
        .env_clear()
        .status()?;
    if !status.success() {
        return Err(refused("namespace identity mapping refused"));
    }
    Ok(())
}
fn pipe() -> io::Result<(OwnedFd, OwnedFd)> {
    let mut fds = [0; 2];
    if unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) } != 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) })
}
fn exact_map(text: &str, op: u32, app: u32, controller:Option<u32>) -> bool {
    let rows:Result<Vec<Vec<u32>>,_>=text.lines().map(|r|r.split_whitespace().map(str::parse::<u32>).collect()).collect();
    let Ok(mut rows)=rows else{return false};
    let mut expected=vec![vec![op,op,1],vec![app,app,1]];
    if let Some(id)=controller {expected.push(vec![id,id,1]);}
    rows.sort();expected.sort();rows==expected
}
/// `bwrap --unshare-user --userns-block-fd 4 --info-fd 3` creates the namespace and,
/// given the block fd, writes no uid/gid map itself: it reports its namespaced child and
/// waits. newuidmap/newgidmap then map exactly {operator, app[, registered controller]} into it (the operator's
/// /etc/subuid and /etc/subgid grants cover the subordinate identities), this process holds the namespace by fd,
/// releases bwrap (whose child runs /usr/bin/true and exits), and joins by setns. The
/// joining process is single-threaded and keeps every capability of the namespace,
/// none of the host, until the bootstrap drops them.
pub(crate) fn enter(bwrap: &Path, bwrap_sha256: &str, operator_uid: u32, operator_gid: u32, app_uid: u32, app_gid: u32) -> io::Result<()> {
    enter_registered(bwrap,bwrap_sha256,operator_uid,operator_gid,app_uid,app_gid,None)
}
pub(crate) fn enter_registered(bwrap: &Path, bwrap_sha256: &str, operator_uid: u32, operator_gid: u32,
    app_uid: u32, app_gid: u32, controller:Option<&ControllerIdentity>) -> io::Result<()> {
    if controller.is_some_and(|c| c.uid==operator_uid || c.uid==app_uid || c.gid==operator_gid || c.gid==app_gid) {
        return Err(refused("registered controller overlaps operator or app"));
    }
    if unsafe { libc::geteuid() } == 0 || unsafe { libc::geteuid() } != operator_uid || unsafe { libc::getegid() } != operator_gid {
        return Err(refused("resident requires its unprivileged operator uid"));
    }
    pinned_bwrap(bwrap, bwrap_sha256)?;
    let (info_r, info_w) = pipe()?;
    let (block_r, block_w) = pipe()?;
    let (iw, br) = (info_w.as_raw_fd(), block_r.as_raw_fd());
    let mut command = Command::new(bwrap);
    command
        .env_clear()
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .args(["--unshare-user", "--die-with-parent", "--info-fd", "3", "--userns-block-fd", "4", "--ro-bind", "/", "/", "--", "/usr/bin/true"]);
    unsafe {
        command.pre_exec(move || {
            // Move both ends above 9 first so neither dup2 can land on the other.
            let i = libc::fcntl(iw, libc::F_DUPFD_CLOEXEC, 10);
            let b = libc::fcntl(br, libc::F_DUPFD_CLOEXEC, 10);
            if i < 0 || b < 0 || libc::dup2(i, 3) != 3 || libc::dup2(b, 4) != 4 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        });
    }
    let mut holder = command.spawn()?;
    drop(info_w);
    drop(block_r);
    let result = (|| -> io::Result<()> {
        let mut info = Vec::new();
        File::from(info_r).take(4096).read_to_end(&mut info)?;
        let info: serde_json::Value = serde_json::from_slice(&info).map_err(|_| refused("namespace bwrap info refused"))?;
        let pid = info
            .get("child-pid")
            .and_then(serde_json::Value::as_u64)
            .and_then(|p| u32::try_from(p).ok())
            .filter(|p| *p > 1)
            .ok_or_else(|| refused("namespace bwrap child absent"))?;
        let status = fs::read_to_string(format!("/proc/{pid}/status"))?;
        if !status.lines().any(|l| l.split_whitespace().collect::<Vec<_>>() == ["PPid:", &holder.id().to_string()]) {
            return Err(refused("namespace holder is not the bwrap child"));
        }
        let ns = File::open(format!("/proc/{pid}/ns/user"))?;
        if ns.metadata()?.ino() == fs::metadata("/proc/self/ns/user")?.ino() {
            return Err(refused("namespace bwrap did not create a user namespace"));
        }
        map("/usr/bin/newuidmap", pid, operator_uid, app_uid,controller.map(|c|c.uid))?;
        map("/usr/bin/newgidmap", pid, operator_gid, app_gid,controller.map(|c|c.gid))?;
        File::from(block_w).write_all(&[1])?;
        if !holder.wait()?.success() {
            return Err(refused("namespace bwrap failed"));
        }
        if unsafe { libc::setns(ns.as_raw_fd(), libc::CLONE_NEWUSER) } != 0 {
            return Err(io::Error::other(format!("namespace setns(CLONE_NEWUSER) refused: {}", io::Error::last_os_error())));
        }
        // newgidmap's privileged write preserves setgroups=allow; Linux refuses
        // setgroups until a gid_map exists. Clear groups immediately afterwards.
        if unsafe { libc::setgroups(0, std::ptr::null()) } != 0 {
            return Err(io::Error::other(format!("namespace empty groups refused after gid mapping: {}", io::Error::last_os_error())));
        }
        let uid = fs::read_to_string("/proc/self/uid_map")?;
        let gid = fs::read_to_string("/proc/self/gid_map")?;
        if !exact_map(&uid, operator_uid, app_uid,controller.map(|c|c.uid)) || !exact_map(&gid, operator_gid, app_gid,controller.map(|c|c.gid)) {
            return Err(refused("namespace identity maps differ from broker selection"));
        }
        CONTROLLER.set(controller.copied()).map_err(|_|refused("controller mapping initialized twice"))?;
        Ok(())
    })();
    if result.is_err() {
        let _ = holder.kill();
        let _ = holder.wait();
    }
    result
}
