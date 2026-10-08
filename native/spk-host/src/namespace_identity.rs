//! Enter a mapped user namespace before parsing resident bytes. The mapper
//! remains outside it; both resident and worker later drop all capability sets.
use std::fs::{self, File, Metadata, OpenOptions};
use std::io::{self, Read, Write};
use std::os::unix::fs::{MetadataExt, OpenOptionsExt};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::OnceLock;
use std::collections::BTreeMap;
static ROOTS: OnceLock<BTreeMap<PathBuf, (File, Metadata)>>=OnceLock::new();
fn refused(s: &str)->io::Error { io::Error::new(io::ErrorKind::PermissionDenied,s) }
/// Root in the initial namespace is unmapped inside the resident namespace.
/// Retained handles carry its verified provenance, never the overflow uid.
pub(crate) fn root_owned(path: &Path, observed: &Metadata) -> bool {
    if crate::os::root_owner(observed.uid()) { return true; }
    ROOTS.get().and_then(|roots|roots.get(path)).is_some_and(|(f, held)| {
        let Ok(current)=f.metadata() else { return false; };
        if (current.dev(),current.ino(),current.ctime(),current.ctime_nsec())!=(held.dev(),held.ino(),held.ctime(),held.ctime_nsec()) { return false; }
        (held.dev(),held.ino(),held.mode(),held.nlink(),held.len(),held.mtime(),held.mtime_nsec(),held.ctime(),held.ctime_nsec())
        ==(observed.dev(),observed.ino(),observed.mode(),observed.nlink(),observed.len(),observed.mtime(),observed.mtime_nsec(),observed.ctime(),observed.ctime_nsec())
    })
}
fn remember(path: &Path, roots: &mut BTreeMap<PathBuf,(File,Metadata)>) -> io::Result<()> {
    let m=fs::symlink_metadata(path)?;
    if m.file_type().is_symlink() || m.mode()&0o022!=0 { return Err(refused("namespace bootstrap custody path writable or symlinked")); }
    if m.uid()==0 {
        let f=OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW|libc::O_CLOEXEC|libc::O_PATH).open(path)?;
        let held=f.metadata()?;
        if held.uid()!=0 || (held.dev(),held.ino())!=(m.dev(),m.ino()) { return Err(refused("namespace bootstrap root handle changed")); }
        roots.insert(path.to_owned(),(f,held));
    } else if m.uid()!=unsafe{libc::geteuid()} { return Err(refused("namespace bootstrap custody path belongs to another principal")); }
    Ok(())
}
pub(crate) fn prepare_root_handles(config: &Path, root: &Path, store: &str, grain: &str) -> io::Result<()> {
    let mut roots=BTreeMap::new();
    for path in config.ancestors().skip(1) { remember(path,&mut roots)?; }
    let witness=root.join("attest").join(format!("{store}-{grain}.witness"));
    for path in witness.ancestors() { remember(path,&mut roots)?; }
    ROOTS.set(roots).map_err(|_|refused("namespace root provenance initialized twice"))
}
fn map(program: &str,pid: u32,operator: u32,app: u32) -> io::Result<()> {
    eprintln!("namespace-map helper={program} pid={pid} operator={operator} app={app}");
    let status=Command::new(program).args([pid.to_string(),operator.to_string(),operator.to_string(),"1".into(),app.to_string(),app.to_string(),"1".into()]).env_clear().status()?;
    if !status.success() { return Err(refused("namespace identity mapping refused")); }
    Ok(())
}
pub(crate) fn enter(operator_uid:u32,operator_gid:u32,app_uid:u32,app_gid:u32)->io::Result<()> {
    if unsafe{libc::geteuid()}==0 || unsafe{libc::geteuid()}!=operator_uid || unsafe{libc::getegid()}!=operator_gid {
        return Err(refused("resident requires its unprivileged operator uid"));
    }
    let (mut a,mut b)=UnixStream::pair()?;
    a.set_read_timeout(Some(std::time::Duration::from_secs(10)))?;
    b.set_read_timeout(Some(std::time::Duration::from_secs(10)))?;
    let parent=std::process::id();
    let mapper=unsafe{libc::fork()};
    if mapper<0 { return Err(io::Error::last_os_error()); }
    if mapper==0 {
        drop(a);
        let result=(||->io::Result<()> {
            let mut ready=[0];b.read_exact(&mut ready)?;
            if ready!=[1] { return Err(refused("namespace mapper handshake refused")); }
            map("/usr/bin/newuidmap",parent,operator_uid,app_uid)?;
            map("/usr/bin/newgidmap",parent,operator_gid,app_gid)?;
            b.write_all(&[1])
        })();
        if let Err(e)=&result { eprintln!("{e}"); }
        unsafe{libc::_exit(if result.is_ok(){0}else{1})}
    }
    drop(b);
    let result=(||->io::Result<()> {
        if unsafe{libc::unshare(libc::CLONE_NEWUSER)}!=0 { return Err(io::Error::other(format!("namespace unshare(CLONE_NEWUSER) refused: {}",io::Error::last_os_error()))); }
        // newgidmap's privileged write preserves setgroups=allow; Linux refuses
        // setgroups until a gid_map exists. Clear groups immediately afterwards.
        if unsafe{libc::prctl(libc::PR_SET_DUMPABLE,1,0,0,0)}!=0 { return Err(io::Error::last_os_error()); }
        a.write_all(&[1])?;let mut ready=[0];a.read_exact(&mut ready)?;
        if ready!=[1] { return Err(refused("namespace mapping did not complete")); }
        if unsafe{libc::setgroups(0,std::ptr::null())}!=0 { return Err(io::Error::other(format!("namespace empty groups refused after gid mapping: {}",io::Error::last_os_error()))); }
        let uid=fs::read_to_string("/proc/self/uid_map")?;
        let gid=fs::read_to_string("/proc/self/gid_map")?;
        let exact=|text: &str, op: u32, app: u32| {
            let rows:Vec<Vec<u32>>=text.lines().map(|r|r.split_whitespace().filter_map(|n|n.parse().ok()).collect()).collect();
            rows.len()==2 && rows.contains(&vec![op,op,1]) && rows.contains(&vec![app,app,1])
        };
        if !exact(&uid,operator_uid,app_uid) || !exact(&gid,operator_gid,app_gid) { return Err(refused("namespace identity maps differ from broker selection")); }
        Ok(())
    })();
    drop(a);let mut status=0;
    let waited=unsafe{libc::waitpid(mapper,&mut status,0)};
    result?;
    if waited!=mapper || status!=0 { return Err(refused("namespace mapper failed")); }
    Ok(())
}
