//! Root volume copies retain every directory/file handle. A durable freeze
//! intent precedes the cgroup freeze of the grain's processes; startup takes
//! the same lock and thaws exactly the cgroups the intent names. No path-based
//! chown, destination reopen or thaw. (The volume is a quota directory, not a
//! filesystem of its own, so there is no filesystem to freeze: G6 of
//! deploy/spk-host/VOLUMES.md.)
use crate::io_context::IoContext;
use super::*;
use std::io::{Seek,SeekFrom};
use std::os::unix::process::CommandExt;

pub(super) struct Dir(pub(super) File);
fn component(name:&str)->io::Result<CString>{
    if name.is_empty() || matches!(name,"."|"..") || name.contains('/') {
        return Err(invalid("volume custody component refused"));
    }
    CString::new(name).map_err(|_|invalid("NUL volume component"))
}
impl Dir {
    pub(super) fn absolute(path:&Path,allowed:&[u32])->io::Result<Self>{
        if !path.is_absolute(){return Err(invalid("volume custody absolute directory required"))}
        let mut dir=Self(File::open("/").ctx("open", &"/")?);
        for part in path.components().skip(1) {
            let std::path::Component::Normal(part)=part else{return Err(invalid("noncanonical volume path"))};
            let name=part.to_str().ok_or_else(||invalid("volume path encoding"))?;
            dir=dir.directory(name,allowed)?;
        }
        Ok(dir)
    }
    pub(super) fn directory(&self,name:&str,allowed:&[u32])->io::Result<Self>{
        let name=component(name)?;
        let fd=unsafe{libc::openat(self.0.as_raw_fd(),name.as_ptr(),libc::O_RDONLY|libc::O_DIRECTORY|libc::O_NOFOLLOW|libc::O_CLOEXEC)};
        if fd<0{return Err(io::Error::last_os_error())}
        let file=unsafe{File::from_raw_fd(fd)};
        let m=file.metadata()?;
        // `0` in `allowed` is root, whichever account holds root (src/os.rs).
        let owner_allowed=allowed.iter().any(|a| *a==m.uid() || (*a==0 && crate::os::root_owner(m.uid())));
        if !m.is_dir() || !owner_allowed || m.mode()&0o022!=0 {
            return Err(invalid("volume directory retained identity refused"));
        }
        Ok(Self(file))
    }
    fn create_dir(&self,name:&str)->io::Result<Self>{
        let c=component(name)?;
        if unsafe{libc::mkdirat(self.0.as_raw_fd(),c.as_ptr(),0o700)}!=0{
            let e=io::Error::last_os_error();
            if e.raw_os_error()!=Some(libc::EEXIST){return Err(e)}
        }
        self.directory(name,&[unsafe{libc::geteuid()}])
    }
    fn create(&self,name:&str)->io::Result<File>{
        let c=component(name)?;
        let fd=unsafe{libc::openat(self.0.as_raw_fd(),c.as_ptr(),
            libc::O_RDWR|libc::O_CREAT|libc::O_EXCL|libc::O_NOFOLLOW|libc::O_CLOEXEC,0o600)};
        if fd<0{return Err(io::Error::last_os_error())}
        let f=unsafe{File::from_raw_fd(fd)};
        let m=f.metadata()?;
        if !m.is_file() || m.uid()!=unsafe{libc::geteuid()} || m.nlink()!=1 || m.mode()&0o777!=0o600 {
            return Err(invalid("new volume copy retained identity refused"));
        }
        Ok(f)
    }
    pub(super) fn read_root(&self,name:&str)->io::Result<File>{
        let c=component(name)?;
        let fd=unsafe{libc::openat(self.0.as_raw_fd(),c.as_ptr(),libc::O_RDONLY|libc::O_NOFOLLOW|libc::O_CLOEXEC|libc::O_NONBLOCK)};
        if fd<0{return Err(io::Error::last_os_error())}
        let f=unsafe{File::from_raw_fd(fd)};let m=f.metadata()?;
        if !m.is_file() || m.uid()!=unsafe{libc::geteuid()} || m.nlink()!=1 || m.mode()&0o022!=0 {
            return Err(invalid("root volume source retained identity refused"));
        }
        Ok(f)
    }
    fn same_leaf(&self,name:&str,f:&File)->io::Result<()>{
        let c=component(name)?;let mut s=unsafe{std::mem::zeroed::<libc::stat>()};
        if unsafe{libc::fstatat(self.0.as_raw_fd(),c.as_ptr(),&mut s,libc::AT_SYMLINK_NOFOLLOW)}!=0 {
            return Err(io::Error::last_os_error());
        }
        let m=f.metadata()?;
        if s.st_dev!=m.dev() || s.st_ino!=m.ino() || s.st_mode&libc::S_IFMT!=libc::S_IFREG || m.nlink()!=1 {
            return Err(invalid("volume destination name switched; retained file preserved"));
        }
        Ok(())
    }
    fn unlink(&self,name:&str)->io::Result<()>{
        let c=component(name)?;
        if unsafe{libc::unlinkat(self.0.as_raw_fd(),c.as_ptr(),0)}!=0{return Err(io::Error::last_os_error())}
        Ok(())
    }
    fn lock(&self)->io::Result<File>{
        let name=component(".freeze.lock")?;
        let fd=unsafe{libc::openat(self.0.as_raw_fd(),name.as_ptr(),libc::O_RDWR|libc::O_CREAT|libc::O_NOFOLLOW|libc::O_CLOEXEC,0o600)};
        if fd<0{return Err(io::Error::last_os_error())}
        let f=unsafe{File::from_raw_fd(fd)};let m=f.metadata()?;
        if !m.is_file() || m.uid()!=unsafe{libc::geteuid()} || m.nlink()!=1 || m.mode()&0o777!=0o600 {
            return Err(invalid("freeze lock retained identity refused"));
        }
        if unsafe{libc::flock(f.as_raw_fd(),libc::LOCK_EX|libc::LOCK_NB)}!=0 {
            return Err(invalid("another live source-owned volume capture holds freeze custody"));
        }
        Ok(f)
    }
}
fn change_owner(f:&File,uid:u32,gid:u32)->io::Result<()>{
    let before=f.metadata()?;
    if unsafe{libc::fchown(f.as_raw_fd(),uid,gid)}!=0{return Err(io::Error::last_os_error())}
    let after=f.metadata()?;
    if (before.dev(),before.ino())!=(after.dev(),after.ino()) || after.uid()!=uid || after.gid()!=gid {
        return Err(invalid("retained export ownership differs"));
    }
    Ok(())
}
fn root_volume_uid(root:&Path,name:&str)->io::Result<u32>{
    let volumes=Dir::absolute(root,&[0])?.directory("volumes",&[0])?;
    let f=volumes.read_root(&format!("{name}.conf"))?;
    if f.metadata()?.len()>MAX_CONFIG{return Err(invalid("volume config bound"))}
    let mut text=String::new();f.take(MAX_CONFIG+1).read_to_string(&mut text)?;
    let values:Vec<_>=text.lines().filter_map(|line|line.strip_prefix("app_uid=")).collect();
    if values.len()!=1{return Err(invalid("registered volume app UID absent or repeated"))}
    let uid=values[0].parse::<u32>().map_err(|_|invalid("registered volume UID invalid"))?;
    if uid<100{return Err(invalid("registered volume UID privileged"))}
    Ok(uid)
}
const CGROUP_ROOT:&str="/sys/fs/cgroup";
fn cgroup_path_ok(path:&Path)->bool{
    path.starts_with(CGROUP_ROOT) && path.components().all(|c|!matches!(c,std::path::Component::ParentDir|std::path::Component::CurDir))
}
fn group_unit_name(store:&str,app:&str,name:&str)->bool{
    let prefix=format!("mini-spk-s{store}-a{app}-g");
    name.strip_prefix(&prefix).and_then(|r|r.strip_suffix(".service")).is_some_and(decimal)
}
/// The cgroups of the grain's resident units in the operator's user manager.
fn grain_groups(base:&Path,store:&str,app:&str)->io::Result<Vec<PathBuf>>{
    fn visit(dir:&Path,depth:usize,store:&str,app:&str,out:&mut Vec<PathBuf>)->io::Result<()>{
        let entries=match fs::read_dir(dir){Ok(e)=>e,Err(e) if e.kind()==io::ErrorKind::NotFound=>return Ok(()),Err(e)=>return Err(e)};
        for entry in entries{
            let entry=entry?;
            if !entry.file_type()?.is_dir(){continue}
            let name=entry.file_name().to_string_lossy().into_owned();
            if group_unit_name(store,app,&name){out.push(entry.path());continue}
            if depth<8 && (name.ends_with(".slice") || name.ends_with(".service")) {visit(&entry.path(),depth+1,store,app,out)?}
        }
        Ok(())
    }
    let mut out=Vec::new();visit(base,0,store,app,&mut out)?;out.sort();Ok(out)
}
fn write_freeze(group:&Path,value:&str)->io::Result<()>{
    let file=group.join("cgroup.freeze");
    fs::write(&file,value).ctx("write",&file)
}
fn frozen_state(group:&Path)->io::Result<bool>{
    let events=group.join("cgroup.events");
    let text=fs::read_to_string(&events).ctx("read",&events)?;
    Ok(text.lines().any(|l|l=="frozen 1"))
}
/// Whether a live process of `uid` sits outside every group in `groups` (a process the freeze
/// would not hold). `/proc` is read as root, so none is hidden.
fn unfrozen_process_of(uid:u32,groups:&[PathBuf])->io::Result<Option<u32>>{
    for entry in fs::read_dir("/proc").ctx("list","/proc")?{
        let entry=entry?;
        let Some(pid)=entry.file_name().to_str().and_then(|n|n.parse::<u32>().ok()) else{continue};
        let Ok(status)=fs::read_to_string(entry.path().join("status")) else{continue};
        let real=status.lines().find_map(|l|l.strip_prefix("Uid:")).and_then(|l|l.split_whitespace().next()).and_then(|n|n.parse::<u32>().ok());
        let zombie=status.lines().any(|l|l.starts_with("State:") && l.contains("Z"));
        if real!=Some(uid) || zombie{continue}
        let Ok(cg)=fs::read_to_string(entry.path().join("cgroup")) else{continue};
        let held=cg.lines().filter_map(|l|l.strip_prefix("0::")).any(|p|{
            let full=Path::new(CGROUP_ROOT).join(p.trim_start_matches('/'));
            groups.iter().any(|g|full.starts_with(g))
        });
        if !held{return Ok(Some(pid))}
    }
    Ok(None)
}
#[derive(Serialize,Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Pending {protocol:String,name:String,groups:Vec<String>}
struct Frozen {dir:Dir,groups:Vec<PathBuf>,name:String,_lock:File,finished:bool}
impl Frozen {
    /// Freeze the grain's running processes (none when it is stopped). `cgroups` is the
    /// operator manager's cgroup directory.
    fn begin(root:&Path,store:&str,app:&str,operator_uid:u32,cgroups:&Path)->io::Result<Self>{
        let name=volume_name(store,app);
        let grains=Dir::absolute(root,&[0])?;
        let app_uid=root_volume_uid(root,&name)?;
        let dir=grains.directory("volume-custody",&[0])?.create_dir("freezes")?;
        let lock=dir.lock()?;
        recover_locked(&dir)?;
        let _=operator_uid;
        let groups=grain_groups(cgroups,store,app)?;
        let pending=Pending{protocol:"mini-spk-freeze-pending-v2".into(),name:name.clone(),
            groups:groups.iter().map(|g|g.to_string_lossy().into_owned()).collect()};
        let leaf=format!("{name}.json");
        let mut file=dir.create(&leaf)?;
        file.write_all(&serde_json::to_vec(&pending)?)?;
        let this=Self{dir,groups,name:leaf,_lock:lock,finished:false};
        let held=(||->io::Result<()>{
            for g in &this.groups{write_freeze(g,"1")?}
            let deadline=std::time::Instant::now()+Duration::from_secs(10);
            for g in &this.groups{
                while !frozen_state(g)?{
                    if std::time::Instant::now()>deadline{return Err(invalid("grain cgroup did not freeze in time"))}
                    std::thread::sleep(Duration::from_millis(5));
                }
            }
            if let Some(pid)=unfrozen_process_of(app_uid,&this.groups)?{
                return Err(invalid(format!("process {pid} of the grain's uid is outside the frozen cgroups; the capture would not be consistent")));
            }
            Ok(())
        })();
        if let Err(error)=held{
            // Our freeze never completed: thaw what we froze and drop the intent.
            let _=this.thaw();
            return Err(error)
        }
        Ok(this)
    }
    fn finish(mut self)->io::Result<()>{
        self.thaw()?;self.finished=true;Ok(())
    }
    fn thaw(&self)->io::Result<()>{
        clear_pending(&self.dir,&self.name,||thaw_groups(&self.groups))
    }
}
impl Drop for Frozen {
    fn drop(&mut self){
        if !self.finished{let _=self.thaw();} // SIGKILL retains intent for startup.
    }
}
fn thaw_groups(groups:&[PathBuf])->io::Result<()>{
    for g in groups{
        if !cgroup_path_ok(g){return Err(invalid("freeze intent names a path outside the cgroup tree"))}
        match write_freeze(g,"0"){
            Ok(())=>{},
            Err(e) if e.kind()==io::ErrorKind::NotFound=>{}, // the group is gone: nothing is frozen
            Err(e)=>return Err(e),
        }
    }
    Ok(())
}
// Called while holding freeze custody. An unsuccessful thaw never erases the
// durable repair obligation.
fn clear_pending(dir:&Dir,leaf:&str,thaw:impl FnOnce()->io::Result<()>)->io::Result<()>{
    thaw()?;
    dir.unlink(leaf)
}
fn recover_locked(dir:&Dir)->io::Result<()>{
    let listing=PathBuf::from(format!("/proc/self/fd/{}",dir.0.as_raw_fd()));
    for entry in fs::read_dir(&listing).ctx("list", &listing)?{
        let leaf=entry?.file_name().to_string_lossy().into_owned();
        if leaf==".freeze.lock"{continue}
        if !leaf.ends_with(".json"){return Err(invalid("unknown freeze custody artifact"))}
        let file=dir.read_root(&leaf)?;
        if file.metadata()?.len()>65536{return Err(invalid("freeze intent exceeds bound"))}
        let p:Pending=serde_json::from_reader(file)?;
        let (store,app)=p.name.split_once('-').ok_or_else(||invalid("freeze coordinate"))?;
        if p.protocol!="mini-spk-freeze-pending-v2" || !store_key(store) || !decimal(app)
            || leaf!=format!("{}.json",p.name){return Err(invalid("freeze intent coordinate refused"))}
        let groups:Vec<PathBuf>=p.groups.iter().map(PathBuf::from).collect();
        if groups.iter().any(|g|!cgroup_path_ok(g)||g.file_name().and_then(|n|n.to_str()).is_none_or(|n|!group_unit_name(store,app,n))){
            return Err(invalid("freeze intent names a group that is not this grain's unit"))
        }
        clear_pending(dir,&leaf,||thaw_groups(&groups))?;
    }
    Ok(())
}
pub(super) fn recover(root:&Path)->io::Result<()>{
    let grains=Dir::absolute(root,&[0])?;
    let dir=grains.directory("volume-custody",&[0])?.create_dir("freezes")?;
    let _lock=dir.lock()?;
    recover_locked(&dir)
}
fn sparse_copy(source:&mut File,out:&mut File)->io::Result<()>{
    let length=source.metadata()?.len();out.set_len(length)?;
    let mut offset=0;
    while offset<length {
        let data=unsafe{libc::lseek(source.as_raw_fd(),offset as i64,libc::SEEK_DATA)};
        if data<0 {
            let error=io::Error::last_os_error();
            if error.raw_os_error()==Some(libc::ENXIO){break}
            if error.raw_os_error()==Some(libc::EINVAL){
                source.seek(SeekFrom::Start(0))?;out.seek(SeekFrom::Start(0))?;
                let copied=io::copy(source,out)?;
                if copied!=length{return Err(invalid("volume image changed during copy"))}
                return Ok(())
            }
            return Err(error)
        }
        let hole=unsafe{libc::lseek(source.as_raw_fd(),data,libc::SEEK_HOLE)};
        if hole<0{return Err(io::Error::last_os_error())}
        let end=(hole as u64).min(length);
        if end<=data as u64{return Err(invalid("volume extent did not advance"))}
        source.seek(SeekFrom::Start(data as u64))?;out.seek(SeekFrom::Start(data as u64))?;
        if io::copy(&mut (&mut *source).take(end-data as u64),out)?!=end-data as u64 {
            return Err(invalid("volume extent changed during copy"));
        }
        offset=end;
    }
    Ok(())
}
/// The operator manager's cgroup directory, where a grain's resident units live.
fn operator_cgroups(operator_uid:u32)->PathBuf{
    PathBuf::from(format!("{CGROUP_ROOT}/user.slice/user-{operator_uid}.slice/user@{operator_uid}.service"))
}
/// Build the export image of a quiesced volume: an ext4 image of its tree, made by `mke2fs -d`
/// as the grain's uid with no privilege (symlinks stay links, nothing is followed), into a stage
/// the grain's uid owns. Returns the open image.
fn build_image(root:&Path,name:&str,app_uid:u32,size_mib:u64)->io::Result<(File,String)>{
    let vars=Dir::absolute(root,&[0])?.directory("vars",&[0])?;
    let stage_name=format!(".export-{name}");
    let c=component(&stage_name)?;
    if unsafe{libc::mkdirat(vars.0.as_raw_fd(),c.as_ptr(),0o700)}!=0{return Err(io::Error::last_os_error())}
    let built=(||->io::Result<File>{
        let stage=vars.directory(&stage_name,&[unsafe{libc::geteuid()}])?;
        change_owner(&stage.0,app_uid,app_uid)?;
        let image=stage.create("image.ext4")?;
        image.set_len(super::volume_dir::export_image_bytes(size_mib))?;
        change_owner(&image,app_uid,app_uid)?;
        let uid=app_uid.to_string();
        let tree=root.join("vars").join(name);
        let stage_path=root.join("vars").join(&stage_name);
        let output=Command::new("/usr/bin/setpriv")
            .args([&format!("--reuid={uid}"),&format!("--regid={uid}"),"--clear-groups","--no-new-privs","--inh-caps=-all","--bounding-set=-all","--","/usr/sbin/mke2fs"])
            .args(["-q","-t","ext4","-F","-d"]).arg(&tree).arg("image.ext4")
            .current_dir(&stage_path).env_clear().env("PATH","/usr/sbin:/usr/bin:/sbin:/bin").stdin(Stdio::null()).output()?;
        if !output.status.success(){
            return Err(invalid(format!("volume export image build failed: {}",String::from_utf8_lossy(&output.stderr).trim())))
        }
        Ok(image)
    })();
    Ok((built.map_err(|e|{ let _=remove_stage(&vars,&stage_name); e})?,stage_name))
}
fn remove_stage(vars:&Dir,stage_name:&str)->io::Result<()>{
    let c=component(stage_name)?;
    // The stage is the grain uid's; it is opened by descriptor, never by owner expectation.
    let fd=unsafe{libc::openat(vars.0.as_raw_fd(),c.as_ptr(),libc::O_RDONLY|libc::O_DIRECTORY|libc::O_NOFOLLOW|libc::O_CLOEXEC)};
    if fd>=0{
        let stage=unsafe{File::from_raw_fd(fd)};
        super::volume_dir::remove_contents(stage.as_raw_fd())?;
    }
    if unsafe{libc::unlinkat(vars.0.as_raw_fd(),c.as_ptr(),libc::AT_REMOVEDIR)}!=0{return Err(io::Error::last_os_error())}
    Ok(())
}
pub(super) fn export(root:&Path,store:&str,app:&str,uid:u32,gid:u32)->io::Result<Value>{
    let grains=Dir::absolute(root,&[0])?;
    let op=grains.directory(store,&[uid])?;
    let exports=match op.directory("exports",&[uid]){
        Ok(dir)=>dir,
        Err(e) if e.kind()==io::ErrorKind::NotFound=>{
            let dir=op.create_dir("exports")?;
            change_owner(&dir.0,uid,gid)?;dir
        },
        Err(e)=>return Err(e),
    };
    if exports.0.metadata()?.mode()&0o777!=0o700 {
        return Err(invalid("exports directory must remain private"));
    }
    let name=volume_name(store,app);
    let registered=super::volume_dir::capture_target(root,&name)?;
    let stamp=SystemTime::now().duration_since(UNIX_EPOCH).map_err(|_|invalid("clock"))?.as_nanos();
    let leaf=format!("{app}-{stamp}.ext4");
    let mut out=exports.create(&leaf)?;
    let freeze_started=std::time::Instant::now();
    let frozen=Frozen::begin(root,store,app,uid,&operator_cgroups(uid))?;
    let copied=(||->io::Result<String>{
        let before=super::volume_dir::fingerprint(registered.dir.as_raw_fd())?;
        let (mut image,stage_name)=build_image(root,&name,registered.app_uid,registered.size_mib)?;
        let result=(||->io::Result<String>{
            let after=super::volume_dir::fingerprint(registered.dir.as_raw_fd())?;
            if before!=after{return Err(invalid("volume tree changed during capture"))}
            sparse_copy(&mut image,&mut out)?;
            out.seek(SeekFrom::Start(0))?;file_sha256(&mut out)
        })();
        let vars=Dir::absolute(root,&[0])?.directory("vars",&[0])?;
        let _=remove_stage(&vars,&stage_name);
        result
    })();
    frozen.finish()?;
    let frozen_ms=freeze_started.elapsed().as_millis();
    let hash=copied?;
    exports.same_leaf(&leaf,&out)?;
    let fsck=inspect_copy("/usr/sbin/e2fsck",&["-fn"],&out)?;
    let listing=inspect_copy("/usr/sbin/debugfs",&["-R","ls -l /"],&out)?;
    change_owner(&out,uid,gid)?;
    exports.same_leaf(&leaf,&out)?;
    Ok(json!({"image":root.join(store).join("exports").join(leaf),"sha256":hash,
        "bytes":out.metadata()?.len().to_string(),"frozenMs":frozen_ms.to_string(),"e2fsck":if fsck.status.success(){"clean"}else{"errors"},
        "rootListing":String::from_utf8_lossy(&listing.stdout).lines().map(str::trim).filter(|line|!line.is_empty()).collect::<Vec<_>>()}))
}

pub(super) fn inspect_copy(program:&str,args:&[&str],file:&File)->io::Result<std::process::Output>{
    let fd=file.as_raw_fd();
    let mut cmd=Command::new(program);
    cmd.args(args).arg(format!("/proc/self/fd/{fd}")).stdin(Stdio::null()).env_clear();
    unsafe{cmd.pre_exec(move||{
        if libc::fcntl(fd,libc::F_SETFD,0)<0{return Err(io::Error::last_os_error())}
        Ok(())
    });}
    cmd.output()
}


#[cfg(test)]
mod tests {
    use super::*;
    struct Scratch(PathBuf);
    impl Scratch {
        fn new()->Self {
            let p=std::env::temp_dir().join(format!("mini-volume-custody-{}-{}",std::process::id(),SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos()));
            fs::create_dir(&p).unwrap();fs::set_permissions(&p,fs::Permissions::from_mode(0o700)).unwrap();Self(p)
        }
        fn dir(&self)->Dir {Dir(File::open(&self.0).unwrap())}
    }
    impl Drop for Scratch {fn drop(&mut self){let _=fs::remove_dir_all(&self.0);}}
    #[test]
    fn volume_custody_symlink_switch_never_chowns_or_writes_victim(){
        let scratch=Scratch::new();let dir=scratch.dir();
        fs::write(scratch.0.join("victim"),b"untouched").unwrap();
        let before=fs::metadata(scratch.0.join("victim")).unwrap();
        let mut owned=dir.create("copy").unwrap();owned.write_all(b"captured").unwrap();
        fs::rename(scratch.0.join("copy"),scratch.0.join("retained")).unwrap();
        std::os::unix::fs::symlink("victim",scratch.0.join("copy")).unwrap();
        assert!(dir.same_leaf("copy",&owned).is_err());
        change_owner(&owned,unsafe{libc::geteuid()},unsafe{libc::getegid()}).unwrap();
        owned.write_all(b" only-owned").unwrap();
        assert_eq!(fs::read(scratch.0.join("victim")).unwrap(),b"untouched");
        let after=fs::metadata(scratch.0.join("victim")).unwrap();
        assert_eq!((before.dev(),before.ino(),before.uid(),before.gid()),(after.dev(),after.ino(),after.uid(),after.gid()));
        assert!(dir.read_root("copy").is_err());
    }
    #[test]
    fn volume_custody_parent_switch_keeps_fd_relative_creation(){
        let scratch=Scratch::new();let parent=scratch.dir();let retained=parent.create_dir("destination").unwrap();
        fs::create_dir(scratch.0.join("victim")).unwrap();
        fs::rename(scratch.0.join("destination"),scratch.0.join("old")).unwrap();
        std::os::unix::fs::symlink("victim",scratch.0.join("destination")).unwrap();
        let mut output=retained.create("image").unwrap();output.write_all(b"source bytes").unwrap();
        assert!(!scratch.0.join("victim/image").exists());
        assert_eq!(fs::read(scratch.0.join("old/image")).unwrap(),b"source bytes");
        assert!(parent.directory("destination",&[unsafe{libc::geteuid()}]).is_err());
    }
    #[test]
    fn volume_custody_hardlinks_and_nonprivate_directory_refuse(){
        let scratch=Scratch::new();let dir=scratch.dir();let f=dir.create("source").unwrap();
        fs::hard_link(scratch.0.join("source"),scratch.0.join("alias")).unwrap();
        assert!(dir.read_root("source").is_err());assert!(dir.same_leaf("source",&f).is_err());
        fs::create_dir(scratch.0.join("shared")).unwrap();fs::set_permissions(scratch.0.join("shared"),fs::Permissions::from_mode(0o777)).unwrap();
        assert!(dir.directory("shared",&[unsafe{libc::geteuid()}]).is_err());
        assert!(component("../escape").is_err());
    }
    #[test]
    fn volume_custody_sparse_copy_hashes_retained_exact_bytes(){
        let scratch=Scratch::new();let dir=scratch.dir();let mut source=dir.create("source").unwrap();
        source.set_len(1024*1024).unwrap();source.seek(SeekFrom::Start(500000)).unwrap();source.write_all(b"private checkpoint").unwrap();
        let mut out=dir.create("copy").unwrap();sparse_copy(&mut source,&mut out).unwrap();
        source.seek(SeekFrom::Start(0)).unwrap();out.seek(SeekFrom::Start(0)).unwrap();
        assert_eq!(file_sha256(&mut source).unwrap(),file_sha256(&mut out).unwrap());
        assert_eq!(out.metadata().unwrap().len(),1024*1024);
        fs::rename(scratch.0.join("copy"),scratch.0.join("retained")).unwrap();
        std::os::unix::fs::symlink("source",scratch.0.join("copy")).unwrap();
        assert!(dir.same_leaf("copy",&out).is_err());
    }
    #[test]
    fn volume_custody_failed_thaw_preserves_durable_repair_obligation(){
        let scratch=Scratch::new();let dir=scratch.dir();
        let mut pending=dir.create("frozen.json").unwrap();pending.write_all(b"exact retained filesystem").unwrap();
        assert!(clear_pending(&dir,"frozen.json",||Err(io::Error::from_raw_os_error(libc::EIO))).is_err());
        assert_eq!(fs::read(scratch.0.join("frozen.json")).unwrap(),b"exact retained filesystem");
        clear_pending(&dir,"frozen.json",||Ok(())).unwrap();
        assert!(!scratch.0.join("frozen.json").exists());
    }
    #[test]
    fn volume_custody_live_capture_lock_refuses_competing_recovery(){
        let scratch=Scratch::new();let dir=scratch.dir();
        let held=dir.lock().unwrap();assert!(dir.lock().is_err());
        drop(held);assert!(dir.lock().is_ok());
    }

    fn physical_receiving_root()->PathBuf {
        assert_eq!(unsafe{libc::geteuid()},0,"explicit root disposable receiver only");
        let root=PathBuf::from(std::env::var_os("MINI_VOLUME_QUOTA_ROOT").expect("explicit owned grains root"));
        assert!(root.to_string_lossy().starts_with("/var/lib/mini-spk-volume-test-"));
        root
    }
    const PHYS_STORE:&str="1111111111111111";
    const PHYS_APP:&str="990010";
    const PHYS_UID:u32=64010;
    #[test]
    #[ignore = "explicit disposable root cgroup worker; only launched by receiving parent"]
    fn volume_custody_physical_freeze_worker(){
        let root=physical_receiving_root();assert_eq!(std::env::var("MINI_VOLUME_CUSTODY_WORKER").unwrap(),"yes");
        let _guard=Frozen::begin(&root,PHYS_STORE,PHYS_APP,0,Path::new(CGROUP_ROOT)).unwrap();
        let mut ready=OpenOptions::new().write(true).create_new(true).mode(0o600).open(root.join("worker-ready")).unwrap();
        ready.write_all(b"frozen and intent durable").unwrap();
        loop{std::thread::sleep(Duration::from_millis(100));}
    }
    #[test]
    #[ignore = "explicit root-only cgroup2 host; actual SIGKILL/freeze recovery qualification"]
    fn volume_custody_physical_process_death_thaws_exact_cgroup(){
        let root=physical_receiving_root();
        let (dep,host,vid)=("a".repeat(64),"b".repeat(64),"d".repeat(64));
        let volume=super::volume_dir::Volume{root:&root,store:PHYS_STORE,grain:PHYS_APP,app_uid:PHYS_UID,size_mib:64,volume_id:&vid,custodian:None,deployment_id:&dep,host_id:&host};
        volume.create(None).unwrap();
        fs::create_dir_all(root.join("volume-custody")).unwrap();
        let group=Path::new(CGROUP_ROOT).join(format!("mini-spk-s{PHYS_STORE}-a{PHYS_APP}-g1.service"));
        fs::create_dir(&group).unwrap();
        use std::os::unix::process::CommandExt;
        let sleeper=Command::new("/usr/bin/sleep").arg("1000").uid(PHYS_UID).gid(PHYS_UID).spawn().unwrap();
        fs::write(group.join("cgroup.procs"),sleeper.id().to_string()).unwrap();
        struct Cleanup{group:PathBuf,sleeper:std::process::Child,worker:Option<std::process::Child>}
        impl Drop for Cleanup{fn drop(&mut self){
            if let Some(w)=self.worker.as_mut(){let _=w.kill();let _=w.wait();}
            let _=fs::write(self.group.join("cgroup.freeze"),"0");
            let _=self.sleeper.kill();let _=self.sleeper.wait();
            for _ in 0..50{ if fs::remove_dir(&self.group).is_ok(){break} std::thread::sleep(Duration::from_millis(20)); }
        }}
        let mut cleanup=Cleanup{group:group.clone(),sleeper,worker:None};
        cleanup.worker=Some(Command::new(std::env::current_exe().unwrap())
            .args(["--exact","broker::volume_custody::tests::volume_custody_physical_freeze_worker","--ignored","--nocapture"])
            .env("MINI_VOLUME_CUSTODY_WORKER","yes").spawn().unwrap());
        let ready=root.join("worker-ready");let _=fs::remove_file(&ready);let deadline=std::time::Instant::now()+Duration::from_secs(10);
        while !ready.exists(){
            assert!(cleanup.worker.as_mut().unwrap().try_wait().unwrap().is_none(),"freeze worker exited before ready");
            assert!(std::time::Instant::now()<deadline,"bounded freeze worker readiness");
            std::thread::sleep(Duration::from_millis(10));
        }
        let intent=root.join(format!("volume-custody/freezes/{PHYS_STORE}-{PHYS_APP}.json"));assert!(intent.is_file());
        assert!(fs::read_to_string(group.join("cgroup.events")).unwrap().contains("frozen 1"));
        let mut worker=cleanup.worker.take().unwrap();
        worker.kill().unwrap();let status=worker.wait().unwrap();
        use std::os::unix::process::ExitStatusExt;assert_eq!(status.signal(),Some(libc::SIGKILL));
        assert!(intent.is_file(),"SIGKILL must retain durable freeze obligation");
        assert!(fs::read_to_string(group.join("cgroup.events")).unwrap().contains("frozen 1"),"the grain stays frozen until recovery");
        recover(&root).unwrap();assert!(!intent.exists());
        let deadline=std::time::Instant::now()+Duration::from_secs(5);
        while fs::read_to_string(group.join("cgroup.events")).unwrap().contains("frozen 1"){
            assert!(std::time::Instant::now()<deadline,"recovery thawed exactly the named cgroup");
            std::thread::sleep(Duration::from_millis(10));
        }
        volume.destroy().unwrap();
    }
}
