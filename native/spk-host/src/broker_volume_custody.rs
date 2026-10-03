//! Root volume copies retain every directory/file handle. A durable freeze
//! intent precedes FIFREEZE; startup takes the same lock and reconciles only
//! that exact filesystem. No path-based chown, destination reopen or thaw.
use super::*;
use std::io::{Seek,SeekFrom};
use std::os::unix::process::CommandExt;

const FIFREEZE:libc::c_ulong=0xc0045877;
const FITHAW:libc::c_ulong=0xc0045878;
struct Dir(File);
fn component(name:&str)->io::Result<CString>{
    if name.is_empty() || matches!(name,"."|"..") || name.contains('/') {
        return Err(invalid("volume custody component refused"));
    }
    CString::new(name).map_err(|_|invalid("NUL volume component"))
}
impl Dir {
    fn absolute(path:&Path,allowed:&[u32])->io::Result<Self>{
        if !path.is_absolute(){return Err(invalid("volume custody absolute directory required"))}
        let mut dir=Self(File::open("/")?);
        for part in path.components().skip(1) {
            let std::path::Component::Normal(part)=part else{return Err(invalid("noncanonical volume path"))};
            let name=part.to_str().ok_or_else(||invalid("volume path encoding"))?;
            dir=dir.directory(name,allowed)?;
        }
        Ok(dir)
    }
    fn directory(&self,name:&str,allowed:&[u32])->io::Result<Self>{
        let name=component(name)?;
        let fd=unsafe{libc::openat(self.0.as_raw_fd(),name.as_ptr(),libc::O_RDONLY|libc::O_DIRECTORY|libc::O_NOFOLLOW|libc::O_CLOEXEC)};
        if fd<0{return Err(io::Error::last_os_error())}
        let file=unsafe{File::from_raw_fd(fd)};
        let m=file.metadata()?;
        if !m.is_dir() || !allowed.contains(&m.uid()) || m.mode()&0o022!=0 {
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
    fn read_root(&self,name:&str)->io::Result<File>{
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
        self.0.sync_all()
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
fn freeze_ioctl(fd:i32,operation:libc::c_ulong)->io::Result<()>{
    if unsafe{libc::ioctl(fd,operation,0)}==0{return Ok(())}
    Err(io::Error::last_os_error())
}
#[derive(Serialize,Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Pending {protocol:String,name:String,mount_dev:u64,mount_ino:u64}
struct Frozen {dir:Dir,mount:File,name:String,_lock:File,finished:bool}
impl Frozen {
    fn begin(root:&Path,name:&str,required:bool)->io::Result<Option<Self>>{
        let grains=Dir::absolute(root,&[0])?;
        let vars=grains.directory("vars",&[0])?;
        let mount=vars.directory(name,&[0,root_volume_uid(root,name)?])?.0;
        if mount.metadata()?.dev()==vars.0.metadata()?.dev(){
            if required{return Err(invalid("registered volume is not a distinct mounted filesystem"))}
            return Ok(None)
        }
        let dir=grains.directory("broker",&[0])?.create_dir("freezes")?;
        let lock=dir.lock()?;
        recover_locked(root,&dir)?;
        let meta=mount.metadata()?;
        let pending=Pending{protocol:"mini-spk-freeze-pending-v1".into(),name:name.into(),
            mount_dev:meta.dev(),mount_ino:meta.ino()};
        let leaf=format!("{name}.json");
        let mut file=dir.create(&leaf)?;
        file.write_all(&serde_json::to_vec(&pending)?)?;file.sync_all()?;dir.0.sync_all()?;
        if let Err(error)=freeze_ioctl(mount.as_raw_fd(),FIFREEZE){
            // Known refusal did not acquire our freeze; never thaw another
            // caller's busy filesystem. Ambiguous errors keep the intent.
            if matches!(error.raw_os_error(),Some(libc::EBUSY)|Some(libc::EINVAL)){
                dir.unlink(&leaf)?;
            }
            return Err(error)
        }
        Ok(Some(Self{dir,mount,name:leaf,_lock:lock,finished:false}))
    }
    fn finish(mut self)->io::Result<()>{
        self.thaw()?;self.finished=true;Ok(())
    }
    fn thaw(&self)->io::Result<()>{
        clear_pending(&self.dir,&self.name,||freeze_ioctl(self.mount.as_raw_fd(),FITHAW))
    }
}
impl Drop for Frozen {
    fn drop(&mut self){
        if !self.finished{let _=self.thaw();} // SIGKILL retains intent for startup.
    }
}
// Called only after exact mount identity validation while holding freeze custody.
// An unsuccessful thaw never erases the durable repair obligation.
fn clear_pending(dir:&Dir,leaf:&str,thaw:impl FnOnce()->io::Result<()>)->io::Result<()>{
    match thaw(){
        Ok(())=>{},
        Err(e) if e.raw_os_error()==Some(libc::EINVAL)=>{},
        Err(e)=>return Err(e),
    }
    dir.unlink(leaf)
}
fn recover_locked(root:&Path,dir:&Dir)->io::Result<()>{
    let listing=PathBuf::from(format!("/proc/self/fd/{}",dir.0.as_raw_fd()));
    for entry in fs::read_dir(listing)?{
        let leaf=entry?.file_name().to_string_lossy().into_owned();
        if leaf==".freeze.lock"{continue}
        if !leaf.ends_with(".json"){return Err(invalid("unknown freeze custody artifact"))}
        let file=dir.read_root(&leaf)?;
        if file.metadata()?.len()>4096{return Err(invalid("freeze intent exceeds bound"))}
        let p:Pending=serde_json::from_reader(file)?;
        let (store,app)=p.name.split_once('-').ok_or_else(||invalid("freeze coordinate"))?;
        if p.protocol!="mini-spk-freeze-pending-v1" || !store_key(store) || !decimal(app)
            || leaf!=format!("{}.json",p.name){return Err(invalid("freeze intent coordinate refused"))}
        let grains=Dir::absolute(root,&[0])?;
        let mount=grains.directory("vars",&[0])?.directory(&p.name,&[0,root_volume_uid(root,&p.name)?])?.0;
        let m=mount.metadata()?;
        if m.dev()!=p.mount_dev || m.ino()!=p.mount_ino {
            return Err(invalid("pending freeze filesystem changed; no unrelated mount thawed"));
        }
        clear_pending(dir,&leaf,||freeze_ioctl(mount.as_raw_fd(),FITHAW))?;
    }
    Ok(())
}
pub(super) fn recover(root:&Path)->io::Result<()>{
    let grains=Dir::absolute(root,&[0])?;
    let dir=grains.directory("broker",&[0])?.create_dir("freezes")?;
    let _lock=dir.lock()?;
    recover_locked(root,&dir)
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
    let source_name=format!("{name}.ext4");
    let volumes=grains.directory("volumes",&[0])?;
    let mut source=volumes.read_root(&source_name)?;
    let stamp=SystemTime::now().duration_since(UNIX_EPOCH).map_err(|_|invalid("clock"))?.as_nanos();
    let leaf=format!("{app}-{stamp}.ext4");
    let mut out=exports.create(&leaf)?;
    let frozen=Frozen::begin(root,&name,true)?;
    let copied=(||->io::Result<String>{
        sparse_copy(&mut source,&mut out)?;out.sync_all()?;
        out.seek(SeekFrom::Start(0))?;file_sha256(&mut out)
    })();
    if let Some(guard)=frozen{guard.finish()?}
    let hash=copied?;
    exports.same_leaf(&leaf,&out)?;
    change_owner(&out,uid,gid)?;
    out.sync_all()?;exports.0.sync_all()?;
    exports.same_leaf(&leaf,&out)?;
    Ok(json!({"image":root.join(store).join("exports").join(leaf),"sha256":hash,
        "bytes":out.metadata()?.len().to_string()}))
}

pub(super) struct BackupTarget {dir:Dir}
pub(super) struct Copy {pub(super) file:File,pub(super) hash:String,pub(super) bytes:u64,pub(super) frozen_ms:u128}
impl BackupTarget {
    pub(super) fn create(path:&Path,operator:u32)->io::Result<Self>{
        let parent=Dir::absolute(path.parent().ok_or_else(||invalid("backup parent"))?,&[0,operator])?;
        let leaf=path.file_name().and_then(|n|n.to_str()).ok_or_else(||invalid("backup leaf"))?;
        let c=component(leaf)?;
        if unsafe{libc::mkdirat(parent.0.as_raw_fd(),c.as_ptr(),0o700)}!=0{return Err(io::Error::last_os_error())}
        let dir=parent.directory(leaf,&[0])?;
        dir.0.sync_all()?;parent.0.sync_all()?;
        Ok(Self{dir})
    }
    pub(super) fn copy_volume(&self,root:&Path,name:&str,active:bool)->io::Result<Copy>{
        let source_dir=Dir::absolute(root,&[0])?.directory("volumes",&[0])?;
        let leaf=format!("{name}.ext4");
        let mut source=source_dir.read_root(&leaf)?;
        let mut out=self.dir.create(&leaf)?;
        let started=std::time::Instant::now();
        let frozen=Frozen::begin(root,name,active)?;
        let copied=(||->io::Result<String>{
            sparse_copy(&mut source,&mut out)?;out.sync_all()?;
            source_dir.same_leaf(&leaf,&source)?;
            out.seek(SeekFrom::Start(0))?;file_sha256(&mut out)
        })();
        if let Some(guard)=frozen{guard.finish()?}
        let hash=copied?;
        self.dir.same_leaf(&leaf,&out)?;self.dir.0.sync_all()?;
        let conf=format!("{name}.conf");
        let mut source=source_dir.read_root(&conf)?;
        let mut destination=self.dir.create(&conf)?;
        io::copy(&mut source,&mut destination)?;
        destination.sync_all()?;self.dir.same_leaf(&conf,&destination)?;self.dir.0.sync_all()?;
        let bytes=out.metadata()?.len();
        Ok(Copy{file:out,hash,bytes,frozen_ms:started.elapsed().as_millis()})
    }
    pub(super) fn write_manifest(&self,value:&Value)->io::Result<()>{
        let mut file=self.dir.create("grains-backup.json")?;
        file.write_all(&serde_json::to_vec_pretty(value)?)?;file.sync_all()?;self.dir.0.sync_all()
    }
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
        pending.sync_all().unwrap();dir.0.sync_all().unwrap();
        assert!(clear_pending(&dir,"frozen.json",||Err(io::Error::from_raw_os_error(libc::EIO))).is_err());
        assert_eq!(fs::read(scratch.0.join("frozen.json")).unwrap(),b"exact retained filesystem");
        clear_pending(&dir,"frozen.json",||Ok(())).unwrap();
        assert!(!scratch.0.join("frozen.json").exists());
        let mut before_freeze=dir.create("before-freeze.json").unwrap();before_freeze.write_all(b"durable before ioctl").unwrap();
        before_freeze.sync_all().unwrap();dir.0.sync_all().unwrap();
        clear_pending(&dir,"before-freeze.json",||Err(io::Error::from_raw_os_error(libc::EINVAL))).unwrap();
        assert!(!scratch.0.join("before-freeze.json").exists());
    }
    #[test]
    fn volume_custody_live_capture_lock_refuses_competing_recovery(){
        let scratch=Scratch::new();let dir=scratch.dir();
        let held=dir.lock().unwrap();assert!(dir.lock().is_err());
        drop(held);assert!(dir.lock().is_ok());
    }

    fn physical_receiving_root()->PathBuf {
        assert_eq!(unsafe{libc::geteuid()},0,"explicit root disposable-filesystem receiver only");
        let root=PathBuf::from(std::env::var_os("MINI_VOLUME_CUSTODY_RECEIVING_ROOT").expect("explicit owned receiving root"));
        assert!(root.to_string_lossy().starts_with("/var/lib/mini-spk-custody-receiving-"));
        let dir=Dir::absolute(&root,&[0]).unwrap();assert_eq!(dir.0.metadata().unwrap().mode()&0o777,0o700);
        root
    }
    #[test]
    #[ignore = "explicit disposable root loop filesystem worker; only launched by receiving parent"]
    fn volume_custody_physical_freeze_worker(){
        let root=physical_receiving_root();assert_eq!(std::env::var("MINI_VOLUME_CUSTODY_WORKER").unwrap(),"yes");
        let _guard=Frozen::begin(&root,"1111111111111111-990010",true).unwrap().expect("actual mounted filesystem");
        let mut partial=OpenOptions::new().write(true).create_new(true).mode(0o600).open(root.join("partial-copy.ext4")).unwrap();
        partial.write_all(&vec![7u8;128*1024]).unwrap();partial.sync_all().unwrap();
        let mut ready=OpenOptions::new().write(true).create_new(true).mode(0o600).open(root.join("broker/worker-ready")).unwrap();
        ready.write_all(b"frozen and partial output durable").unwrap();ready.sync_all().unwrap();
        loop{std::thread::sleep(Duration::from_millis(100));}
    }
    #[test]
    #[ignore = "explicit root-only disposable loop filesystem; actual SIGKILL/freeze recovery qualification"]
    fn volume_custody_physical_process_death_reconciles_exact_mount(){
        let root=physical_receiving_root();recover(&root).unwrap();
        struct Worker {child:std::process::Child,root:PathBuf}
        impl Drop for Worker {fn drop(&mut self){let _=self.child.kill();let _=self.child.wait();let _=recover(&self.root);}}
        let child=Command::new(std::env::current_exe().unwrap())
            .args(["--exact","broker::volume_custody::tests::volume_custody_physical_freeze_worker","--ignored","--nocapture"])
            .env("MINI_VOLUME_CUSTODY_WORKER","yes").env("MINI_VOLUME_CUSTODY_RECEIVING_ROOT",&root).spawn().unwrap();
        let mut worker=Worker{child,root:root.clone()};
        let ready=root.join("broker/worker-ready");let deadline=std::time::Instant::now()+Duration::from_secs(5);
        while !ready.exists(){
            assert!(worker.child.try_wait().unwrap().is_none(),"freeze worker exited before ready");
            assert!(std::time::Instant::now()<deadline,"bounded freeze worker readiness");
            std::thread::sleep(Duration::from_millis(10));
        }
        let intent=root.join("broker/freezes/1111111111111111-990010.json");assert!(intent.is_file());
        worker.child.kill().unwrap();let status=worker.child.wait().unwrap();
        use std::os::unix::process::ExitStatusExt;assert_eq!(status.signal(),Some(libc::SIGKILL));
        assert!(intent.is_file(),"SIGKILL must retain durable freeze obligation");
        assert!(!root.join("grains-backup.json").exists(),"partial output is not a completed backup");
        recover(&root).unwrap();assert!(!intent.exists());
        let status=Command::new("/usr/bin/timeout").args(["3","/usr/bin/touch"])
            .arg(root.join("vars/1111111111111111-990010/after-recovery")).status().unwrap();
        assert!(status.success(),"actual filesystem remained frozen after recovery");
        assert_eq!(fs::metadata(root.join("partial-copy.ext4")).unwrap().len(),128*1024);
    }

}
