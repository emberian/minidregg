//! Rename is the journal commit point. Abandoned staging files are retained
//! evidence, never promoted or deleted; each save uses a fresh exclusive name.
use std::ffi::CString;
use std::fs::{File,OpenOptions};
use std::io::{self,Read,Write};
use std::os::fd::{AsRawFd,FromRawFd};
use std::os::unix::fs::{MetadataExt,OpenOptionsExt};
use std::path::Path;
fn refused(s:&str)->io::Error {io::Error::new(io::ErrorKind::InvalidInput,s)}
fn component(s:&str)->io::Result<CString>{
    if s.is_empty() || matches!(s,"."|"..") || s.contains('/') {return Err(refused("journal leaf invalid"))}
    CString::new(s).map_err(|_|refused("journal leaf contains NUL"))
}
fn stat_leaf(dir:&File,name:&CString)->io::Result<Option<libc::stat>>{
    let mut st=unsafe{std::mem::zeroed::<libc::stat>()};
    if unsafe{libc::fstatat(dir.as_raw_fd(),name.as_ptr(),&mut st,libc::AT_SYMLINK_NOFOLLOW)}!=0{
        let e=io::Error::last_os_error();if e.kind()==io::ErrorKind::NotFound{return Ok(None)}return Err(e)
    }Ok(Some(st))
}
pub(crate) fn write(path:&Path,bytes:&[u8])->io::Result<()>{write_before_publish(path,bytes,||Ok(()))}
fn write_before_publish(path:&Path,bytes:&[u8],before:impl FnOnce()->io::Result<()>)->io::Result<()>{
    let parent=path.parent().ok_or_else(||refused("journal parent absent"))?;
    let dir=OpenOptions::new().read(true).custom_flags(libc::O_DIRECTORY|libc::O_NOFOLLOW|libc::O_CLOEXEC).open(parent)?;
    let m=dir.metadata()?;let uid=unsafe{libc::geteuid()};
    if !m.is_dir() || m.uid()!=uid || m.mode()&0o022!=0{return Err(refused("journal parent custody differs"))}
    let leaf=path.file_name().and_then(|x|x.to_str()).ok_or_else(||refused("journal filename invalid"))?;
    let name=component(leaf)?;
    if let Some(st)=stat_leaf(&dir,&name)?{
        if st.st_mode&libc::S_IFMT!=libc::S_IFREG || st.st_uid!=uid || st.st_nlink!=1 || st.st_mode&0o077!=0{
            return Err(refused("committed journal custody differs"))
        }
    }
    let mut entropy=File::open("/dev/urandom")?;
    let (stage,mut file)=loop{
        let mut nonce=[0u8;16];entropy.read_exact(&mut nonce)?;
        let text=nonce.iter().map(|b|format!("{b:02x}")).collect::<String>();
        let stage=component(&format!(".{leaf}.stage-{text}"))?;
        let fd=unsafe{libc::openat(dir.as_raw_fd(),stage.as_ptr(),libc::O_WRONLY|libc::O_CREAT|libc::O_EXCL|libc::O_NOFOLLOW|libc::O_CLOEXEC,0o600)};
        if fd>=0{break(stage,unsafe{File::from_raw_fd(fd)})}
        let e=io::Error::last_os_error();if e.kind()!=io::ErrorKind::AlreadyExists{return Err(e)}
    };
    file.write_all(bytes)?;file.sync_all()?;
    before()?;
    let identity=file.metadata()?;
    let st=stat_leaf(&dir,&stage)?.ok_or_else(||refused("journal stage disappeared"))?;
    if st.st_dev!=identity.dev() || st.st_ino!=identity.ino() || st.st_nlink!=1 || st.st_uid!=uid || st.st_mode&libc::S_IFMT!=libc::S_IFREG {
        return Err(refused("journal stage switched; retained bytes not published"))
    }
    if unsafe{libc::renameat(dir.as_raw_fd(),stage.as_ptr(),dir.as_raw_fd(),name.as_ptr())}!=0{return Err(io::Error::last_os_error())}
    dir.sync_all()
}
#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;
    struct Scratch(std::path::PathBuf);
    impl Scratch{fn new()->Self{
        let p=std::env::temp_dir().join(format!("mini-journal-{}-{}",std::process::id(),std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
        fs::create_dir(&p).unwrap();fs::set_permissions(&p,fs::Permissions::from_mode(0o700)).unwrap();Self(p)
    }}
    impl Drop for Scratch{fn drop(&mut self){let _=fs::remove_dir_all(&self.0);}}
    #[test]
    fn journal_orphan_temp_is_preserved_and_never_promoted(){
        let s=Scratch::new();let p=s.0.join("journal.json");write(&p,b"committed").unwrap();
        fs::write(p.with_extension("tmp"),b"foreign or abandoned").unwrap();
        assert!(write_before_publish(&p,b"uncommitted",||Err(io::Error::from(io::ErrorKind::Interrupted))).is_err());
        assert_eq!(fs::read(&p).unwrap(),b"committed");
        write(&p,b"new committed").unwrap();assert_eq!(fs::read(&p).unwrap(),b"new committed");
        assert_eq!(fs::read(p.with_extension("tmp")).unwrap(),b"foreign or abandoned");
        let stage=fs::read_dir(&s.0).unwrap().filter_map(|e|{let e=e.unwrap();e.file_name().to_str().unwrap().starts_with(".journal.json.stage-").then_some(e.path())}).collect::<Vec<_>>();
        assert_eq!(stage.len(),1);assert_eq!(fs::read(&stage[0]).unwrap(),b"uncommitted");
    }
    #[test]
    fn journal_foreign_symlink_and_hardlink_refuse_without_changes(){
        let s=Scratch::new();let p=s.0.join("journal.json");let victim=s.0.join("victim");
        fs::write(&victim,b"never overwrite").unwrap();fs::set_permissions(&victim,fs::Permissions::from_mode(0o600)).unwrap();
        std::os::unix::fs::symlink(&victim,&p).unwrap();assert!(write(&p,b"bad").is_err());assert_eq!(fs::read(&victim).unwrap(),b"never overwrite");
        fs::remove_file(&p).unwrap();fs::hard_link(&victim,&p).unwrap();assert!(write(&p,b"bad").is_err());assert_eq!(fs::read(&victim).unwrap(),b"never overwrite");
    }
    #[test]
    #[ignore="private worker used only by bounded process-death test"]
    fn journal_process_death_worker(){
        let root=std::path::PathBuf::from(std::env::var_os("MINI_JOURNAL_RECEIVING_ROOT").expect("explicit worker root"));
        write_before_publish(&root.join("journal.json"),b"uncommitted-before-rename",||{
            fs::write(root.join("ready"),b"durable stage").unwrap();
            loop{std::thread::sleep(std::time::Duration::from_millis(10));}
        }).unwrap();
    }
    #[test]
    fn journal_actual_process_death_before_rename_recovers_committed_cut(){
        let s=Scratch::new();let p=s.0.join("journal.json");write(&p,b"committed-old").unwrap();
        struct Worker(std::process::Child);impl Drop for Worker{fn drop(&mut self){let _=self.0.kill();let _=self.0.wait();}}
        let child=std::process::Command::new(std::env::current_exe().unwrap()).args(["--exact","journal_io::tests::journal_process_death_worker","--ignored","--nocapture"])
            .env("MINI_JOURNAL_RECEIVING_ROOT",&s.0).spawn().unwrap();let mut worker=Worker(child);
        let deadline=std::time::Instant::now()+std::time::Duration::from_secs(5);
        while !s.0.join("ready").exists(){assert!(worker.0.try_wait().unwrap().is_none());assert!(std::time::Instant::now()<deadline);std::thread::sleep(std::time::Duration::from_millis(10));}
        worker.0.kill().unwrap();let status=worker.0.wait().unwrap();
        use std::os::unix::process::ExitStatusExt;assert_eq!(status.signal(),Some(libc::SIGKILL));
        assert_eq!(fs::read(&p).unwrap(),b"committed-old");write(&p,b"next-committed").unwrap();assert_eq!(fs::read(&p).unwrap(),b"next-committed");
        let stage=fs::read_dir(&s.0).unwrap().filter_map(|e|{let e=e.unwrap();e.file_name().to_str().unwrap().starts_with(".journal.json.stage-").then_some(e.path())}).collect::<Vec<_>>();
        assert_eq!(stage.len(),1);assert_eq!(fs::read(&stage[0]).unwrap(),b"uncommitted-before-rename");
    }
}
