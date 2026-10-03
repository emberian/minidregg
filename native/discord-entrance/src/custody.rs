//! Private durable transport custody. A started arbitrary command is never replayed.
//! This records physical execution; Mini's own operation records decide semantic outcomes.
use std::fs::{self, File, OpenOptions};
use std::io::{Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{DirBuilderExt, MetadataExt, OpenOptionsExt};
use std::path::{Path, PathBuf};
use serde_json::Value;

pub fn private_dir(path: &Path) -> Result<(), String> {
    match fs::DirBuilder::new().mode(0o700).create(path) {
        Ok(()) => {},
        Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => {},
        Err(e) => return Err(e.to_string()),
    }
    let m = fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    if !m.is_dir() || m.mode() & 0o077 != 0 || m.uid() != unsafe {libc::geteuid()} {
        return Err(format!("{} must be an owner-private directory", path.display()));
    }
    Ok(())
}

/// Caller holds the corresponding lease. Sync both file contents and rename directory.
pub fn atomic_json(path: &Path, value: &Value) -> Result<(), String> {
    let tmp = path.with_extension("pending");
    let mut f = OpenOptions::new().write(true).create(true).truncate(true).mode(0o600)
        .custom_flags(libc::O_NOFOLLOW).open(&tmp).map_err(|e| e.to_string())?;
    f.write_all(&serde_json::to_vec(value).map_err(|e| e.to_string())?).map_err(|e| e.to_string())?;
    f.sync_all().map_err(|e| e.to_string())?;
    fs::rename(&tmp,path).map_err(|e| e.to_string())?;
    File::open(path.parent().ok_or("record has no parent")?).and_then(|f|f.sync_all()).map_err(|e|e.to_string())
}

pub fn read_json(path: &Path) -> Result<Option<Value>, String> {
    let f = match OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW).open(path) {
        Ok(f) => f,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e.to_string()),
    };
    let meta=f.metadata().map_err(|e|e.to_string())?;
    if !meta.is_file() || meta.len()>16*1024*1024 {return Err("invalid or oversized custody record".into());}
    let mut bytes=Vec::new(); f.take(16*1024*1024+1).read_to_end(&mut bytes).map_err(|e|e.to_string())?;
    serde_json::from_slice(&bytes).map(Some).map_err(|e|format!("corrupt custody record: {e}"))
}

pub struct Record { pub path: PathBuf, pub value: Option<Value>, _lease: File }
impl Record {
    /// None means another worker holds this record; no duplicate work may start.
    pub fn lock(root:&Path,key:&str)->Result<Option<Self>,String>{
        if key.is_empty() || !key.bytes().all(|b|b.is_ascii_alphanumeric() || b==b'-') {return Err("invalid custody key".into());}
        private_dir(root)?;
        let f=OpenOptions::new().read(true).write(true).create(true).truncate(false).mode(0o600)
            .custom_flags(libc::O_NOFOLLOW).open(root.join(format!("{key}.lock"))).map_err(|e|e.to_string())?;
        if unsafe {libc::flock(f.as_raw_fd(),libc::LOCK_EX|libc::LOCK_NB)}!=0 {
            let e=std::io::Error::last_os_error();
            if e.kind()==std::io::ErrorKind::WouldBlock {return Ok(None)}
            return Err(e.to_string());
        }
        let path=root.join(format!("{key}.json"));
        Ok(Some(Self{value:read_json(&path)?,path,_lease:f}))
    }
    pub fn save(&mut self,value:Value)->Result<(),String>{atomic_json(&self.path,&value)?;self.value=Some(value);Ok(())}
}

#[cfg(test)] mod tests {
    use super::*;
    #[test] fn locks_survive_reopen_and_corruption_is_not_absence(){
        let root=std::env::temp_dir().join(format!("discord-custody-{}",std::process::id()));
        let mut a=Record::lock(&root,"one").unwrap().unwrap();
        a.save(serde_json::json!({"phase":"started"})).unwrap();
        assert!(Record::lock(&root,"one").unwrap().is_none());drop(a);
        let a=Record::lock(&root,"one").unwrap().unwrap();assert_eq!(a.value.unwrap()["phase"],"started");
        fs::write(root.join("two.json"),b"{").unwrap();assert!(Record::lock(&root,"two").is_err());
        fs::remove_dir_all(root).unwrap();
    }
}
