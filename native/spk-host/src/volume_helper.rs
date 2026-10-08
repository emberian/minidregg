//! One-shot privileged volume boundary. Only a root-installed registry selects
//! paths, identities and quotas; caller-supplied paths must match it exactly.
use crate::broker::{decimal, store_key, volume_name};
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::fs::{self, File, OpenOptions};
use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::os::unix::fs::{MetadataExt, OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use sha2::{Digest, Sha256};
use minidregg_compatible_upgrade_custody as custody;
const REGISTRY: &str = "/etc/mini-spk-volumes";
fn refuse(message: &str) -> io::Error { io::Error::new(io::ErrorKind::PermissionDenied, message) }
fn hex(value: &str) -> bool { value.len()==64 && value.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) }
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub(crate) struct Registry {
    pub protocol: String,
    pub store: String,
    pub deployment_id: String,
    pub host_id: String,
    pub grains_root: PathBuf,
    pub operator_uid: u32,
    pub operator_gid: u32,
    pub app_uids: Vec<u32>,
    pub helper: PathBuf,
    pub helper_sha256: String,
}
impl Registry {
    pub(crate) fn load(store: &str) -> io::Result<Self> {
        if !store_key(store) { return Err(refuse("volume-helper: store id refused")); }
        let path=Path::new(REGISTRY).join(format!("{store}.json"));
        custody::root_ancestors(&path)?;
        let file=OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW|libc::O_CLOEXEC).open(&path)?;
        let meta=file.metadata()?;
        if !meta.is_file() || meta.uid()!=0 || meta.nlink()!=1 || meta.mode()&0o7777!=0o644 || meta.len()>65536 {
            return Err(refuse("volume-helper: root registry custody refused"));
        }
        let result: Self=serde_json::from_reader(file.take(65537))?;
        if result.protocol!="mini-spk-volume-registry-v1" || result.store!=store
            || !hex(&result.deployment_id) || !hex(&result.host_id)
            || result.operator_uid==0 || result.operator_gid==0 || result.app_uids.is_empty()
            || result.app_uids.iter().any(|u| *u<65536 || *u==result.operator_uid)
            || result.app_uids.iter().collect::<std::collections::BTreeSet<_>>().len()!=result.app_uids.len()
            || result.grains_root!=Path::new("/var/lib/mini-spk-worlds").join(store)
        { return Err(refuse("volume-helper: registry shape refused")); }
        custody::root_ancestors(&result.grains_root)?;
        let root=fs::symlink_metadata(&result.grains_root)?;
        if !root.is_dir() || root.uid()!=0 || root.mode()&0o7777!=0o755 {
            return Err(refuse("volume-helper: world root custody refused"));
        }
        custody::root_pin(&result.helper,&result.helper_sha256)?;
        Ok(result)
    }
    fn coordinates(&self, request: &Request) -> io::Result<()> {
        if request.store!=self.store || request.deployment_id!=self.deployment_id || !decimal(&request.grain)
            || request.volume_path!=self.grains_root.join("vars").join(volume_name(&self.store,&request.grain))
        { return Err(refuse("volume-helper: cross-world-volume-path refused")); }
        if !self.app_uids.contains(&request.app_uid) {
            return Err(refuse("volume-helper: namespace app uid outside registered world range"));
        }
        if !hex(&request.volume_id) || !(64..=16384).contains(&request.size_mib) {
            return Err(refuse("volume-helper: volume identity or quota refused"));
        }
        Ok(())
    }
    fn status_coordinates(&self, request: &StatusRequest) -> io::Result<()> {
        if request.store != self.store || request.deployment_id != self.deployment_id
            || request.volumes_root != self.grains_root.join("volumes")
        { return Err(refuse("volume-helper: cross-world-volume-path refused")); }
        Ok(())
    }
}
#[derive(Clone, Copy, Debug, Deserialize, Serialize)]
#[serde(rename_all="kebab-case")]
pub enum Verb { Create, Mount, Unmount, Freeze, Thaw, Destroy }
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub struct Request {
    pub verb: Verb,
    pub store: String,
    pub deployment_id: String,
    pub grain: String,
    pub volume_path: PathBuf,
    pub app_uid: u32,
    pub size_mib: u64,
    pub volume_id: String,
    #[serde(default)]
    pub import_sha256: Option<String>,
}
#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all="kebab-case")]
enum StatusVerb { VolumesStatus }
#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
struct StatusRequest {
    verb: StatusVerb,
    store: String,
    deployment_id: String,
    volumes_root: PathBuf,
}
#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
pub(crate) struct VolumeStatus {
    pub request: Request,
    pub settled: bool,
    pub paused: bool,
    pub mounted: bool,
}
#[derive(Debug, Deserialize, Serialize)]
#[serde(rename_all="camelCase", deny_unknown_fields)]
struct Status {
    protocol: String,
    store: String,
    volumes_root: PathBuf,
    volumes: Vec<VolumeStatus>,
}

fn authenticate_root(registry: &Registry) -> io::Result<u32> {
    if unsafe{libc::geteuid()}!=0 || std::env::current_exe()?!=registry.helper {
        return Err(refuse("volume-helper: root installed helper required"));
    }
    let caller=std::env::var("SUDO_UID").ok().and_then(|u|u.parse::<u32>().ok())
        .ok_or_else(||refuse("volume-helper: authenticated sudo caller absent"))?;
    if caller!=registry.operator_uid { return Err(refuse("volume-helper: caller uid differs from registered operator")); }
    Ok(caller)
}
fn verb_lock(registry: &Registry, read_only: bool) -> io::Result<File> {
    let path=registry.grains_root.join("volume-custody/verbs.lock");
    let file=OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW|libc::O_CLOEXEC).open(path)?;
    let meta=file.metadata()?;
    if !meta.is_file() || meta.uid()!=0 || meta.nlink()!=1 || meta.permissions().mode()&0o7777!=0o600 { return Err(refuse("volume-helper: verb lock custody refused")); }
    if unsafe{libc::flock(file.as_raw_fd(),(if read_only {libc::LOCK_SH}else{libc::LOCK_EX})|libc::LOCK_NB)}!=0 {
        return Err(refuse("volume-helper: another store volume verb is active"));
    }
    Ok(file)
}
fn paused(registry: &Registry, request: &Request) -> io::Result<bool> {
    let read=|parts: &[&str]| crate::broker::volume_pause_bytes(&registry.grains_root,&request.store,&request.grain,parts,registry.operator_uid);
    let bytes=match read(&["checkpoint-pause.json"]) {
        Ok(bytes)=>bytes,
        Err(e) if e.kind()==io::ErrorKind::NotFound=>return Ok(false),
        Err(e)=>return Err(e),
    };
    let intent:crate::checkpoint_control::Intent=serde_json::from_slice(&bytes)?;
    let r=&intent.request;let b=&r.binding;
    let gen=format!("g{}",b.generation);
    let journal=registry.grains_root.join(&request.store).join("host/apps").join(&request.grain).join(&gen);
    if r.protocol!="mini-spk-checkpoint-control-v1" || r.action!="pause" || !hex(&r.nonce_hex)
        || b.app!=request.grain || !decimal(&b.generation) || b.journal_dir!=journal || b.resident_config!=journal.join("resident.json")
    { return Err(refuse("volume-helper: retained pause coordinates refused")); }
    let receipt=format!("checkpoint-{}-pause.json",r.nonce_hex);
    let retained=match read(&[&gen,&receipt]) {Ok(bytes)=>bytes,Err(e) if e.kind()==io::ErrorKind::NotFound=>return Ok(false),Err(e)=>return Err(e)};
    if retained!=bytes {return Ok(false)}
    let record_bytes=read(&[&gen,"record.json"])?;
    let record:crate::hostd::Record=serde_json::from_slice(&record_bytes)?;
    let resident_bytes=read(&[&gen,"resident.json"])?;
    let resident:Value=serde_json::from_slice(&resident_bytes)?;
    Ok(record.phase==crate::hostd::Phase::Running && record.app().to_string()==request.grain
        && record.generation().to_string()==b.generation
        && format!("{:x}",Sha256::digest(&record_bytes))==intent.journal_sha256
        && format!("{:x}",Sha256::digest(&resident_bytes))==b.resident_config_sha256
        && resident["miniConfigSha256"]==b.mini_config_sha256 && resident["store"]==request.store
        && resident["unit"]==crate::broker::resident_unit(&request.store,&request.grain,&b.generation)?
        && resident["grainsRoot"]==registry.grains_root.to_string_lossy().as_ref())
}
fn root_volume_status(registry: &Registry) -> io::Result<Vec<VolumeStatus>> {
    let dir=registry.grains_root.join("volumes");
    let meta=fs::symlink_metadata(&dir)?;
    if !meta.is_dir() || meta.uid()!=0 || meta.mode()&0o7777!=0o700 { return Err(refuse("volume-helper: volume registry directory custody refused")); }
    let mut volumes=Vec::new();
    for entry in fs::read_dir(&dir)? {
        let entry=entry?;
        let name=entry.file_name().into_string().map_err(|_|refuse("volume-helper: registration name encoding"))?;
        let Some(name)=name.strip_suffix(".conf") else {continue};
        let (store,grain)=name.split_once('-').ok_or_else(||refuse("volume-helper: registration name refused"))?;
        if store!=registry.store || !decimal(grain) {return Err(refuse("volume-helper: cross-world-volume-path refused"))}
        let f=OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW|libc::O_CLOEXEC).open(entry.path())?;
        let meta=f.metadata()?;
        if !meta.is_file() || meta.uid()!=0 || meta.nlink()!=1 || meta.mode()&0o7777!=0o600 || meta.len()>4096 {return Err(refuse("volume-helper: registration custody refused"))}
        let mut text=String::new();f.take(4097).read_to_string(&mut text)?;
        let field=|key:&str| text.lines().find_map(|line|line.strip_prefix(key)).ok_or_else(||refuse("volume-helper: registration field absent"));
        let request=Request {verb:Verb::Mount,store:store.to_owned(),deployment_id:field("deployment_id=")?.to_owned(),grain:grain.to_owned(),
            volume_path:registry.grains_root.join("vars").join(name),app_uid:field("app_uid=")?.parse().map_err(|_|refuse("volume-helper: registration uid refused"))?,
            size_mib:field("size_mib=")?.parse().map_err(|_|refuse("volume-helper: registration quota refused"))?,volume_id:field("volume_id=")?.to_owned(),import_sha256:None};
        registry.coordinates(&request)?;registration(registry,&request)?;
        let pending=registry.grains_root.join("volume-custody/freezes").join(format!("{name}.json"));
        let settled=match fs::symlink_metadata(pending) {Ok(meta)=>{if !meta.is_file() || meta.uid()!=0 || meta.nlink()!=1 || meta.mode()&0o7777!=0o600 {return Err(refuse("volume-helper: freeze obligation custody refused"))}false},Err(e) if e.kind()==io::ErrorKind::NotFound=>true,Err(e)=>return Err(e)};
        let mounted=Command::new("/usr/bin/findmnt").args(["-n","-M"]).arg(&request.volume_path).env_clear().output()?.status.success();
        let paused=paused(registry,&request)?;
        volumes.push(VolumeStatus {request,settled,paused,mounted});
        if volumes.len()>registry.app_uids.len() {return Err(refuse("volume-helper: volume inventory bound"))}
    }
    volumes.sort_by(|a,b|a.request.grain.cmp(&b.request.grain));
    Ok(volumes)
}
fn execute_status(bytes: &[u8]) -> io::Result<Value> {
    let request:StatusRequest=serde_json::from_slice(bytes)?;
    eprintln!("volume-helper verb=VolumesStatus caller_uid={} store={} path={}",std::env::var("SUDO_UID").unwrap_or_else(|_|"absent".into()),request.store,request.volumes_root.display());
    let registry=Registry::load(&request.store)?;
    registry.status_coordinates(&request)?;
    authenticate_root(&registry)?;
    let _lock=verb_lock(&registry,true)?;
    Ok(serde_json::to_value(Status {protocol:"mini-spk-volumes-status-v1".into(),store:registry.store.clone(),volumes_root:request.volumes_root,volumes:root_volume_status(&registry)?})?)
}
fn run(program: &str, args: &[&str]) -> io::Result<String> {
    let output=Command::new(program).args(args).env_clear().env("PATH","/usr/sbin:/usr/bin:/sbin:/bin")
        .stdin(Stdio::null()).output()?;
    if !output.status.success() { return Err(io::Error::other(format!("volume-helper: {}: {}",program,String::from_utf8_lossy(&output.stderr)))); }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_owned())
}
fn script(registry: &Registry, request: &Request, action: &str, import: Option<&Path>) -> io::Result<()> {
    let mut args=vec!["--root".to_owned(),registry.grains_root.display().to_string(),action.to_owned(),request.store.clone(),request.grain.clone()];
    if action!="attest" { args.extend([request.app_uid.to_string(),request.size_mib.to_string()]); }
    if matches!(action,"create"|"create-from") { args.push(request.volume_id.clone()); }
    if let Some(path)=import { args.push(path.display().to_string()); }
    let output=Command::new("/bin/bash").arg("-c").arg(include_str!("../../../deploy/spk-host/spk-var-volume"))
        .arg("mini-spk-volume-helper").args(args).env_clear().env("PATH","/usr/sbin:/usr/bin:/sbin:/bin")
        .stdin(Stdio::null()).output()?;
    if !output.status.success() { return Err(io::Error::other(format!("volume-helper: volume {} refused: {}",action,String::from_utf8_lossy(&output.stderr)))); }
    Ok(())
}
fn registration(registry: &Registry, request: &Request) -> io::Result<()> {
    let path=registry.grains_root.join("volumes").join(format!("{}.conf",volume_name(&request.store,&request.grain)));
    let f=OpenOptions::new().read(true).custom_flags(libc::O_NOFOLLOW|libc::O_CLOEXEC).open(path)?;
    let m=f.metadata()?;
    if !m.is_file() || m.uid()!=0 || m.nlink()!=1 || m.mode()&0o7777!=0o600 || m.len()>4096 { return Err(refuse("volume-helper: registration custody refused")); }
    let mut text=String::new();f.take(4097).read_to_string(&mut text)?;
    let expected=format!("app_uid={}\nsize_mib={}\ndeployment_id={}\nhost_id={}\nvolume_id={}\n",request.app_uid,request.size_mib,registry.deployment_id,registry.host_id,request.volume_id);
    if text!=expected { return Err(refuse("volume-helper: exact registration differs from request")); }
    Ok(())
}
fn mount_registered(registry: &Registry, request: &Request) -> io::Result<()> {
    registration(registry, request)?;
    // Never use an arbitrary path or backing image supplied by the operator.
    let probe=Command::new("/usr/bin/findmnt").args(["-n","-M"]).arg(&request.volume_path).env_clear().output()?;
    if !probe.status.success() {
        let image=registry.grains_root.join("volumes").join(format!("{}.ext4",volume_name(&request.store,&request.grain)));
        let meta=fs::symlink_metadata(&image)?;
        if !meta.is_file() || meta.uid()!=0 || meta.nlink()!=1 || meta.mode()&0o7777!=0o600 || meta.len()!=request.size_mib*1024*1024 { return Err(refuse("volume-helper: backing image custody refused")); }
        run("/usr/bin/mount",&["-t","ext4","-o","loop,nosuid,nodev,noatime",image.to_str().ok_or_else(||refuse("image encoding"))?,request.volume_path.to_str().ok_or_else(||refuse("volume encoding"))?])?;
    }
    script(registry,request,"verify",None)?;
    script(registry,request,"attest",None)
}
pub fn execute(bytes: &[u8]) -> io::Result<Value> {
    if bytes.len()>16384 { return Err(refuse("volume-helper: request bound")); }
    let selector:Value=serde_json::from_slice(bytes)?;
    if selector["verb"]=="volumes-status" { return execute_status(bytes); }
    let request: Request=serde_json::from_slice(bytes)?;
    // Check the path before checking euid, so the committed cross-world plant
    // can exercise the same receiving function without privilege.
    let logging_uid=if unsafe{libc::geteuid()}==0 { std::env::var("SUDO_UID").unwrap_or_else(|_|"absent".into()) } else {unsafe{libc::geteuid()}.to_string()};
    eprintln!("volume-helper verb={:?} caller_uid={} store={} grain={} path={}",request.verb,logging_uid,request.store,request.grain,request.volume_path.display());
    let registry=Registry::load(&request.store)?;
    registry.coordinates(&request)?;
    let caller=authenticate_root(&registry)?;
    let _lock=verb_lock(&registry,false)?;
    let root=&registry.grains_root;
    let name=volume_name(&request.store,&request.grain);
    crate::broker::volume_recover(root)?;
    match request.verb {
        Verb::Create => {
            let config=root.join("volumes").join(format!("{name}.conf"));
            if fs::symlink_metadata(&config).is_ok() {
                mount_registered(&registry,&request)?;
                return Ok(json!({"store":request.store,"grain":request.grain,"verb":request.verb,"volumePath":request.volume_path}));
            }
            let import=if let Some(sha)=&request.import_sha256 {
                if !hex(sha) { return Err(refuse("volume-helper: import digest refused")); }
                let mut source=crate::broker::volume_import(root,&request.store,sha,caller)?;
                if source.metadata()?.len()!=request.size_mib*1024*1024 { return Err(refuse("volume-helper: import size refused")); }
                let target=root.join("volumes").join(format!(".import-{name}"));
                let mut out=OpenOptions::new().write(true).create_new(true).mode(0o600).open(&target)?;
                io::copy(&mut source,&mut out)?;out.sync_all()?;
                let mut input=File::open(&target)?;
                let mut hash=Sha256::new();
                let mut buffer=[0u8;65536];
                loop { let n=input.read(&mut buffer)?;if n==0 {break} hash.update(&buffer[..n]); }
                if format!("{:x}",hash.finalize())!=*sha { fs::remove_file(&target)?;return Err(refuse("volume-helper: exact import digest differs")); }
                Some(target)
            } else { None };
            script(&registry,&request,if import.is_some(){"create-from"}else{"create"},import.as_deref())?;
            script(&registry,&request,"attest",None)?;
        }
        Verb::Mount => {
            mount_registered(&registry,&request)?;
        }
        Verb::Unmount => {
            registration(&registry,&request)?;
            crate::broker::volume_recover(root)?;
            script(&registry,&request,"verify",None)?;
            run("/usr/bin/umount",&[request.volume_path.to_str().ok_or_else(||refuse("volume encoding"))?])?;
        }
        Verb::Freeze => {
            registration(&registry,&request)?;
            script(&registry,&request,"verify",None)?;
            // Freeze/copy/thaw is one custody transaction. A lost exec reply
            // never licenses resubmitting an export; retain the exact artifact.
            return crate::broker::volume_export(root,&request.store,&request.grain,caller,registry.operator_gid);
        }
        Verb::Thaw => { registration(&registry,&request)?;crate::broker::volume_recover(root)?; }
        Verb::Destroy => {
            registration(&registry,&request)?;
            let mounted=Command::new("/usr/bin/findmnt").args(["-n","-M"]).arg(&request.volume_path).env_clear().output()?;
            if mounted.status.success() { return Err(refuse("volume-helper: destroy requires unmounted volume")); }
            let image=root.join("volumes").join(format!("{name}.ext4"));
            if !run("/usr/sbin/losetup",&["-j",image.to_str().ok_or_else(||refuse("image encoding"))?])?.is_empty() { return Err(refuse("volume-helper: destroy refuses attached loop")); }
            fs::remove_file(image)?;
            fs::remove_file(root.join("volumes").join(format!("{name}.conf")))?;
            fs::remove_file(root.join("attest").join(format!("{name}.witness")))?;
            fs::remove_dir(&request.volume_path)?;
        }
    }
    Ok(json!({"store":request.store,"grain":request.grain,"verb":request.verb,"volumePath":request.volume_path}))
}
pub(crate) fn call(helper: &Path, request: &Request) -> io::Result<Value> {
    let r=Registry::load(&request.store)?;
    r.coordinates(request)?;
    if helper!=r.helper || unsafe{libc::geteuid()}!=r.operator_uid { return Err(refuse("volume-helper: selected helper or operator differs")); }
    invoke(helper,&serde_json::to_string(request)?)
}
fn invoke(helper:&Path,payload:&str) -> io::Result<Value> {
    let output=Command::new("/usr/bin/sudo").args(["-n","--"]).arg(helper).arg(payload).env_clear()
        .env("PATH","/usr/sbin:/usr/bin:/sbin:/bin").stdin(Stdio::null()).output()?;
    eprint!("{}",String::from_utf8_lossy(&output.stderr));
    if !output.status.success() { return Err(io::Error::other(format!("volume-helper exec refused or uncertain: {}",String::from_utf8_lossy(&output.stderr)))); }
    Ok(serde_json::from_slice(&output.stdout)?)
}
pub(crate) fn volumes_status(helper:&Path,store:&str) -> io::Result<Vec<VolumeStatus>> {
    let registry=Registry::load(store)?;
    if helper!=registry.helper || unsafe{libc::geteuid()}!=registry.operator_uid {return Err(refuse("volume-helper: selected helper or operator differs"))}
    let request=StatusRequest {verb:StatusVerb::VolumesStatus,store:store.to_owned(),deployment_id:registry.deployment_id.clone(),volumes_root:registry.grains_root.join("volumes")};
    let status:Status=serde_json::from_value(invoke(helper,&serde_json::to_string(&request)?)?)?;
    if status.protocol!="mini-spk-volumes-status-v1" || status.store!=store || status.volumes_root!=request.volumes_root || status.volumes.len()>registry.app_uids.len() {return Err(refuse("volume-helper: inventory reply coordinates refused"))}
    for volume in &status.volumes {registry.coordinates(&volume.request)?;}
    Ok(status.volumes)
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn tenancy_helper_cross_world_path_refuses() {
        let r=Registry { protocol:"mini-spk-volume-registry-v1".into(),store:"0123456789abcdef".into(),deployment_id:"a".repeat(64),host_id:"b".repeat(64),grains_root:"/var/lib/mini-spk-worlds/0123456789abcdef".into(),operator_uid:1001,operator_gid:1001,app_uids:vec![165536],helper:"/usr/local/libexec/mini-spk-volume-helper".into(),helper_sha256:"c".repeat(64) };
        let mut q=Request {verb:Verb::Mount,store:r.store.clone(),deployment_id:r.deployment_id.clone(),grain:"9101".into(),volume_path:r.grains_root.join("vars/0123456789abcdef-9101"),app_uid:165536,size_mib:512,volume_id:"d".repeat(64),import_sha256:None};
        assert!(r.coordinates(&q).is_ok());
        q.volume_path="/var/lib/mini-spk-worlds/fedcba9876543210/vars/fedcba9876543210-9101".into();
        assert_eq!(r.coordinates(&q).unwrap_err().to_string(),"volume-helper: cross-world-volume-path refused");
        q.volume_path=r.grains_root.join("vars/../vars/0123456789abcdef-9101");
        assert!(r.coordinates(&q).is_err());
        let mut status=StatusRequest {verb:StatusVerb::VolumesStatus,store:r.store.clone(),deployment_id:r.deployment_id.clone(),volumes_root:r.grains_root.join("volumes")};
        assert!(r.status_coordinates(&status).is_ok());
        status.volumes_root=Path::new("/var/lib/mini-spk-worlds/fedcba9876543210/volumes").to_owned();
        assert_eq!(r.status_coordinates(&status).unwrap_err().to_string(),"volume-helper: cross-world-volume-path refused");
    }
    #[test]
    fn tenancy_helper_refuses_untyped_privilege_requests() {
        assert!(serde_json::from_str::<Request>(r#"{"verb":"exec","command":"sh"}"#).is_err());
        assert!(serde_json::from_str::<Request>(r#"{"verb":"mount","store":"","grain":"1","volumePath":"/","appUid":0,"sizeMib":1,"volumeId":"0","deploymentId":"0","command":"sh"}"#).is_err());
        assert!(serde_json::from_str::<StatusRequest>(r#"{"verb":"volumes-status","store":"0123456789abcdef","deploymentId":"a","volumesRoot":"/","command":"sh"}"#).is_err());
    }
}
