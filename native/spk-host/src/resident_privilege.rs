//! Broker-selected trusted bootstrap switches both identities before any app
//! bytes. Resident/operator and launch/reap worker then hold zero capabilities.
//! One private inherited channel, one spawn, actual waitpid; loss is unresolved.
use crate::spawn_gate::{AppFds,BoundedChild,SpawnSpec};
use serde::{Deserialize,Serialize};
use std::fs;
use std::io::{self,Read,Write};
use std::os::fd::{AsRawFd,FromRawFd,OwnedFd};
use std::os::unix::net::UnixStream;
use std::path::Path;
use std::sync::{Mutex,OnceLock};
use std::time::Duration;
const LIMIT:usize=1024*1024;
const TIMEOUT:Duration=Duration::from_secs(10);
static LAUNCH:OnceLock<Mutex<Option<Client>>>=OnceLock::new();
fn refused(s:&str)->io::Error{io::Error::new(io::ErrorKind::InvalidInput,s)}
#[derive(Clone,Copy,Debug)]
struct Identity{uid:u32,gid:u32}
impl Identity{
    fn unit(prefix:&str)->io::Result<Self>{
        let parse=|part:&str|->io::Result<u32>{
            std::env::var(format!("MINI_SPK_{prefix}_{part}")).ok().and_then(|x|x.parse().ok())
                .filter(|x|*x>=100).ok_or_else(||refused("broker-rendered nonprivileged identity absent"))
        };Ok(Self{uid:parse("UID")?,gid:parse("GID")?})
    }
}
fn capability_sets_zero()->io::Result<bool>{
    let status=fs::read_to_string("/proc/thread-self/status")?;
    for field in ["CapInh:","CapPrm:","CapEff:","CapBnd:","CapAmb:"]{
        let value=status.lines().find_map(|x|x.strip_prefix(field)).ok_or_else(||refused("capability set absent"))?;
        if u64::from_str_radix(value.trim(),16).map_err(|_|refused("capability set invalid"))?!=0{return Ok(false)}
    }Ok(true)
}
fn dropped(identity:Identity)->io::Result<()>{
    let (mut u0,mut u1,mut u2)=(0,0,0);let (mut g0,mut g1,mut g2)=(0,0,0);
    if unsafe{libc::getresuid(&mut u0,&mut u1,&mut u2)}!=0 || unsafe{libc::getresgid(&mut g0,&mut g1,&mut g2)}!=0
        ||[u0,u1,u2]!=[identity.uid;3]||[g0,g1,g2]!=[identity.gid;3]||unsafe{libc::getgroups(0,std::ptr::null_mut())}!=0
        ||unsafe{libc::prctl(libc::PR_GET_NO_NEW_PRIVS,0,0,0,0)}!=1||!capability_sets_zero()?{
        return Err(refused("bootstrap identity/groups/capabilities/no_new_privs differ"))
    }Ok(())
}
fn drop_identity(identity:Identity)->io::Result<()>{
    // The root-owned unit bounds startup to SETUID, SETGID, SETPCAP. Dropping
    // bounding bits does not remove currently permitted SETID before the switch.
    for cap in 0..64{
        if unsafe{libc::prctl(libc::PR_CAPBSET_DROP,cap,0,0,0)}!=0{
            let e=io::Error::last_os_error();if e.raw_os_error()!=Some(libc::EINVAL){return Err(e)}
        }
    }
    if unsafe{libc::prctl(libc::PR_SET_NO_NEW_PRIVS,1,0,0,0)}!=0
        ||unsafe{libc::setgroups(0,std::ptr::null())}!=0
        ||unsafe{libc::setresgid(identity.gid,identity.gid,identity.gid)}!=0
        ||unsafe{libc::setresuid(identity.uid,identity.uid,identity.uid)}!=0
        ||unsafe{libc::prctl(libc::PR_CAP_AMBIENT,libc::PR_CAP_AMBIENT_CLEAR_ALL,0,0,0)}!=0
        ||!crate::setid_bound::clear_capabilities()
        ||unsafe{libc::prctl(libc::PR_SET_DUMPABLE,0,0,0,0)}!=0{
        return Err(io::Error::last_os_error())
    }dropped(identity)
}
fn install_parser_namespace_filter()->io::Result<()>{
    #[cfg(target_arch="x86_64")]const ARCH:u32=0xc000003e;
    #[cfg(target_arch="aarch64")]const ARCH:u32=0xc00000b7;
    let ins=|code,jt,jf,k|libc::sock_filter{code,jt,jf,k};
    let deny=0x00050000|libc::EPERM as u32;
    let mut p=vec![ins(0x20,0,0,4),ins(0x15,1,0,ARCH),ins(0x06,0,0,0x80000000),ins(0x20,0,0,0)];
    #[cfg(target_arch="x86_64")]{p.push(ins(0x35,0,1,0x40000000));p.push(ins(0x06,0,0,0x80000000));}
    for nr in [libc::SYS_unshare,libc::SYS_setns]{p.push(ins(0x15,0,1,nr as u32));p.push(ins(0x06,0,0,deny));}
    p.push(ins(0x15,0,1,libc::SYS_clone3 as u32));p.push(ins(0x06,0,0,0x00050000|libc::ENOSYS as u32));
    p.extend([ins(0x15,0,3,libc::SYS_clone as u32),ins(0x20,0,0,16),
        ins(0x45,0,1,(libc::CLONE_NEWCGROUP|libc::CLONE_NEWIPC|libc::CLONE_NEWNET|libc::CLONE_NEWNS|libc::CLONE_NEWPID|libc::CLONE_NEWUSER|libc::CLONE_NEWUTS|0x80) as u32),
        ins(0x06,0,0,deny),ins(0x06,0,0,0x7fff0000)]);
    let prog=libc::sock_fprog{len:p.len() as u16,filter:p.as_mut_ptr()};
    let rc=unsafe{libc::syscall(libc::SYS_seccomp,libc::SECCOMP_SET_MODE_FILTER,libc::SECCOMP_FILTER_FLAG_TSYNC,&prog)};
    if rc!=0{return Err(io::Error::last_os_error())}Ok(())
}
#[derive(Serialize,Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Launch {program:std::path::PathBuf,sha256:String,args:Vec<String>}
#[derive(Serialize,Deserialize)]
#[serde(rename_all="camelCase",deny_unknown_fields)]
struct Reply {pid:u32,start:String,reaped:bool,status:Option<i32>,error:Option<String>}
fn send_frame(stream:&mut UnixStream,value:&impl Serialize)->io::Result<()>{
    let b=serde_json::to_vec(value)?;if b.is_empty()||b.len()>LIMIT{return Err(refused("launch frame bound"))}
    stream.write_all(&(b.len() as u32).to_le_bytes())?;stream.write_all(&b)
}
fn receive_frame<T:serde::de::DeserializeOwned>(stream:&mut UnixStream)->io::Result<T>{
    let mut h=[0;4];stream.read_exact(&mut h)?;let n=u32::from_le_bytes(h) as usize;
    if n==0||n>LIMIT{return Err(refused("launch frame bound"))}let mut b=vec![0;n];stream.read_exact(&mut b)?;Ok(serde_json::from_slice(&b)?)
}
fn send_rights(stream:&UnixStream,tag:u8,fds:&[i32])->io::Result<()>{
    let mut tag=tag;let mut iov=libc::iovec{iov_base:(&mut tag as *mut u8).cast(),iov_len:1};
    let size=unsafe{libc::CMSG_SPACE(std::mem::size_of_val(fds) as u32)} as usize;
    let mut control=vec![0usize;size.div_ceil(std::mem::size_of::<usize>())];
    let mut msg:libc::msghdr=unsafe{std::mem::zeroed()};msg.msg_iov=&mut iov;msg.msg_iovlen=1;
    if !fds.is_empty(){msg.msg_control=control.as_mut_ptr().cast();msg.msg_controllen=size;
        unsafe{let c=libc::CMSG_FIRSTHDR(&msg);(*c).cmsg_level=libc::SOL_SOCKET;(*c).cmsg_type=libc::SCM_RIGHTS;(*c).cmsg_len=libc::CMSG_LEN(std::mem::size_of_val(fds) as u32) as usize;
            std::ptr::copy_nonoverlapping(fds.as_ptr().cast::<u8>(),libc::CMSG_DATA(c),std::mem::size_of_val(fds));}}
    if unsafe{libc::sendmsg(stream.as_raw_fd(),&msg,libc::MSG_NOSIGNAL)}!=1{return Err(io::Error::last_os_error())}Ok(())
}
fn receive_rights(stream:&UnixStream)->io::Result<(u8,Vec<OwnedFd>)>{
    let mut tag=0u8;let mut iov=libc::iovec{iov_base:(&mut tag as *mut u8).cast(),iov_len:1};
    let size=unsafe{libc::CMSG_SPACE(8*4)} as usize;let mut control=vec![0usize;size.div_ceil(std::mem::size_of::<usize>())];
    let mut msg:libc::msghdr=unsafe{std::mem::zeroed()};msg.msg_iov=&mut iov;msg.msg_iovlen=1;msg.msg_control=control.as_mut_ptr().cast();msg.msg_controllen=size;
    let n=unsafe{libc::recvmsg(stream.as_raw_fd(),&mut msg,libc::MSG_CMSG_CLOEXEC)};
    if n==0{return Err(io::Error::from(io::ErrorKind::UnexpectedEof))}if n<0{return Err(io::Error::last_os_error())}
    let mut fds=Vec::new();let mut bad=false;
    unsafe{let mut c=libc::CMSG_FIRSTHDR(&msg);while !c.is_null(){
        if (*c).cmsg_level!=libc::SOL_SOCKET||(*c).cmsg_type!=libc::SCM_RIGHTS||(*c).cmsg_len<libc::CMSG_LEN(0) as usize{bad=true;break}
        let bytes=(*c).cmsg_len-libc::CMSG_LEN(0) as usize;
        if bytes%4!=0{bad=true;break}for i in 0..bytes/4{fds.push(OwnedFd::from_raw_fd(std::ptr::read_unaligned(libc::CMSG_DATA(c).add(i*4).cast::<i32>())));}
        c=libc::CMSG_NXTHDR(&msg,c);
    }}
    if bad||msg.msg_flags&(libc::MSG_TRUNC|libc::MSG_CTRUNC)!=0||n!=1{return Err(refused("launch descriptor frame refused"))}
    Ok((tag,fds))
}
fn start_identity(pid:u32)->io::Result<String>{
    let text=fs::read_to_string(format!("/proc/{pid}/stat"))?;
    text.rsplit_once(')').and_then(|(_,tail)|tail.split_whitespace().nth(19)).map(str::to_owned).ok_or_else(||refused("app PID start identity absent"))
}
#[derive(Debug)]
pub(crate) struct Client {stream:UnixStream,start:String,pid:u32,worker:libc::pid_t}
impl Drop for Client {
    fn drop(&mut self){
        // EOF asks the app-identity worker to kill/reap its actual child. The
        // operator may reap its own worker, but cannot manufacture waitpid for
        // the grandchild. A lost channel still needs independent unit audit.
        let _=self.stream.shutdown(std::net::Shutdown::Both);
        let end=std::time::Instant::now()+Duration::from_secs(5);
        loop {let n=unsafe {libc::waitpid(self.worker,std::ptr::null_mut(),libc::WNOHANG)};
            if n==self.worker || n<0 && io::Error::last_os_error().raw_os_error()==Some(libc::ECHILD){break}
            if std::time::Instant::now()>=end {break}
            std::thread::sleep(Duration::from_millis(10));
        }
    }
}
impl Client {
    pub(crate) fn wait(&mut self,pid:u32)->io::Result<i32>{
        loop{let r=self.command(2,pid)?;if r.reaped{return r.status.ok_or_else(||refused("reaped child status absent"))}std::thread::sleep(Duration::from_millis(20));}
    }
    pub(crate) fn kill_and_reap(&mut self,pid:u32)->io::Result<bool>{Ok(self.command(3,pid)?.reaped)}
    fn command(&mut self,tag:u8,pid:u32)->io::Result<Reply>{
        if self.pid!=pid||self.start.is_empty(){return Err(refused("launch reaper identity differs"))}
        send_rights(&self.stream,tag,&[])?;let r:Reply=receive_frame(&mut self.stream)?;
        if r.pid!=pid||r.start!=self.start{return Err(refused("launch reaper PID/start changed"))}
        if let Some(error)=&r.error{return Err(io::Error::other(error.clone()))}Ok(r)
    }
}
pub(crate) fn launch(spec:&SpawnSpec)->io::Result<Option<BoundedChild>>{
    let Some(lock)=LAUNCH.get() else{return Ok(None)};
    let mut client=lock.lock().map_err(|_|refused("launch channel poisoned"))?.take().ok_or_else(||refused("generation launch channel already consumed; exact recovery only"))?;
    let f=spec.fds.ok_or_else(||refused("admitted launch descriptors absent"))?;
    send_rights(&client.stream,1,&[f.rpc,f.image,f.persistent_var,f.seccomp,f.output])?;
    send_frame(&mut client.stream,&Launch{program:spec.program.clone(),sha256:spec.sha256.clone(),args:spec.args.clone()})?;
    let r:Reply=receive_frame(&mut client.stream)?;
    if let Some(error)=r.error{return Err(io::Error::other(error))}
    if r.pid==0||r.start.is_empty()||r.reaped{return Err(refused("launch worker did not confirm live child identity"))}
    client.pid=r.pid;client.start=r.start;Ok(Some(BoundedChild::remote(r.pid as i32,client)))
}
fn worker(mut stream:UnixStream,app:Identity)->io::Result<()>{
    drop_identity(app)?;
    // The launch worker inherits only its private channel and standard unit
    // output; root/bootstrap descriptors or environment never reach its parser.
    let fd=stream.as_raw_fd() as u32;
    if fd>3 && unsafe{libc::syscall(libc::SYS_close_range,3u32,fd-1,0u32)}<0 {return Err(io::Error::last_os_error())}
    if unsafe{libc::syscall(libc::SYS_close_range,fd+1,u32::MAX,0u32)}<0 {return Err(io::Error::last_os_error())}
    for (key,_) in std::env::vars_os(){std::env::remove_var(key);}
    stream.set_read_timeout(None)?;stream.set_write_timeout(Some(TIMEOUT))?;
    let (tag,fds)=receive_rights(&stream)?;stream.set_read_timeout(Some(TIMEOUT))?;
    if tag!=1||fds.len()!=5{return Err(refused("one launch with exactly five admitted descriptors required"))}
    let wire:Launch=receive_frame(&mut stream)?;
    let mut owned=Vec::new();for fd in &fds{
        let high=unsafe{libc::fcntl(fd.as_raw_fd(),libc::F_DUPFD_CLOEXEC,10)};if high<0{return Err(io::Error::last_os_error())}owned.push(unsafe{OwnedFd::from_raw_fd(high)});
    }
    let f=AppFds{rpc:owned[0].as_raw_fd(),image:owned[1].as_raw_fd(),persistent_var:owned[2].as_raw_fd(),seccomp:owned[3].as_raw_fd(),output:owned[4].as_raw_fd()};
    let spec=SpawnSpec{program:wire.program,sha256:wire.sha256,args:wire.args,app_uid:app.uid,app_gid:app.gid,fds:Some(f)};
    let mut child=match crate::spawn_gate::spawn_as_self(&spec){Ok(child)=>child,Err(e)=>{
        send_frame(&mut stream,&Reply{pid:0,start:String::new(),reaped:false,status:None,error:Some(e.to_string())})?;return Err(e)
    }};
    let pid=child.pid();let start=start_identity(pid)?;
    send_frame(&mut stream,&Reply{pid,start:start.clone(),reaped:false,status:None,error:None})?;
    stream.set_read_timeout(None)?;
    loop{
        let (tag,fds)=receive_rights(&stream)?;if !fds.is_empty()||!matches!(tag,2|3){return Err(refused("launch worker command refused"))}
        let result=if tag==3{
            let dead=child.kill_and_reap();(dead,None)
        }else{match child.try_wait()?{Some(status)=>(true,Some(status)),None=>(false,None)}};
        send_frame(&mut stream,&Reply{pid,start:start.clone(),reaped:result.0,status:result.1,error:None})?;
        if result.0{return Ok(())}
    }
}
pub(crate) fn require_app_identity(uid:u32,gid:u32)->io::Result<()> {dropped(Identity{uid,gid})}
pub(crate) fn require_parser()->io::Result<()>{
    if LAUNCH.get().is_none(){return Err(refused("resident needs broker identity bootstrap before parsing"))}
    dropped(Identity::unit("OPERATOR")?)
}
/// Only root-owned broker unit environment selects identities. No app packet
/// can name an operator/app UID/GID; neither parser retains switch privileges.
pub fn run(path:&Path)->io::Result<()>{
    if unsafe{libc::geteuid()}!=0{return Err(refused("resident bootstrap requires trusted root unit"))}
    let operator=Identity::unit("OPERATOR")?;let app=Identity::unit("APP")?;
    if operator.uid==app.uid{return Err(refused("operator and app identities must differ"))}
    let (parent,child)=UnixStream::pair()?;
    let pid=unsafe{libc::fork()};if pid<0{return Err(io::Error::last_os_error())}
    if pid==0{
        drop(parent);let status=if worker(child,app).is_ok(){0}else{1};unsafe{libc::_exit(status)}
    }
    drop(child);drop_identity(operator)?;install_parser_namespace_filter()?;
    parent.set_read_timeout(Some(TIMEOUT))?;parent.set_write_timeout(Some(TIMEOUT))?;
    LAUNCH.set(Mutex::new(Some(Client{stream:parent,start:String::new(),pid:0,worker:pid}))).map_err(|_|refused("resident bootstrap already initialized"))?;
    let result=crate::resident_service::run(path);
    if let Some(lock)=LAUNCH.get(){if let Ok(mut client)=lock.lock(){drop(client.take());}}
    result
}
