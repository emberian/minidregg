//! The host-side volume custodian and its client (deploy/spk-host/VOLUMES.md, "The custodian").
//! The kernel lets only the initial user namespace set a project id or a quota limit. The custodian
//! is a small root service on the host that does exactly that, for directories under one root and
//! named by a grain id alone; the helper inside a user-namespaced container asks it over one Unix
//! socket. Request grammar, one line each way, version 1:
//!
//!   MINI-VOLUME/1 create <ID> <SIZE_MIB> <APP_UID>
//!   MINI-VOLUME/1 usage <ID>
//!   MINI-VOLUME/1 destroy <ID>
//!   -> OK key=value ...      |      REFUSED <name> <text>
//!
//! `ID` is `<store, 16 lower-case hex>-<resource, canonical decimal>`: the volume's directory name
//! under `ROOT/vars`. No other text from a caller reaches a path.
use super::volume_custody::Dir;
use super::volume_dir::{cstr, deterministic_project, open_dir_at, remove_contents, stat_at, PROJECT_BASE, PROJECT_PROBES};
use super::*;
use crate::volume_quota as quota;
use std::collections::BTreeMap;
use std::os::unix::fs::FileTypeExt;

fn refuse(message: impl Into<String>) -> io::Error { io::Error::new(io::ErrorKind::PermissionDenied, message.into()) }

const VERSION: &str = "MINI-VOLUME/1";
const MAX_LINE: u64 = 256;

fn valid_id(id: &str) -> bool {
    match id.split_once('-') { Some((store, resource)) => store_key(store) && decimal(resource), None => false }
}

// ---------------------------------------------------------------- client

#[derive(Debug)]
pub(crate) struct Reply(pub BTreeMap<String, u64>);

impl Reply {
    pub(crate) fn get(&self, key: &str) -> io::Result<u64> {
        self.0.get(key).copied().ok_or_else(|| refuse(format!("volume custodian reply lacks {key}")))
    }
}

fn call(socket: &Path, line: &str) -> io::Result<Reply> {
    let mut stream = UnixStream::connect(socket).map_err(|e| io::Error::new(e.kind(), format!("volume custodian {}: {e}", socket.display())))?;
    stream.set_read_timeout(Some(Duration::from_secs(120)))?;
    stream.set_write_timeout(Some(Duration::from_secs(10)))?;
    stream.write_all(format!("{VERSION} {line}\n").as_bytes())?;
    let mut text = String::new();
    BufReader::new(stream.take(4096)).read_line(&mut text)?;
    let text = text.strip_suffix('\n').ok_or_else(|| refuse("volume custodian reply truncated"))?;
    if let Some(rest) = text.strip_prefix("REFUSED ") { return Err(refuse(format!("volume custodian refused: {rest}"))); }
    let rest = text.strip_prefix("OK").ok_or_else(|| refuse("volume custodian reply refused"))?;
    let mut map = BTreeMap::new();
    for pair in rest.split_whitespace() {
        let (k, v) = pair.split_once('=').ok_or_else(|| refuse("volume custodian reply field refused"))?;
        map.insert(k.to_owned(), v.parse().map_err(|_| refuse("volume custodian reply number refused"))?);
    }
    Ok(Reply(map))
}

pub(crate) fn create(socket: &Path, id: &str, size_mib: u64, app_uid: u32) -> io::Result<Reply> {
    call(socket, &format!("create {id} {size_mib} {app_uid}"))
}
pub(crate) fn usage(socket: &Path, id: &str) -> io::Result<Reply> { call(socket, &format!("usage {id}")) }
pub(crate) fn destroy(socket: &Path, id: &str) -> io::Result<Reply> { call(socket, &format!("destroy {id}")) }

// ---------------------------------------------------------------- service

#[derive(Debug, PartialEq, Eq)]
enum Op { Create { id: String, size_mib: u64, app_uid: u32 }, Usage(String), Destroy(String) }

fn parse(line: &str) -> io::Result<Op> {
    let mut w = line.split(' ');
    if w.next() != Some(VERSION) { return Err(named("bad-version", format!("speak {VERSION}"))); }
    let verb = w.next().unwrap_or("");
    let id = w.next().ok_or_else(|| named("bad-request", "no volume id"))?;
    if !valid_id(id) { return Err(named("bad-id", "volume ids are <store>-<resource>")); }
    let id = id.to_owned();
    let mut num = || -> io::Result<u64> {
        w.next().filter(|s| decimal(s)).and_then(|s| s.parse().ok()).ok_or_else(|| named("bad-request", "a number is not a canonical decimal"))
    };
    let op = match verb {
        "create" => { let size_mib = num()?; let app_uid = u32::try_from(num()?).map_err(|_| named("bad-uid", "uid too large"))?; Op::Create { id, size_mib, app_uid } }
        "usage" => Op::Usage(id),
        "destroy" => Op::Destroy(id),
        _ => return Err(named("bad-request", "verb is create, usage or destroy")),
    };
    if w.next().is_some() { return Err(named("bad-request", "trailing words")); }
    Ok(op)
}

pub struct Custodian {
    root: PathBuf,
    uid_base: u32,
    uid_limit: u32,
    vars: Dir,
    lock: File,
}

fn named(name: &str, text: impl std::fmt::Display) -> io::Error { refuse(format!("{name} {text}")) }

impl Custodian {
    /// Open the root, require project quota on it and make `vars` (0711, owned by the container's
    /// root, which is `uid_base` on the host). Everything later is relative to these descriptors.
    pub fn open(root: &Path, uid_base: u32, uid_limit: u32) -> io::Result<Self> {
        if unsafe { libc::geteuid() } != 0 || !quota::in_init_user_namespace(&fs::read_to_string("/proc/self/uid_map")?) {
            return Err(refuse("the custodian runs as root in the initial user namespace"));
        }
        if uid_limit == 0 || uid_base.checked_add(uid_limit).is_none() { return Err(refuse("custodian uid range refused")); }
        let rootdir = Dir::absolute(root, &[0])?;
        let name = cstr("vars")?;
        if stat_at(rootdir.0.as_raw_fd(), &name)?.is_none() && unsafe { libc::mkdirat(rootdir.0.as_raw_fd(), name.as_ptr(), 0o711) } != 0 {
            return Err(io::Error::last_os_error());
        }
        let vars = rootdir.directory("vars", &[0, uid_base])?;
        if unsafe { libc::fchown(vars.0.as_raw_fd(), uid_base, uid_base) } != 0 || unsafe { libc::fchmod(vars.0.as_raw_fd(), 0o711) } != 0 {
            return Err(io::Error::last_os_error());
        }
        quota::require_project_quota(vars.0.as_raw_fd())?;
        let lock_name = cstr(".custodian.lock")?;
        let fd = unsafe { libc::openat(rootdir.0.as_raw_fd(), lock_name.as_ptr(), libc::O_RDWR | libc::O_CREAT | libc::O_NOFOLLOW | libc::O_CLOEXEC, 0o600) };
        if fd < 0 { return Err(io::Error::last_os_error()); }
        let lock = unsafe { File::from_raw_fd(fd) };
        let m = lock.metadata()?;
        if !m.is_file() || m.uid() != 0 || m.nlink() != 1 { return Err(refuse("custodian lock custody refused")); }
        Ok(Self { root: root.to_owned(), uid_base, uid_limit, vars, lock })
    }

    fn exclusive(&self) -> io::Result<()> {
        if unsafe { libc::flock(self.lock.as_raw_fd(), libc::LOCK_EX) } != 0 { return Err(io::Error::last_os_error()); }
        Ok(())
    }

    fn open_volume(&self, id: &str) -> io::Result<Option<(File, u32)>> {
        let c = cstr(id)?;
        let Some(s) = stat_at(self.vars.0.as_raw_fd(), &c)? else { return Ok(None) };
        if s.st_mode & libc::S_IFMT != libc::S_IFDIR { return Err(named("not-a-volume", "the name is not a plain directory")); }
        let dir = open_dir_at(self.vars.0.as_raw_fd(), &c).map_err(|_| named("not-a-volume", "the name is not a plain directory"))?;
        let m = dir.metadata()?;
        if m.dev() != self.vars.0.metadata()?.dev() || m.ino() != s.st_ino as u64 {
            return Err(named("not-a-volume", "the directory is on another filesystem or was replaced"));
        }
        if m.uid() < self.uid_base || m.uid() - self.uid_base >= self.uid_limit {
            return Err(named("not-a-volume", "the directory is not owned inside the container's uid range"));
        }
        let (project, inherit) = quota::project_of(dir.as_raw_fd())?;
        if project < PROJECT_BASE || !inherit { return Err(named("not-a-volume", "the directory carries no custodian project")); }
        Ok(Some((dir, project)))
    }

    fn claim_project(&self, id: &str) -> io::Result<u32> {
        for probe in 0..PROJECT_PROBES {
            let p = deterministic_project(id, probe);
            if !quota::in_use(&quota::get_quota(self.vars.0.as_raw_fd(), p)?) { return Ok(p); }
        }
        Err(named("no-project-id", "no unused project id in the probe sequence"))
    }

    fn create(&self, id: &str, size_mib: u64, app_uid: u32) -> io::Result<String> {
        if !(64..=16384).contains(&size_mib) { return Err(named("bad-size", "size_mib must be 64..=16384")); }
        if app_uid == 0 || app_uid >= self.uid_limit { return Err(named("bad-uid", "app uid outside the container's range")); }
        let host_uid = self.uid_base + app_uid;
        let c = cstr(id)?;
        self.exclusive()?;
        if stat_at(self.vars.0.as_raw_fd(), &c)?.is_some() { return Err(named("exists", "a volume of this id already exists")); }
        let project = self.claim_project(id)?;
        let (mut made, mut limited) = (false, false);
        let bytes = size_mib * 1024 * 1024;
        let result = (|| -> io::Result<()> {
            if unsafe { libc::mkdirat(self.vars.0.as_raw_fd(), c.as_ptr(), 0o700) } != 0 { return Err(io::Error::last_os_error()); }
            made = true;
            let dir = open_dir_at(self.vars.0.as_raw_fd(), &c)?;
            // Bounded before it is owned by the grain: nothing of the grain's can be written first.
            quota::set_project(dir.as_raw_fd(), project)?;
            limited = true;
            quota::set_limits(dir.as_raw_fd(), project, bytes, bytes / quota::BYTES_PER_INODE)?;
            if unsafe { libc::fchown(dir.as_raw_fd(), host_uid, host_uid) } != 0 || unsafe { libc::fchmod(dir.as_raw_fd(), 0o700) } != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        })();
        if let Err(e) = result {
            if made {
                if let Ok(dir) = open_dir_at(self.vars.0.as_raw_fd(), &c) {
                    let _ = remove_contents(dir.as_raw_fd());
                    if limited { let _ = quota::clear_limits(dir.as_raw_fd(), project); }
                }
                unsafe { libc::unlinkat(self.vars.0.as_raw_fd(), c.as_ptr(), libc::AT_REMOVEDIR) };
            }
            return Err(named("kernel", e));
        }
        Ok(format!("project={project} bytes={bytes} inodes={}", bytes / quota::BYTES_PER_INODE))
    }

    fn usage(&self, id: &str) -> io::Result<String> {
        let (dir, project) = self.open_volume(id)?.ok_or_else(|| named("absent", "no volume of this id"))?;
        let q = quota::get_quota(dir.as_raw_fd(), project)?;
        let m = dir.metadata()?;
        Ok(format!("project={project} uid={} inode={} bhard_kib={} bsoft_kib={} ihard={} isoft={} cur_bytes={} cur_inodes={}",
            m.uid() - self.uid_base, m.ino(), q.bhardlimit, q.bsoftlimit, q.ihardlimit, q.isoftlimit, q.curspace, q.curinodes))
    }

    fn destroy(&self, id: &str) -> io::Result<String> {
        self.exclusive()?;
        let Some((dir, project)) = self.open_volume(id)? else { return Ok("removed=0".into()) };
        // Contents, then the limit, then the name: a destroy cut short is finished by running it again.
        remove_contents(dir.as_raw_fd())?;
        quota::clear_limits(dir.as_raw_fd(), project)?;
        drop(dir);
        let c = cstr(id)?;
        if unsafe { libc::unlinkat(self.vars.0.as_raw_fd(), c.as_ptr(), libc::AT_REMOVEDIR) } != 0 { return Err(io::Error::last_os_error()); }
        Ok("removed=1".into())
    }

    /// One request line to one reply line.
    pub fn handle(&self, line: &str) -> String {
        let result = parse(line).and_then(|op| match op {
            Op::Create { id, size_mib, app_uid } => self.create(&id, size_mib, app_uid),
            Op::Usage(id) => self.usage(&id),
            Op::Destroy(id) => self.destroy(&id),
        });
        match result {
            Ok(fields) => format!("OK {fields}\n"),
            Err(e) => {
                let text = e.to_string().replace('\n', " ");
                // A refusal already carries its name; anything else is the kernel's.
                if e.kind() == io::ErrorKind::PermissionDenied { format!("REFUSED {text}\n") } else { format!("REFUSED kernel {text}\n") }
            }
        }
    }

    /// Serve `socket` until the process ends. Mode 0660 with `gid` as its group; a stale socket
    /// file is replaced, anything else at the path is refused.
    pub fn serve(&self, socket: &Path, gid: u32) -> io::Result<()> {
        if let Ok(m) = fs::symlink_metadata(socket) {
            if !m.file_type().is_socket() { return Err(refuse("custodian socket path holds something other than a socket")); }
            fs::remove_file(socket)?;
        }
        let listener = UnixListener::bind(socket)?;
        let c = CString::new(socket.as_os_str().as_encoded_bytes()).map_err(|_| refuse("socket path"))?;
        if unsafe { libc::chown(c.as_ptr(), 0, gid) } != 0 { return Err(io::Error::last_os_error()); }
        fs::set_permissions(socket, fs::Permissions::from_mode(0o660))?;
        eprintln!("volume-custodian root={} socket={} uid-range={}+{}", self.root.display(), socket.display(), self.uid_base, self.uid_limit);
        for stream in listener.incoming() {
            let Ok(mut stream) = stream else { continue };
            let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
            let mut line = String::new();
            let reply = match BufReader::new((&stream).take(MAX_LINE)).read_line(&mut line) {
                Ok(_) if line.ends_with('\n') => self.handle(line.trim_end_matches('\n')),
                _ => "REFUSED bad-request line missing or over 256 bytes\n".to_owned(),
            };
            eprintln!("volume-custodian {} -> {}", line.trim_end(), reply.trim_end());
            let _ = stream.write_all(reply.as_bytes());
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const ID: &str = "0123456789abcdef-9101";

    #[test]
    fn the_grammar_takes_three_verbs_and_a_grain_id_and_nothing_else() {
        assert_eq!(parse(&format!("{VERSION} create {ID} 64 165")).unwrap(), Op::Create { id: ID.into(), size_mib: 64, app_uid: 165 });
        assert_eq!(parse(&format!("{VERSION} usage {ID}")).unwrap(), Op::Usage(ID.into()));
        assert_eq!(parse(&format!("{VERSION} destroy {ID}")).unwrap(), Op::Destroy(ID.into()));
        for bad in [
            format!("MINI-VOLUME/2 usage {ID}"), format!("usage {ID}"), format!("{VERSION} usage"),
            format!("{VERSION} usage ../{ID}"), format!("{VERSION} usage /etc"), format!("{VERSION} usage 0123456789ABCDEF-9101"),
            format!("{VERSION} usage 0123456789abcdef-09101"), format!("{VERSION} usage {ID} extra"), format!("{VERSION}  usage {ID}"),
            format!("{VERSION} create {ID} 64"), format!("{VERSION} create {ID} 064 165"), format!("{VERSION} create {ID} 64 -1"),
            format!("{VERSION} create {ID} 64 165 9"), format!("{VERSION} chown {ID}"), format!("{VERSION} usage {ID}\n"),
        ] {
            assert!(parse(&bad).is_err(), "{bad:?}");
        }
    }

    #[test]
    fn replies_round_trip_and_a_refusal_is_an_error_with_its_name() {
        let dir = std::env::temp_dir().join(format!("mini-custodian-{}", std::process::id()));
        fs::create_dir(&dir).unwrap();
        let sock = dir.join("s");
        let listener = UnixListener::bind(&sock).unwrap();
        let t = std::thread::spawn(move || {
            for reply in ["OK project=1000000007 bytes=67108864\n", "REFUSED exists a volume of this id already exists\n"] {
                let (mut c, _) = listener.accept().unwrap();
                let mut l = String::new();
                BufReader::new(&c).read_line(&mut l).unwrap();
                assert!(l.starts_with("MINI-VOLUME/1 "), "{l}");
                c.write_all(reply.as_bytes()).unwrap();
            }
        });
        let ok = create(&sock, ID, 64, 165).unwrap();
        assert_eq!(ok.get("project").unwrap(), 1_000_000_007);
        let err = destroy(&sock, ID).unwrap_err().to_string();
        assert!(err.contains("exists"), "{err}");
        t.join().unwrap();
        let _ = fs::remove_dir_all(&dir);
    }
}
