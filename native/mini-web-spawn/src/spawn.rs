//! Spawning as the member. On the box this is the SAME line the door's `mini-session-run` runs
//! (`setpriv --reuid=mini-s-NAME --regid=mini-sessions --init-groups --reset-env -- env -i …
//! mini-shell-ssh MINI HOST CONFIG SOCKET WORKSPACE HOME`), placed by `systemd-run --scope` in the
//! member's own `user-UID.slice`, so a browser shell and an ssh shell share one memory and task
//! cap. The differences from the runner: a pty instead of captured streams (`shell`), and for
//! `body` the inherited listener on fd 3 and `mini web --body` instead of the forced command.
//!
//! `--dev CONFIG.json` runs the same wrapper as the current user with paths from the file (the
//! Mac journey and the tests); no setpriv, no scope.

use std::collections::BTreeMap;
use std::ffi::{CStr, CString};
use std::fs;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::fs::MetadataExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::Value;

use crate::store::is_account_name;

/// Where a member's shell and body live.
#[derive(Debug, Clone, PartialEq)]
pub struct Member {
    pub account: String,
    pub uid: u32,
    pub workspace: PathBuf,
    pub home: PathBuf,
    /// The public reader: no writes are offered, every POST is refused by the body.
    pub anonymous: bool,
}

#[derive(Debug, Clone)]
pub struct DevConfig {
    pub mini: PathBuf,
    pub host: PathBuf,
    pub config: PathBuf,
    pub socket: PathBuf,
    pub wrapper: PathBuf,
    pub sessions: BTreeMap<String, (PathBuf, PathBuf)>,
    pub public: Option<(PathBuf, PathBuf)>,
    /// The public reader's enrolled subject (authors delegate `observe` to it).
    pub public_subject: Option<String>,
    /// The published document the public front page shows (`frontDoc`).
    pub front_doc: Option<String>,
    /// Which member's publication each house name is (`housePublications`: NAME -> member).
    pub house_publications: BTreeMap<String, String>,
    /// One resident directory for every session (`residents`): the dev layout runs every member as
    /// this one account, so they share ONE consent provider and ONE codec Host
    /// (`MINI_CONSENT_ANCHOR_DIR`, as `/etc/mini/session-residents` does for the ssh wrapper).
    pub residents: Option<PathBuf>,
}

/// A front-page document name as the body accepts it: a workspace reference name (1-64 of
/// `[A-Za-z0-9-]`). Anything else is no setting at all, so the front page stays the index.
pub fn front_doc_name(raw: &str) -> Option<String> {
    let name = raw.trim();
    (!name.is_empty() && name.len() <= 64 && name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-')).then(|| name.to_owned())
}

/// The public body's operations room: the reference name its front page reads as the box's own
/// signed turns (`web/body.rs` `operations`).
pub const OPERATIONS_ROOM: &str = "operations";

/// One house publication: a reference name and the hosted member whose publication it is.
fn house_entry(name: &str, member: &str) -> Option<(String, String)> {
    let name = front_doc_name(name)?;
    (is_account_name(member) && member != PUBLIC_NAME).then(|| (name, member.to_owned()))
}

/// `/etc/mini/house-publications`: one `NAME MEMBER` per line; anything else on a line drops
/// that line (its name then stays reserved for nobody).
pub fn house_publications(text: &str) -> BTreeMap<String, String> {
    text.lines()
        .filter_map(|line| {
            let mut words = line.split_whitespace();
            match (words.next(), words.next(), words.next()) {
                (Some(name), Some(member), None) => house_entry(name, member),
                _ => None,
            }
        })
        .collect()
}

/// The name a publication of DOC by MEMBER is handed to the public reader under. The public body
/// shows a house name (the front page's document, the operations room, every name the operator
/// lists) as the box's own, and binds a name to whichever publication it imports first, so a
/// house name is handed over only from the member the operator named for it; anyone else's
/// document of that name is handed over as `DOC-MEMBER` and reads at that name like any other.
pub fn handed_name(doc: &str, member: &str, front_doc: Option<&str>, house: &BTreeMap<String, String>) -> String {
    let reserved = doc == OPERATIONS_ROOM || front_doc == Some(doc) || house.contains_key(doc);
    if !reserved || house.get(doc).map(String::as_str) == Some(member) {
        return doc.to_owned();
    }
    let qualified = format!("{doc}-{member}");
    if qualified.len() <= 64 { qualified } else { format!("m-{member}") }
}

impl DevConfig {
    pub fn load(path: &Path) -> Result<DevConfig, String> {
        let v: Value = serde_json::from_slice(&fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?)
            .map_err(|e| format!("{}: {e}", path.display()))?;
        let abs = |k: &str| -> Result<PathBuf, String> {
            let p = PathBuf::from(v[k].as_str().ok_or_else(|| format!("dev config: {k} missing"))?);
            if !p.is_absolute() {
                return Err(format!("dev config: {k} must be absolute"));
            }
            Ok(p)
        };
        let pair = |v: &Value, who: &str| -> Result<(PathBuf, PathBuf), String> {
            let w = PathBuf::from(v["workspace"].as_str().ok_or_else(|| format!("dev config: {who} workspace missing"))?);
            let h = PathBuf::from(v["home"].as_str().ok_or_else(|| format!("dev config: {who} home missing"))?);
            if !w.is_absolute() || !h.is_absolute() {
                return Err(format!("dev config: {who} paths must be absolute"));
            }
            Ok((w, h))
        };
        let mut sessions = BTreeMap::new();
        if let Some(map) = v["sessions"].as_object() {
            for (name, entry) in map {
                if !is_account_name(name) {
                    return Err(format!("dev config: {name} is not an account name"));
                }
                sessions.insert(name.clone(), pair(entry, name)?);
            }
        }
        let public = if v["public"].is_object() { Some(pair(&v["public"], "public")?) } else { None };
        let public_subject = v["publicSubject"].as_str().map(str::to_owned).filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()));
        let front_doc = v["frontDoc"].as_str().and_then(front_doc_name);
        let house_publications = v["housePublications"].as_object().map(|map| {
            map.iter().filter_map(|(name, member)| house_entry(name, member.as_str()?)).collect()
        }).unwrap_or_default();
        let residents = match v["residents"].as_str() {
            None => None,
            Some(dir) if Path::new(dir).is_absolute() => Some(PathBuf::from(dir)),
            Some(_) => return Err("dev config: residents must be absolute".into()),
        };
        Ok(DevConfig { mini: abs("mini")?, host: abs("host")?, config: abs("config")?, socket: abs("socket")?, wrapper: abs("wrapper")?, sessions, public, public_subject, front_doc, house_publications, residents })
    }
}

/// The box's fixed layout (dregg-infra `edge/mini/lib.sh`), under an optional root for tests.
#[derive(Debug, Clone)]
pub struct BoxLayout {
    pub root: PathBuf,
}

impl BoxLayout {
    fn p(&self, rel: &str) -> PathBuf {
        self.root.join(rel.trim_start_matches('/'))
    }
    pub fn tenancy(&self) -> PathBuf { self.p("/etc/mini/tenancy") }
    pub fn mini(&self) -> PathBuf { self.p("/var/lib/mini/candidate/current/bin/mini") }
    pub fn host(&self) -> PathBuf { self.p("/var/lib/mini/candidate/current/bin/minidregg-host") }
    pub fn config(&self) -> PathBuf { self.p("/var/lib/mini/store/node/deployment/pinned-config.json") }
    pub fn socket(&self) -> PathBuf { self.p("/var/lib/mini/store/node/public/mini.sock") }
    pub fn wrapper(&self) -> PathBuf { self.p("/usr/local/lib/mini/mini-shell-ssh") }
    pub fn sessions(&self) -> PathBuf { self.p("/var/lib/mini/sessions") }
    /// The public reader's enrolled subject, written by the operator after `mini-reenroll public`.
    pub fn public_subject_file(&self) -> PathBuf { self.p("/etc/mini/public-subject") }
    /// The published document the public front page shows, one name, written by the operator (run-sheet
    /// step 9c: `welcome`). Absent, empty or not a reference name: the front page is the index.
    pub fn front_doc_file(&self) -> PathBuf { self.p("/etc/mini/front-doc") }
    /// Whose publication each house name is, written by the operator (`welcome house`,
    /// `operations box`). Absent: every house name is reserved for nobody.
    pub fn house_publications_file(&self) -> PathBuf { self.p("/etc/mini/house-publications") }
}

pub enum Layout {
    Box(BoxLayout),
    Dev(DevConfig),
}

pub const HOSTED_GROUP: &str = "mini-hosted";
pub const TENANT_GROUP: &str = "mini-sessions";
/// The public reader is a hosted member like any other (`mini-s-public`, enrolled through the
/// roster and `mini-reenroll`), so authors delegate `observe` to a real participant.
pub const PUBLIC_NAME: &str = "public";

pub struct Spawner {
    pub layout: Layout,
}

impl Spawner {
    /// The member NAME resolves to, with every check `mini-session-run` makes: split tenancy, the
    /// account exists and is hosted, its home is its own 0700 directory.
    pub fn member(&self, name: &str) -> Result<Member, String> {
        if !is_account_name(name) {
            return Err(format!("{name:?} is not a session name"));
        }
        match &self.layout {
            Layout::Dev(dev) => {
                let (workspace, home) = dev.sessions.get(name).ok_or_else(|| format!("{name} is not in the dev config"))?;
                Ok(Member { account: name.to_owned(), uid: unsafe { libc::getuid() }, workspace: workspace.clone(), home: home.clone(), anonymous: false })
            }
            Layout::Box(layout) => {
                let tenancy = fs::read_to_string(layout.tenancy()).unwrap_or_default();
                if tenancy.trim() != "split" {
                    return Err("only under split tenancy".into());
                }
                let account = format!("mini-s-{name}");
                let (uid, gid) = passwd(&account).ok_or_else(|| format!("no account {account} (render-authorized-keys.sh makes hosted accounts)"))?;
                let hosted_gid = group_gid(HOSTED_GROUP).ok_or_else(|| format!("no group {HOSTED_GROUP}"))?;
                if !in_group(&account, gid, hosted_gid) {
                    return Err(format!("{account} is not in {HOSTED_GROUP}"));
                }
                let home = layout.sessions().join(name);
                let meta = fs::symlink_metadata(&home).map_err(|_| format!("{} must be {account}'s 0700 home", home.display()))?;
                if !meta.is_dir() || meta.uid() != uid || meta.mode() & 0o777 != 0o700 {
                    return Err(format!("{} must be {account}'s 0700 home", home.display()));
                }
                Ok(Member { account, uid, workspace: home.join("workspace"), home, anonymous: false })
            }
        }
    }

    /// The public reader's body: the hosted member `public`, anonymous (no write offered).
    pub fn public(&self) -> Result<Member, String> {
        match &self.layout {
            Layout::Dev(dev) => {
                let (workspace, home) = dev.public.clone().ok_or("the dev config has no public reader")?;
                Ok(Member { account: PUBLIC_NAME.into(), uid: unsafe { libc::getuid() }, workspace, home, anonymous: true })
            }
            Layout::Box(_) => {
                let mut member = self.member(PUBLIC_NAME)?;
                member.anonymous = true;
                Ok(member)
            }
        }
    }

    /// The public reader's subject, when the operator has enrolled it (`/etc/mini/public-subject`,
    /// or `publicSubject` in the dev config).
    pub fn public_subject(&self) -> Option<String> {
        match &self.layout {
            Layout::Dev(dev) => dev.public_subject.clone(),
            Layout::Box(layout) => fs::read_to_string(layout.public_subject_file()).ok().map(|s| s.trim().to_owned()).filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())),
        }
    }

    /// Whose publication each house name is (`/etc/mini/house-publications`, or
    /// `housePublications` in the dev config).
    pub fn house_publications(&self) -> BTreeMap<String, String> {
        match &self.layout {
            Layout::Dev(dev) => dev.house_publications.clone(),
            Layout::Box(layout) => fs::read_to_string(layout.house_publications_file()).map(|t| house_publications(&t)).unwrap_or_default(),
        }
    }

    /// The public front page's document (`/etc/mini/front-doc`, or `frontDoc` in the dev config).
    pub fn front_doc(&self) -> Option<String> {
        match &self.layout {
            Layout::Dev(dev) => dev.front_doc.clone(),
            Layout::Box(layout) => fs::read_to_string(layout.front_doc_file()).ok().as_deref().and_then(front_doc_name),
        }
    }

    /// What a public body is started from, as one comparable line: the reader's subject and front
    /// document (both passed as arguments), the identity of its `workspace.json` (rewritten only by
    /// a lifecycle step: init, adoption, re-enrolment), the pinned config's (a re-genesis writes a
    /// new one) and the candidate the `mini` path resolves to. The helper warms the public body
    /// before any visitor, so a body started between a ship and the reader's re-initialisation must
    /// not outlive it: when the basis changes, the helper replaces the body.
    pub fn public_basis(&self, member: &Member) -> String {
        let (mini, _, config, _, _) = self.paths();
        let identity = |path: &Path| fs::metadata(path).map(|m| format!("{}:{}:{}.{}", m.dev(), m.ino(), m.mtime(), m.mtime_nsec())).unwrap_or_default();
        let candidate = fs::canonicalize(&mini).map(|p| p.display().to_string()).unwrap_or_default();
        format!("{:?} {:?} {} {} {candidate}", self.public_subject(), self.front_doc(), identity(&member.workspace.join("workspace.json")), identity(&config))
    }

    /// Every hosted member's home (the hand-off sweep reads their published references).
    pub fn homes(&self) -> Vec<(String, PathBuf)> {
        match &self.layout {
            Layout::Dev(dev) => dev.sessions.iter().map(|(n, (_, h))| (n.clone(), h.clone())).collect(),
            Layout::Box(layout) => fs::read_dir(layout.sessions())
                .map(|d| d.flatten().filter(|e| e.path().is_dir()).filter_map(|e| e.file_name().into_string().ok().map(|n| (n, e.path()))).collect())
                .unwrap_or_default(),
        }
    }

    fn paths(&self) -> (PathBuf, PathBuf, PathBuf, PathBuf, PathBuf) {
        match &self.layout {
            Layout::Dev(d) => (d.mini.clone(), d.host.clone(), d.config.clone(), d.socket.clone(), d.wrapper.clone()),
            Layout::Box(b) => (b.mini(), b.host(), b.config(), b.socket(), b.wrapper()),
        }
    }

    /// The privilege prefix: the scope and the setpriv line on the box, nothing in dev.
    fn command(&self, member: &Member, unit: &str, env: &[(&str, String)]) -> Command {
        let mut argv: Vec<String> = Vec::new();
        if let Layout::Box(_) = self.layout {
            argv.extend([
                "systemd-run".into(), "--scope".into(), "--quiet".into(), "--collect".into(),
                format!("--slice=user-{}.slice", member.uid), format!("--unit={unit}"),
                "-p".into(), "TasksMax=64".into(), "--".into(),
                "setpriv".into(), format!("--reuid={}", member.account), format!("--regid={TENANT_GROUP}"),
                "--init-groups".into(), "--reset-env".into(), "--".into(),
            ]);
        }
        argv.extend(["env".into(), "-i".into(), "PATH=/usr/bin:/bin".into(), "LANG=C.UTF-8".into(), format!("HOME={}", member.home.display())]);
        if let Layout::Dev(DevConfig { residents: Some(dir), .. }) = &self.layout {
            argv.push(format!("MINI_CONSENT_ANCHOR_DIR={}", dir.display()));
        }
        for (k, v) in env {
            argv.push(format!("{k}={v}"));
        }
        let mut command = Command::new(&argv[0]);
        command.args(&argv[1..]);
        command.env_clear();
        command.env("PATH", "/usr/bin:/bin:/usr/local/bin");
        command.stdin(Stdio::null()).stdout(Stdio::null()).stderr(Stdio::inherit());
        command
    }

    /// `mini shell` as the member under a fresh pty of COLS×ROWS: the child's pid and the master.
    pub fn shell(&self, member: &Member, unit: &str, cols: u16, rows: u16) -> Result<(u32, OwnedFd), String> {
        let (mini, host, config, socket, wrapper) = self.paths();
        let (master, slave_path) = open_pty()?;
        let mut command = self.command(member, unit, &[("TERM", "xterm-256color".into())]);
        command.arg(wrapper).arg(mini).arg(host).arg(config).arg(socket).arg(&member.workspace).arg(&member.home);
        let master_fd = master.as_raw_fd();
        let slave_c = CString::new(slave_path.as_bytes()).map_err(|_| "pty path")?;
        unsafe {
            command.pre_exec(move || {
                if libc::setsid() < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                let slave = libc::open(slave_c.as_ptr(), libc::O_RDWR | libc::O_NOCTTY);
                if slave < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                if libc::ioctl(slave, libc::TIOCSCTTY as _, 0) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                let size = libc::winsize { ws_row: rows, ws_col: cols, ws_xpixel: 0, ws_ypixel: 0 };
                libc::ioctl(slave, libc::TIOCSWINSZ as _, &size);
                for fd in 0..3 {
                    if libc::dup2(slave, fd) < 0 {
                        return Err(std::io::Error::last_os_error());
                    }
                }
                if slave > 2 {
                    libc::close(slave);
                }
                libc::close(master_fd);
                Ok(())
            });
        }
        let child = command.spawn().map_err(|e| format!("spawn shell: {e}"))?;
        Ok((child.id(), master))
    }

    /// `mini web --body` as the member, serving the inherited listener on fd 3: the child's pid.
    /// The body is spawned directly, not through the wrapper, so it carries the member's delegated
    /// consent selection itself (`delegated_consent_env`), as the wrapper exports it for a shell.
    pub fn body(&self, member: &Member, unit: &str, listener: &OwnedFd) -> Result<u32, String> {
        let (mini, host, config, socket, _wrapper) = self.paths();
        let env = delegated_consent_env(&mini, &host, &config, &member.home)?;
        let mut command = self.command(member, unit, &env);
        command.arg(mini).arg("web").arg("--body").arg("--listen-fd").arg("3")
            .arg("--dir").arg(&member.workspace).arg("--home").arg(&member.home)
            .arg("--socket").arg(socket).arg("--host").arg(host).arg("--config").arg(config);
        if member.anonymous {
            command.arg("--anonymous");
        }
        if let Some(subject) = self.public_subject() {
            command.arg("--public-subject").arg(subject);
        }
        // Only the public reader's front page shows the operator's document; a member's is their own.
        if member.anonymous {
            if let Some(doc) = self.front_doc() {
                command.arg("--front-doc").arg(doc);
            }
        }
        // fd 4: the read end of this helper's lifeline; the body exits at its EOF (`--parent-fd`).
        command.arg("--parent-fd").arg("4");
        let listener_fd = listener.as_raw_fd();
        let line = lifeline()?;
        unsafe {
            command.pre_exec(move || {
                if libc::dup2(listener_fd, 3) < 0 || libc::dup2(line, 4) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let child = command.spawn().map_err(|e| format!("spawn body: {e}"))?;
        Ok(child.id())
    }
}

/// The helper's lifeline: one pipe made once, both ends close-on-exec, the write end never written
/// and never closed while this process lives. Every body is handed the read end as its fd 4 and
/// exits when it reads EOF there, which is exactly when every write end is gone: this helper ended,
/// however it ended (a stop, a crash, SIGKILL), so no body outlives the helper that started it.
/// Returns the read end.
pub fn lifeline() -> Result<RawFd, String> {
    static LINE: std::sync::OnceLock<Result<(RawFd, RawFd), String>> = std::sync::OnceLock::new();
    LINE.get_or_init(|| {
        let mut fds = [0 as libc::c_int; 2];
        #[cfg(target_os = "linux")]
        let made = unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) };
        #[cfg(not(target_os = "linux"))]
        let made = unsafe { libc::pipe(fds.as_mut_ptr()) };
        if made != 0 {
            return Err(format!("lifeline pipe: {}", std::io::Error::last_os_error()));
        }
        for fd in fds {
            if unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) } != 0 {
                return Err(format!("lifeline close-on-exec: {}", std::io::Error::last_os_error()));
            }
        }
        Ok((fds[0], fds[1]))
    }).clone().map(|(read, _write)| read)
}

/// The delegated full consent selection for a member whose home holds `consent/peer.sock`.
///
/// Under split tenancy a member's account cannot read the operator's Store, so its full consent is
/// answered by a socket-activated worker running as the Store operator (`mini
/// serve-controller-consent`, the frame's mini-consent@NAME). The client takes that delegation only
/// from these seven variables together: the listener (peer uid 0, because systemd creates it), the
/// provider and config digests, and the three local consent paths. This is the same selection the
/// frame's mini-shell-ssh exports for an ssh or browser shell. Without the socket (a box without
/// delegation, a dev layout) it is empty and the body keeps the client's default.
pub fn delegated_consent_env(mini: &Path, host: &Path, config: &Path, home: &Path)
    -> Result<Vec<(&'static str, String)>, String> {
    use sha2::{Digest, Sha256};
    use std::os::unix::fs::FileTypeExt;
    let socket = home.join("consent/peer.sock");
    match fs::symlink_metadata(&socket) {
        Ok(meta) if meta.file_type().is_socket() => {}
        _ => return Ok(Vec::new()),
    }
    let consent = mini.with_file_name("minidregg-client-consent");
    let digest = |path: &Path| -> Result<String, String> {
        let bytes = fs::read(path).map_err(|e| format!("delegated consent: {}: {e}", path.display()))?;
        Ok(Sha256::digest(&bytes).iter().map(|b| format!("{b:02x}")).collect())
    };
    // The ship renders both digests once beside the socket (`consent/peer.pins`: one line,
    // `CONSENT_SHA256 CONFIG_SHA256`), as the ssh wrapper reads them; without it, hash here.
    let (consent_sha, config_sha) = match fs::read_to_string(home.join("consent/peer.pins")) {
        Ok(line) => {
            let hex = |s: &str| s.len() == 64 && s.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b));
            let mut words = line.split_whitespace();
            match (words.next(), words.next()) {
                (Some(a), Some(b)) if hex(a) && hex(b) => (a.to_owned(), b.to_owned()),
                _ => return Err("delegated consent: consent/peer.pins must hold two sha256 digests".into()),
            }
        }
        Err(_) => (digest(&consent)?, digest(config)?),
    };
    Ok(vec![
        ("MINI_CONSENT_SOCKET", socket.display().to_string()),
        ("MINI_CONSENT_PEER_UID", "0".into()),
        ("MINI_CONSENT_SHA256", consent_sha),
        ("MINI_CONSENT_CONFIG_SHA256", config_sha),
        ("MINI_LOCAL_HOST", host.display().to_string()),
        ("MINI_CONSENT_HOST", consent.display().to_string()),
        ("MINI_CONSENT_CONFIG", config.display().to_string()),
    ])
}

/// A new pty: the master (close-on-exec) and the slave's path.
fn open_pty() -> Result<(OwnedFd, String), String> {
    unsafe {
        let master = libc::posix_openpt(libc::O_RDWR | libc::O_NOCTTY);
        if master < 0 {
            return Err(format!("posix_openpt: {}", std::io::Error::last_os_error()));
        }
        let master = OwnedFd::from_raw_fd(master);
        if libc::grantpt(master.as_raw_fd()) < 0 || libc::unlockpt(master.as_raw_fd()) < 0 {
            return Err(format!("grantpt/unlockpt: {}", std::io::Error::last_os_error()));
        }
        libc::fcntl(master.as_raw_fd(), libc::F_SETFD, libc::FD_CLOEXEC);
        let name = libc::ptsname(master.as_raw_fd());
        if name.is_null() {
            return Err("ptsname failed".into());
        }
        let path = CStr::from_ptr(name).to_str().map_err(|_| "pty path")?.to_owned();
        Ok((master, path))
    }
}

pub fn set_window_size(master: RawFd, cols: u16, rows: u16) {
    let size = libc::winsize { ws_row: rows, ws_col: cols, ws_xpixel: 0, ws_ypixel: 0 };
    unsafe {
        libc::ioctl(master, libc::TIOCSWINSZ as _, &size);
    }
}

fn passwd(name: &str) -> Option<(u32, u32)> {
    let c = CString::new(name).ok()?;
    let pw = unsafe { libc::getpwnam(c.as_ptr()) };
    if pw.is_null() {
        return None;
    }
    unsafe { Some(((*pw).pw_uid, (*pw).pw_gid)) }
}

pub fn uid_of(name: &str) -> Option<u32> {
    passwd(name).map(|(uid, _)| uid)
}

fn group_gid(name: &str) -> Option<u32> {
    let c = CString::new(name).ok()?;
    let gr = unsafe { libc::getgrnam(c.as_ptr()) };
    if gr.is_null() {
        return None;
    }
    unsafe { Some((*gr).gr_gid) }
}

fn in_group(account: &str, primary: u32, gid: u32) -> bool {
    if primary == gid {
        return true;
    }
    let Ok(c) = CString::new(HOSTED_GROUP) else { return false };
    let gr = unsafe { libc::getgrnam(c.as_ptr()) };
    if gr.is_null() {
        return false;
    }
    let mut members = unsafe { (*gr).gr_mem };
    unsafe {
        while !(*members).is_null() {
            if CStr::from_ptr(*members).to_str() == Ok(account) {
                return true;
            }
            members = members.add(1);
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Write};
    use std::os::unix::fs::PermissionsExt;

    fn dev(dir: &Path) -> Spawner {
        // A dev wrapper that proves the pty: prints the args and echoes one line.
        let wrapper = dir.join("wrapper.sh");
        fs::write(&wrapper, "#!/bin/sh\necho \"args $# tty=$( [ -t 0 ] && echo yes || echo no ) term=$TERM\"\nread -r line\necho \"got $line\"\n").unwrap();
        fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o700)).unwrap();
        let config = dir.join("dev.json");
        fs::write(&config, serde_json::json!({
            "mini": "/bin/true", "host": "/bin/true", "config": "/dev/null", "socket": "/dev/null",
            "wrapper": wrapper, "sessions": {"alice": {"workspace": dir.join("ws"), "home": dir}},
            "public": {"workspace": dir.join("pws"), "home": dir}, "publicSubject": "4242"
        }).to_string()).unwrap();
        Spawner { layout: Layout::Dev(DevConfig::load(&config).unwrap()) }
    }

    fn scratch() -> PathBuf {
        let dir = std::env::temp_dir().join(format!("mini-web-spawn-{}-{}", std::process::id(), crate::new_token().unwrap()));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn delegated_consent_env_only_beside_a_consent_socket_and_pins_both_digests() {
        use sha2::{Digest, Sha256};
        // Short on purpose: the scratch binds a Unix socket, and macOS caps its path at 104 bytes.
        let dir = std::env::temp_dir().join(format!("mws-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        let bin = dir.join("bin");
        fs::create_dir_all(&bin).unwrap();
        fs::write(bin.join("minidregg-client-consent"), b"provider").unwrap();
        fs::write(dir.join("config.json"), b"{}").unwrap();
        let (mini, host, config) = (bin.join("mini"), bin.join("minidregg-host"), dir.join("config.json"));
        let home = dir.join("h");
        fs::create_dir_all(home.join("consent")).unwrap();
        assert!(delegated_consent_env(&mini, &host, &config, &home).unwrap().is_empty(), "no socket: no delegation");
        fs::write(home.join("consent/peer.sock"), b"").unwrap();
        assert!(delegated_consent_env(&mini, &host, &config, &home).unwrap().is_empty(), "a regular file is no socket");
        fs::remove_file(home.join("consent/peer.sock")).unwrap();
        let _listener = std::os::unix::net::UnixListener::bind(home.join("consent/peer.sock")).unwrap();
        let env: BTreeMap<_, _> = delegated_consent_env(&mini, &host, &config, &home).unwrap().into_iter().collect();
        let hex = |b: &[u8]| Sha256::digest(b).iter().map(|x| format!("{x:02x}")).collect::<String>();
        assert_eq!(env.len(), 7);
        assert_eq!(env["MINI_CONSENT_SOCKET"], home.join("consent/peer.sock").display().to_string());
        assert_eq!(env["MINI_CONSENT_PEER_UID"], "0");
        assert_eq!(env["MINI_CONSENT_SHA256"], hex(b"provider"));
        assert_eq!(env["MINI_CONSENT_CONFIG_SHA256"], hex(b"{}"));
        assert_eq!(env["MINI_LOCAL_HOST"], host.display().to_string());
        assert_eq!(env["MINI_CONSENT_HOST"], bin.join("minidregg-client-consent").display().to_string());
        assert_eq!(env["MINI_CONSENT_CONFIG"], config.display().to_string());
        fs::remove_file(bin.join("minidregg-client-consent")).unwrap();
        assert!(delegated_consent_env(&mini, &host, &config, &home).is_err(), "a socket without its provider refuses");
    }

    #[test]
    fn front_doc_is_one_reference_name_or_no_setting() {
        assert_eq!(front_doc_name("welcome\n").as_deref(), Some("welcome"));
        for bad in ["", "  ", "../etc/passwd", "a b", "doc/x", &"x".repeat(65)] {
            assert_eq!(front_doc_name(bad), None, "{bad:?}");
        }
        let dir = scratch();
        let layout = BoxLayout { root: dir.clone() };
        let spawner = Spawner { layout: Layout::Box(layout.clone()) };
        assert_eq!(spawner.front_doc(), None, "absent file: the index");
        fs::create_dir_all(layout.front_doc_file().parent().unwrap()).unwrap();
        fs::write(layout.front_doc_file(), "welcome\n").unwrap();
        assert_eq!(spawner.front_doc().as_deref(), Some("welcome"));
        fs::write(layout.front_doc_file(), "../welcome").unwrap();
        assert_eq!(spawner.front_doc(), None, "not a reference name: the index");
        assert_eq!(dev(&dir).front_doc(), None, "dev config without frontDoc");
    }

    #[test]
    fn a_house_name_is_handed_over_only_from_its_member() {
        let house = house_publications("welcome house\noperations box\n# a comment line\nbad name x\nnews public\nlobby Alice\n");
        assert_eq!(house.len(), 2, "{house:?}");
        let front = Some("welcome");
        assert_eq!(handed_name("welcome", "house", front, &house), "welcome");
        assert_eq!(handed_name("operations", "box", front, &house), "operations");
        // Teeth: another member's document of a house name is its own name.
        assert_eq!(handed_name("welcome", "sage", front, &house), "welcome-sage");
        assert_eq!(handed_name("operations", "house", front, &house), "operations-house");
        assert_eq!(handed_name("notes", "sage", front, &house), "notes");
        // No operator file: the front page's document and the operations room are nobody's.
        let none = BTreeMap::new();
        assert_eq!(handed_name("welcome", "house", front, &none), "welcome-house");
        assert_eq!(handed_name("operations", "box", None, &none), "operations-box");
        assert_eq!(handed_name("welcome", "house", None, &none), "welcome");
        let long = "d".repeat(64);
        let house = house_publications(&format!("{long} house"));
        assert_eq!(handed_name(&long, "sage", None, &house), "m-sage");
        let dir = scratch();
        let layout = BoxLayout { root: dir.clone() };
        let spawner = Spawner { layout: Layout::Box(layout.clone()) };
        assert!(spawner.house_publications().is_empty(), "absent file");
        fs::create_dir_all(layout.house_publications_file().parent().unwrap()).unwrap();
        fs::write(layout.house_publications_file(), "welcome house\n").unwrap();
        assert_eq!(spawner.house_publications().get("welcome").map(String::as_str), Some("house"));
    }

    #[test]
    fn dev_shell_runs_the_wrapper_under_a_pty() {
        let dir = scratch();
        let spawner = dev(&dir);
        let member = spawner.member("alice").unwrap();
        assert!(spawner.member("mallory").is_err());
        assert!(spawner.member("Alice").is_err());
        assert!(spawner.public().unwrap().anonymous);
        assert_eq!(spawner.public_subject().as_deref(), Some("4242"));
        assert_eq!(spawner.homes().len(), 1);
        let (pid, master) = spawner.shell(&member, "test", 80, 24).unwrap();
        assert!(pid > 0);
        let mut file = fs::File::from(master);
        file.write_all(b"hello\n").unwrap();
        let mut out = String::new();
        let mut buffer = [0u8; 4096];
        let deadline = std::time::Instant::now() + std::time::Duration::from_secs(10);
        while std::time::Instant::now() < deadline && !out.contains("got hello") {
            match file.read(&mut buffer) {
                Ok(0) => break,
                Ok(n) => out.push_str(&String::from_utf8_lossy(&buffer[..n])),
                Err(_) => break,
            }
        }
        assert!(out.contains("args 6 tty=yes term=xterm-256color"), "{out}");
        assert!(out.contains("got hello"), "{out}");
        unsafe { libc::waitpid(pid as i32, std::ptr::null_mut(), 0) };
    }

    #[test]
    fn box_layout_refuses_without_split_tenancy() {
        let dir = scratch();
        let spawner = Spawner { layout: Layout::Box(BoxLayout { root: dir.clone() }) };
        assert_eq!(spawner.member("alice").unwrap_err(), "only under split tenancy");
        fs::create_dir_all(dir.join("etc/mini")).unwrap();
        fs::write(dir.join("etc/mini/tenancy"), "split\n").unwrap();
        // No such account on a Mac or a build box: the next refusal is the account's.
        let why = spawner.member("alice").unwrap_err();
        assert!(why.contains("no account mini-s-alice") || why.contains(HOSTED_GROUP) || why.contains("0700 home"), "{why}");
    }
}
