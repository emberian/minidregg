//! `mini-web-spawn`: the web front end's one privileged process (docs/WEB-FRONTEND-2026-10-27.md
//! §2). Root, synchronous, one request per connection on a Unix socket only the gateway's uid may
//! open. It consumes the login codes the door wrote, mints sessions, and spawns `mini shell` (under a
//! pty) and `mini web --body` (on a root-only listener) as the member, through the same line
//! `mini-session-run` uses. It refuses everything else.
//!
//!   mini-web-spawn --socket /run/mini-web-spawn.sock --state /var/lib/mini-web-spawn \
//!                  --run /run/mini-web-spawn [--gateway mini-web]
//!   mini-web-spawn --dev CONFIG.json --socket S --state DIR --run DIR     (no root; the journey)
//!
//! Under systemd the socket may be inherited (`LISTEN_FDS=1`, mini-web-spawn.socket). A body or
//! shell this helper started is stopped by the pid in the session record, and only that.

// print!/println!/eprint!/eprintln!: a closed standard output ends the command with 141, never a
// panic (`mini_streams`).
#[macro_use]
extern crate mini_streams;
use std::fs;
use std::io::{Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::os::unix::net::{UnixListener, UnixStream};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use mini_web_spawn::spawn::{self, BoxLayout, DevConfig, Layout, Member, Spawner};
use mini_web_spawn::store::{Session, Store};
use mini_web_spawn::{parse_request, read_line, send_with_fd, Request, MAX_SHELLS_PER_SESSION};

struct Helper {
    store: Store,
    spawner: Spawner,
    run: PathBuf,
    gateway_uid: u32,
    dev: bool,
    /// The bodies THIS process spawned and has not reaped. A pid in a session record is never
    /// trusted on its own: after a helper restart (or a fresh run directory) the recorded pid may
    /// be another process, and connecting to a listener that no longer exists stranded the front
    /// page (dregg-build 2026-10-27: `connect body: No such file or directory`).
    children: std::collections::HashSet<u32>,
    /// Why the last publication hand-off could not run, said once on the operator's log until it changes.
    collect_blocked: Option<String>,
    /// The live public body this helper started, while it lives (see [`Helper::warm_public`]).
    public: Option<PublicBody>,
}

/// The public reader's body: its pid, the basis it was started from (`Spawner::public_basis`),
/// and its warming request's state ([`WARMING`], [`WARM`] or [`COLD`]) with how many were sent.
struct PublicBody {
    pid: u32,
    basis: String,
    warm: Option<Arc<AtomicU8>>,
    tries: u32,
}

const WARMING: u8 = 0;
const WARM: u8 = 1;
const COLD: u8 = 2;
/// A warming request that did not answer 200 is sent again at the next sweeps, this many in all.
const WARM_TRIES: u32 = 5;
/// The warming request waits longer than the gateway's 120 s: it is the one meant to be slow.
const WARM_DEADLINE: Duration = Duration::from_secs(600);

fn run_main() {
    if let Err(error) = run() {
        eprintln!("mini-web-spawn: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    let (mut socket, mut state, mut run, mut dev, mut gateway) = (None, None, None, None, "mini-web".to_owned());
    while let Some(flag) = args.next() {
        let value = args.next().ok_or_else(|| format!("{flag} takes a value"))?;
        match flag.as_str() {
            "--socket" => socket = Some(PathBuf::from(value)),
            "--state" => state = Some(PathBuf::from(value)),
            "--run" => run = Some(PathBuf::from(value)),
            "--dev" => dev = Some(PathBuf::from(value)),
            "--gateway" => gateway = value,
            other => return Err(format!("unknown option {other}")),
        }
    }
    let state = state.ok_or("--state DIR is required")?;
    let run = run.ok_or("--run DIR is required")?;
    let (layout, gateway_uid) = match dev {
        Some(config) => (Layout::Dev(DevConfig::load(&config)?), unsafe { libc::getuid() }),
        None => {
            if unsafe { libc::getuid() } != 0 {
                return Err("must run as root (or with --dev CONFIG.json)".into());
            }
            let uid = spawn::uid_of(&gateway).ok_or_else(|| format!("no account {gateway} (the gateway's uid)"))?;
            (Layout::Box(BoxLayout { root: PathBuf::from("/") }), uid)
        }
    };
    fs::create_dir_all(run.join("bodies")).map_err(|e| format!("{}: {e}", run.display()))?;
    fs::set_permissions(&run, fs::Permissions::from_mode(0o700)).map_err(|e| e.to_string())?;
    fs::set_permissions(run.join("bodies"), fs::Permissions::from_mode(0o700)).map_err(|e| e.to_string())?;
    let listener = match inherited_listener() {
        Some(listener) => listener,
        None => {
            let path = socket.ok_or("--socket PATH is required without LISTEN_FDS")?;
            let _ = fs::remove_file(&path);
            let listener = UnixListener::bind(&path).map_err(|e| format!("bind {}: {e}", path.display()))?;
            // The gateway's group opens it; the unit sets the group. In dev the user owns it.
            fs::set_permissions(&path, fs::Permissions::from_mode(if layout_is_dev(&layout) { 0o600 } else { 0o660 })).map_err(|e| e.to_string())?;
            listener
        }
    };
    listener.set_nonblocking(true).map_err(|e| e.to_string())?;
    let mut helper = Helper { store: Store::open(&state)?, spawner: Spawner { layout }, run, gateway_uid, dev: false, children: Default::default(), collect_blocked: None, public: None };
    helper.dev = layout_is_dev(&helper.spawner.layout);
    helper.forget_bodies();
    helper.warm_public();
    eprintln!("mini-web-spawn: serving (gateway uid {gateway_uid}{})", if helper.dev { ", dev" } else { "" });
    let mut last_sweep = std::time::Instant::now();
    loop {
        match listener.accept() {
            // BSD sockets inherit the listener's O_NONBLOCK; the request is read blocking, bounded by its timeouts.
            Ok((stream, _)) => {
                let _ = stream.set_nonblocking(false);
                helper.serve(stream)
            }
            Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                let mut pfd = libc::pollfd { fd: listener.as_raw_fd(), events: libc::POLLIN, revents: 0 };
                unsafe { libc::poll(&mut pfd, 1, 1000) };
            }
            Err(e) => eprintln!("mini-web-spawn: accept: {e}"),
        }
        helper.reap();
        if last_sweep.elapsed() > Duration::from_secs(60) {
            helper.sweep();
            helper.collect();
            helper.warm_public();
            last_sweep = std::time::Instant::now();
        }
    }
}

fn layout_is_dev(layout: &Layout) -> bool {
    matches!(layout, Layout::Dev(_))
}

fn inherited_listener() -> Option<UnixListener> {
    let fds: u32 = std::env::var("LISTEN_FDS").ok()?.parse().ok()?;
    if fds != 1 {
        return None;
    }
    Some(unsafe { UnixListener::from_raw_fd(3) })
}

/// The connecting process's uid (`SO_PEERCRED` on Linux, `getpeereid` elsewhere).
fn peer_uid(stream: &UnixStream) -> Option<u32> {
    #[cfg(target_os = "linux")]
    unsafe {
        let mut cred: libc::ucred = std::mem::zeroed();
        let mut len = std::mem::size_of::<libc::ucred>() as libc::socklen_t;
        if libc::getsockopt(stream.as_raw_fd(), libc::SOL_SOCKET, libc::SO_PEERCRED, &mut cred as *mut _ as *mut _, &mut len) != 0 {
            return None;
        }
        Some(cred.uid)
    }
    #[cfg(not(target_os = "linux"))]
    unsafe {
        let (mut uid, mut gid) = (0u32, 0u32);
        if libc::getpeereid(stream.as_raw_fd(), &mut uid, &mut gid) != 0 {
            return None;
        }
        Some(uid)
    }
}

impl Helper {
    fn serve(&mut self, mut stream: UnixStream) {
        let _ = stream.set_read_timeout(Some(Duration::from_secs(5)));
        let _ = stream.set_write_timeout(Some(Duration::from_secs(5)));
        let (text, fd) = match self.handle(&mut stream) {
            Ok((text, fd)) => (format!("ok{text}\n"), fd),
            Err(why) if why.starts_with("spawn ") || why.starts_with("connect body") || why.starts_with("bind body") => {
                eprintln!("mini-web-spawn: ERROR: {why}");
                (format!("error {why}\n"), None)
            }
            Err(why) => {
                eprintln!("mini-web-spawn: REFUSED: {why}");
                (format!("refused {why}\n"), None)
            }
        };
        if let Err(e) = send_with_fd(&stream, text.as_bytes(), fd.as_ref().map(|f| f.as_raw_fd())) {
            eprintln!("mini-web-spawn: answer: {e}");
        }
        let _ = stream.flush();
    }

    fn handle(&mut self, stream: &mut UnixStream) -> Result<(String, Option<OwnedFd>), String> {
        match peer_uid(stream) {
            Some(uid) if uid == self.gateway_uid => {}
            Some(uid) => return Err(format!("peer uid {uid} is not the gateway")),
            None => return Err("cannot read the peer's credentials".into()),
        }
        let line = read_line(stream).map_err(|e| e.to_string())?;
        match parse_request(&line)? {
            Request::Login { code } => {
                let name = self.store.consume_login(&code)?;
                let member = self.spawner.member(&name)?;
                let (sid, session) = self.store.create(&name)?;
                eprintln!("mini-web-spawn: session {} opened for {}", session.prefix(), member.account);
                Ok((format!(" {sid} {} {} {}", session.name, session.csrf, session.expires), None))
            }
            Request::Who { sid } => {
                let session = self.store.touch(&sid)?;
                Ok((format!(" {} {} {}", session.name, session.csrf, session.expires), None))
            }
            Request::Shell { sid, cols, rows } => {
                let mut session = self.store.touch(&sid)?;
                let member = self.spawner.member(&session.name)?;
                session.shells.retain(|pid| alive(*pid));
                if session.shells.len() >= MAX_SHELLS_PER_SESSION {
                    return Err(format!("this session already has {MAX_SHELLS_PER_SESSION} shells"));
                }
                let unit = format!("mini-web-term-{}-{}", session.prefix(), mini_web_spawn::now());
                let (pid, master) = self.spawner.shell(&member, &unit, cols, rows)?;
                session.shells.push(pid);
                self.store.save(&session)?;
                Ok((format!(" {pid}"), Some(master)))
            }
            Request::Body { sid } => {
                let (mut session, member) = match sid {
                    Some(sid) => {
                        let session = self.store.touch(&sid)?;
                        let member = self.spawner.member(&session.name)?;
                        (session, member)
                    }
                    None => {
                        let (mut session, member) = (self.store.public(), self.spawner.public()?);
                        self.retire_stale_public(&mut session, &member);
                        (session, member)
                    }
                };
                let stream = self.body(&mut session, &member)?;
                Ok((String::new(), Some(OwnedFd::from(stream))))
            }
            Request::Logout { sid } => {
                let session = self.store.touch(&sid)?;
                self.end(&session);
                Ok((String::new(), None))
            }
            Request::Sessions { sid } => {
                let me = self.store.touch(&sid)?;
                let all = self.store.for_name(&me.name);
                let mut text = format!(" {}", all.len());
                for s in all {
                    text.push_str(&format!("\n{} {} {} {}", s.prefix(), s.created, s.last_seen, u8::from(s.hash == me.hash)));
                }
                Ok((text, None))
            }
            Request::Revoke { sid, prefix } => {
                let me = self.store.touch(&sid)?;
                let target = self.store.for_name(&me.name).into_iter().find(|s| s.prefix() == prefix).ok_or("no session of yours has that prefix")?;
                self.end(&target);
                Ok((String::new(), None))
            }
        }
    }

    /// A fresh helper has no children: every recorded body pid is stale. A body that outlived its
    /// helper is ended if it is still ours by command line (Linux), and every record forgets it.
    fn forget_bodies(&mut self) {
        let mut sessions = self.store.all();
        sessions.push(self.store.public());
        for mut s in sessions {
            if let Some(pid) = s.body_pid.take() {
                #[cfg(target_os = "linux")]
                {
                    let ours = fs::read(format!("/proc/{pid}/cmdline")).map(|c| String::from_utf8_lossy(&c).contains("web\0--body")).unwrap_or(false);
                    if ours {
                        unsafe { libc::kill(pid as i32, libc::SIGTERM) };
                        eprintln!("mini-web-spawn: body {pid} from an earlier helper ended");
                    }
                }
                let _ = self.store.save(&s);
            }
        }
    }

    /// A connected stream to the session's body, spawning it on its root-only listener first if
    /// it is not one this helper started and still serving.
    fn body(&mut self, session: &mut Session, member: &Member) -> Result<UnixStream, String> {
        let path = self.body_path(session);
        if !self.live(session) {
            let _ = fs::remove_file(&path);
            let listener = UnixListener::bind(&path).map_err(|e| format!("bind body listener: {e}"))?;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o600)).map_err(|e| e.to_string())?;
            let listener = OwnedFd::from(listener);
            let unit = format!("mini-web-body-{}", session.prefix());
            let pid = self.spawner.body(member, &unit, &listener)?;
            self.children.insert(pid);
            session.body_pid = Some(pid);
            self.store.save(session)?;
            if member.anonymous {
                self.public = Some(PublicBody { pid, basis: self.spawner.public_basis(member), warm: None, tries: 0 });
            }
            eprintln!("mini-web-spawn: body {pid} started for {}", member.account);
            // The listener lives in the body now; the kernel queues our connect until it accepts.
        }
        UnixStream::connect(&path).map_err(|e| format!("connect body: {e}"))
    }

    fn body_path(&self, session: &Session) -> PathBuf {
        self.run.join("bodies").join(format!("{}.sock", &session.hash[..16.min(session.hash.len())]))
    }

    /// The session's body is one this helper started, still running, with its listener in place.
    fn live(&self, session: &Session) -> bool {
        session.body_pid.is_some_and(|pid| self.children.contains(&pid) && alive(pid)) && self.body_path(session).exists()
    }

    /// The public reader is the one body every anonymous visitor shares, and its first request is
    /// the expensive one: the body starts, and its delegated consent worker (mini-consent@public,
    /// socket-activated, idle-exiting) replays the Store before it answers. demo-dry 2026-10-28
    /// (349e59ef1): 8.3 s with the worker warm, 23 s with both cold on an idle box, the gateway's
    /// 504 at 120 s with load on top. So it is paid before any visitor: at the helper's start and at
    /// every sweep, when the reader is enrolled and no live public body answers from the current
    /// basis, the helper starts the body and sends it one `GET /`, the front page's own request
    /// (its signed read opens the consent connection, so the worker is started and has replayed).
    /// A warming request that fails is sent again at the next sweeps, [`WARM_TRIES`] in all.
    /// This warms each start; whether the worker stays warm afterwards is its idle setting's.
    fn warm_public(&mut self) {
        if self.spawner.public_subject().is_none() {
            return;
        }
        let Ok(member) = self.spawner.public() else { return };
        let mut session = self.store.public();
        self.retire_stale_public(&mut session, &member);
        if self.live(&session) {
            let retry = self.public.as_ref().is_some_and(|p| {
                p.pid == session.body_pid.unwrap_or(0) && p.tries < WARM_TRIES && p.warm.as_ref().is_some_and(|w| w.load(Ordering::Acquire) == COLD)
            });
            if retry {
                match UnixStream::connect(self.body_path(&session)) {
                    Ok(stream) => self.send_warm(stream),
                    Err(e) => eprintln!("mini-web-spawn: public reader not warmed: connect body: {e}"),
                }
            }
            return;
        }
        match self.body(&mut session, &member) {
            Ok(stream) => self.send_warm(stream),
            Err(e) => eprintln!("mini-web-spawn: public reader not warmed: {e}"),
        }
    }

    /// One `GET /` to the public body on its own thread (the helper serves on); its outcome is
    /// logged and kept for [`Helper::warm_public`]'s retry.
    fn send_warm(&mut self, mut stream: UnixStream) {
        let Some(public) = self.public.as_mut() else { return };
        let state = Arc::new(AtomicU8::new(WARMING));
        public.warm = Some(state.clone());
        public.tries += 1;
        let pid = public.pid;
        std::thread::spawn(move || {
            let began = Instant::now();
            let answer = (|| -> std::io::Result<String> {
                stream.set_read_timeout(Some(WARM_DEADLINE))?;
                stream.set_write_timeout(Some(Duration::from_secs(10)))?;
                stream.write_all(b"GET / HTTP/1.1\r\nHost: mini-body\r\nX-Mini-Fragment: 1\r\nContent-Length: 0\r\n\r\n")?;
                let mut bytes = Vec::new();
                (&mut stream).take(8 * 1024 * 1024).read_to_end(&mut bytes)?;
                let line = bytes.split(|b| *b == b'\r').next().unwrap_or_default();
                Ok(String::from_utf8_lossy(line).into_owned())
            })();
            let secs = began.elapsed().as_secs_f64();
            match answer {
                Ok(line) if line.starts_with("HTTP/1.1 200 ") => {
                    state.store(WARM, Ordering::Release);
                    eprintln!("mini-web-spawn: public reader warmed (body {pid}): {line} in {secs:.1} s");
                }
                Ok(line) => {
                    state.store(COLD, Ordering::Release);
                    eprintln!("mini-web-spawn: public reader not warmed (body {pid}): answered {line:?} in {secs:.1} s");
                }
                Err(e) => {
                    state.store(COLD, Ordering::Release);
                    eprintln!("mini-web-spawn: public reader not warmed (body {pid}): {e} after {secs:.1} s");
                }
            }
        });
    }

    /// End the live public body when its basis is not the current one (a re-enrolled reader, a new
    /// front document, a re-initialised workspace, a re-genesis, a switched candidate), by the pid
    /// this helper recorded when it started it; the next request or sweep starts a current one.
    fn retire_stale_public(&mut self, session: &mut Session, member: &Member) {
        let Some(public) = self.public.as_ref() else { return };
        if session.body_pid != Some(public.pid) || !self.live(session) {
            return;
        }
        if public.basis == self.spawner.public_basis(member) {
            return;
        }
        let pid = public.pid;
        unsafe { libc::kill(pid as i32, libc::SIGTERM) };
        let _ = fs::remove_file(self.body_path(session));
        session.body_pid = None;
        let _ = self.store.save(session);
        self.public = None;
        eprintln!("mini-web-spawn: public body {pid} ended: its basis changed");
    }

    /// End a session: its body and shells by their recorded pids, then the record.
    fn end(&mut self, session: &Session) {
        if let Some(pid) = session.body_pid {
            unsafe { libc::kill(pid as i32, libc::SIGTERM) };
        }
        for pid in &session.shells {
            unsafe { libc::kill(*pid as i32, libc::SIGHUP) };
        }
        let _ = fs::remove_file(self.run.join("bodies").join(format!("{}.sock", &session.hash[..16.min(session.hash.len())])));
        self.store.delete(&session.hash);
        eprintln!("mini-web-spawn: session {} ended", session.prefix());
    }

    fn reap(&mut self) {
        loop {
            let pid = unsafe { libc::waitpid(-1, std::ptr::null_mut(), libc::WNOHANG) };
            if pid <= 0 {
                break;
            }
            let pid = pid as u32;
            self.children.remove(&pid);
            if self.public.as_ref().is_some_and(|p| p.pid == pid) {
                self.public = None;
            }
            let mut sessions = self.store.all();
            sessions.push(self.store.public());
            for mut s in sessions {
                let had_body = s.body_pid == Some(pid);
                let had_shell = s.shells.contains(&pid);
                if had_body {
                    s.body_pid = None;
                }
                s.shells.retain(|p| *p != pid);
                if had_body || had_shell {
                    let _ = self.store.save(&s);
                }
            }
        }
    }

    /// The publication hand-off: every member's `proposals/*/recipient-reference.json` addressed to
    /// the public subject is copied into the public reader's `inbox/NAME.TARGET.json` (owned by
    /// the public member, 0600). Nothing is decided here: the reference is a hint, and the public
    /// body's own signed read publishes or refuses the document. The one thing only this helper
    /// knows is which member's home a publication came from, so it alone hands over a house name
    /// (`spawn::handed_name`): the front page and the operations room come only from the member
    /// the operator named for them.
    fn collect(&mut self) {
        let Some(subject) = self.spawner.public_subject() else {
            return self.hand_off_blocked("the public reader is not enrolled (no public subject): publications are not handed to it".into());
        };
        let public = match self.spawner.public() {
            Ok(public) => public,
            Err(error) => return self.hand_off_blocked(format!("the public reader is unavailable: {error}")),
        };
        let inbox = public.home.join("inbox");
        if let Err(error) = fs::create_dir_all(&inbox) {
            return self.hand_off_blocked(format!("the public reader's inbox {}: {error}", inbox.display()));
        }
        self.collect_blocked = None;
        let _ = fs::set_permissions(&inbox, fs::Permissions::from_mode(0o700));
        if !self.dev {
            unsafe { libc::chown(std::ffi::CString::new(inbox.to_string_lossy().as_bytes()).unwrap().as_ptr(), public.uid, u32::MAX) };
        }
        let front_doc = self.spawner.front_doc();
        let house = self.spawner.house_publications();
        for (name, home) in self.spawner.homes() {
            if name == spawn::PUBLIC_NAME {
                continue;
            }
            let Ok(proposals) = fs::read_dir(home.join("workspace/proposals")) else { continue };
            // Several publications of one document (published, revoked, published again) share the
            // inbox name NAME.TARGET: the newest one is handed over, whatever order the directory lists.
            let mut proposals: Vec<_> = proposals.flatten().collect();
            proposals.sort_by_key(|p| fs::metadata(p.path().join("recipient-reference.json")).and_then(|m| m.modified()).ok());
            let mut chosen: std::collections::BTreeMap<PathBuf, (String, String, Vec<u8>)> = std::collections::BTreeMap::new();
            for proposal in proposals {
                let reference = proposal.path().join("recipient-reference.json");
                let Ok(meta) = fs::symlink_metadata(&reference) else { continue };
                if !meta.is_file() || meta.len() > 65536 {
                    continue;
                }
                let Ok(value) = fs::read(&reference).ok().and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok()).ok_or(()) else { continue };
                let target = value["target"].as_str().unwrap_or("");
                if value["type"] != "minidregg-delegated-reference-v1" || value["recipient"] != subject.as_str() || target.is_empty() || !target.bytes().all(|b| b.is_ascii_digit()) {
                    continue;
                }
                let doc = fs::read(proposal.path().join("proposal.json")).ok().and_then(|b| serde_json::from_slice::<serde_json::Value>(&b).ok())
                    .and_then(|p| p["delegation"]["name"].as_str().map(str::to_owned))
                    .filter(|n| !n.is_empty() && n.len() <= 64 && n.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'-'))
                    .unwrap_or_else(|| "doc".into());
                let doc = spawn::handed_name(&doc, &name, front_doc.as_deref(), &house);
                let dest = inbox.join(format!("{doc}.{target}.json"));
                let bytes = fs::read(&reference).unwrap_or_default();
                chosen.insert(dest, (doc, target.to_owned(), bytes)); // oldest first: the newest stays
            }
            for (dest, (doc, target, bytes)) in chosen {
                if fs::read(&dest).ok().as_deref() == Some(bytes.as_slice()) {
                    continue;
                }
                let tmp = dest.with_extension("tmp");
                if let Ok(mut file) = fs::OpenOptions::new().write(true).create(true).truncate(true).mode(0o600).open(&tmp) {
                    let _ = file.write_all(&bytes);
                    if !self.dev {
                        unsafe { libc::fchown(std::os::fd::AsRawFd::as_raw_fd(&file), public.uid, u32::MAX) };
                    }
                    let _ = fs::rename(&tmp, &dest);
                    eprintln!("mini-web-spawn: publication {doc} ({target}) from {name} handed to the public reader");
                }
            }
        }
    }

    /// The hand-off runs every tick; a reason it cannot run is logged when it first appears or changes.
    fn hand_off_blocked(&mut self, why: String) {
        if self.collect_blocked.as_deref() != Some(why.as_str()) {
            eprintln!("mini-web-spawn: publication hand-off: {why}");
            self.collect_blocked = Some(why);
        }
    }

    fn sweep(&mut self) {
        for s in self.store.all() {
            if Store::is_expired(&s) {
                self.end(&s);
            }
        }
    }
}

fn alive(pid: u32) -> bool {
    unsafe { libc::kill(pid as i32, 0) == 0 }
}

fn main() -> std::process::ExitCode {
    mini_streams::guard(|| {
        run_main();
        std::process::ExitCode::SUCCESS
    })
}
