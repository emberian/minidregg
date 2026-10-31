//! One line through the ssh entrance's own forced command.
//!
//! Under split tenancy (dregg-infra `/etc/mini/tenancy` = split) every friend's
//! session is its own account (`mini-s-NAME`) and the entrance (account
//! `mini-discord`) cannot run anything as it. It hands the line to the root
//! runner over its socket (`MINI_SESSION_RUNNER`, a socket-activated
//! `mini-session-run@.service` whose socket only root and group `mini-discord`
//! may open): `NAME\nLINE\n` in, [`RUNNER_HEADER`] `EXIT OUTLEN ERRLEN\n` and the
//! two streams out. The runner checks NAME against the Discord roster and runs
//! the same forced command as that account. No setuid program is involved, so the
//! entrance keeps `NoNewPrivileges=yes` and `RestrictSUIDSGID=yes` under split
//! tenancy too. Without a runner (single tenancy, and the tests) the entrance runs
//! the forced command itself, as before.
//!
//! The entrance does not re-derive `mini shell`'s environment. It runs
//! `mini-shell-ssh MINI HOST CONFIG SOCKET WORKSPACE HOME` (the candidate's `mini-line`) with the line in
//! `SSH_ORIGINAL_COMMAND` (so the line is one argument to `mini shell --line`, never parsed
//! by a system shell) and an otherwise empty environment. WORKSPACE and HOME come from the
//! session NAME by `render-authorized-keys.sh`'s rule: HOME is `SESSIONS/NAME`; WORKSPACE is
//! the sponsor workspace for the sponsor and `HOME/workspace` for everyone else.

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::process::CommandExt;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::json;

use crate::reply::Ending;
use crate::roster::is_session_name;
use crate::{env_path, env_u64};

/// The longest line the entrance hands to the shell, in characters.
pub const MAX_LINE: usize = 1000;
/// Output kept from each stream of one line; the rest is dropped (the reply is 2000 chars).
pub const MAX_CAPTURE: usize = 1 << 20;

/// The deployment every session shares: the forced command and what it is given.
#[derive(Debug, Clone)]
pub struct Deployment {
    pub wrapper: PathBuf,
    pub mini: PathBuf,
    pub host: PathBuf,
    pub config: PathBuf,
    pub socket: PathBuf,
    pub timeout: Duration,
    /// The root runner's socket, which runs one line as a session's own account.
    /// None: the entrance shares the sessions' account and runs the wrapper itself.
    pub runner: Option<PathBuf>,
}

/// The first word of the runner's answer.
pub const RUNNER_HEADER: &str = "mini-session-run-v1";

impl Deployment {
    /// `MINI_SHELL_WRAPPER`, `MINI_CLIENT`, `MINI_HOST`, `MINI_CONFIG`, `MINI_SOCKET`
    /// (absolute paths) and `MINI_LINE_TIMEOUT_S` (default 120).
    pub fn from_env() -> Result<Self, String> {
        Ok(Deployment {
            wrapper: env_path("MINI_SHELL_WRAPPER")?,
            mini: env_path("MINI_CLIENT")?,
            host: env_path("MINI_HOST")?,
            config: env_path("MINI_CONFIG")?,
            socket: env_path("MINI_SOCKET")?,
            timeout: Duration::from_secs(env_u64("MINI_LINE_TIMEOUT_S", 120)?),
            runner: match std::env::var("MINI_SESSION_RUNNER") {
                Ok(v) if !v.is_empty() => Some(env_path("MINI_SESSION_RUNNER")?),
                _ => None,
            },
        })
    }

    /// Run one line in one session. Never fails: a spawn failure or a timeout is an ending.
    pub fn run(&self, session: &Session, line: &str) -> Outcome {
        if let Some(socket) = &self.runner {
            return self.run_by_runner(socket, session, line);
        }
        let mut cmd = Command::new(&self.wrapper);
        cmd.args([&self.mini, &self.host, &self.config, &self.socket, &session.workspace, &session.home])
            .stdin(Stdio::null());
        cmd.env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("LANG", "C.UTF-8")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            // Its own process group, so a timeout stops the Host children too.
            .process_group(0);
        cmd.env("SSH_ORIGINAL_COMMAND", line);
        let mut child = match cmd.spawn() {
            Ok(c) => c,
            Err(e) => {
                return Outcome::entrance(Ending::entrance(
                    "error",
                    &format!("the entrance could not start the session: {e}"),
                ))
            }
        };
        let out = capture(child.stdout.take());
        let err = capture(child.stderr.take());
        let started = Instant::now();
        let status = loop {
            match child.try_wait() {
                Ok(Some(s)) => break Some(s),
                Ok(None) if started.elapsed() >= self.timeout => {
                    unsafe { libc::killpg(child.id() as libc::pid_t, libc::SIGKILL) };
                    let _ = child.wait();
                    break None;
                }
                Ok(None) => std::thread::sleep(Duration::from_millis(25)),
                Err(_) => break None,
            }
        };
        let stdout = out.join().unwrap_or_default();
        let stderr = err.join().unwrap_or_default();
        let ending = match status {
            Some(s) => Ending::of_shell(s.code(), &stderr),
            None => self.undecided(),
        };
        Outcome { exit: status.and_then(|s| s.code()), stdout, stderr, ending }
    }

    fn undecided(&self) -> Ending {
        Ending::entrance(
            "undecided",
            &format!(
                "the line did not finish within {} s and was stopped; if it submitted, `lookup ID` asks the Host again",
                self.timeout.as_secs()
            ),
        )
    }

    /// The runner chooses the paths and the account from NAME alone; the line is data on the
    /// socket, never an argument and never a shell word. The runner bounds the line itself
    /// (its own timeout); the entrance waits that long plus a margin, and a missing answer is
    /// `undecided`, never a rerun.
    fn run_by_runner(&self, socket: &Path, session: &Session, line: &str) -> Outcome {
        let mut stream = match UnixStream::connect(socket) {
            Ok(s) => s,
            Err(e) => {
                return Outcome::entrance(Ending::entrance(
                    "error",
                    &format!("the session runner is unavailable ({e}); nothing ran"),
                ))
            }
        };
        let deadline = self.timeout + Duration::from_secs(15);
        let _ = stream.set_read_timeout(Some(deadline));
        let _ = stream.set_write_timeout(Some(Duration::from_secs(10)));
        if stream.write_all(format!("{}\n{line}\n", session.name).as_bytes()).is_err() {
            // The runner had already taken the connection (Linux answers a close-mid-send
            // with EPIPE, macOS with ENOTCONN; a write timeout is the third way). Whether
            // it took the line cannot be known, and a maybe is never rerun.
            return Outcome::entrance(Ending::entrance(
                "undecided",
                "the session runner did not take the whole line; it may have run, `lookup ID` asks the Host again",
            ));
        }
        let _ = stream.shutdown(std::net::Shutdown::Write);
        let mut answer = Vec::new();
        let read = Read::by_ref(&mut stream).take((2 * MAX_CAPTURE + 256) as u64).read_to_end(&mut answer);
        match (read, parse_runner_answer(&answer)) {
            (Ok(_), Some((exit, stdout, stderr))) => {
                let ending = Ending::of_shell(Some(exit), &stderr);
                Outcome { exit: Some(exit), stdout, stderr, ending }
            }
            // The runner took the line and gave no complete answer: it may have run.
            _ => Outcome::entrance(self.undecided()),
        }
    }
}

/// `mini-session-run-v1 EXIT OUTLEN ERRLEN\n` then exactly OUTLEN + ERRLEN bytes.
pub fn parse_runner_answer(answer: &[u8]) -> Option<(i32, String, String)> {
    let end = answer.iter().position(|b| *b == b'\n')?;
    let head = std::str::from_utf8(&answer[..end]).ok()?;
    let mut words = head.split(' ');
    if words.next()? != RUNNER_HEADER {
        return None;
    }
    let exit: i32 = words.next()?.parse().ok()?;
    let out: usize = words.next()?.parse().ok()?;
    let err: usize = words.next()?.parse().ok()?;
    if words.next().is_some() || out > MAX_CAPTURE || err > MAX_CAPTURE {
        return None;
    }
    let body = &answer[end + 1..];
    if body.len() != out + err {
        return None;
    }
    Some((
        exit,
        String::from_utf8_lossy(&body[..out]).into_owned(),
        String::from_utf8_lossy(&body[out..]).into_owned(),
    ))
}

/// How long and how many completed interaction custody records are kept.
#[derive(Debug, Clone, Copy)]
pub struct Retention {
    pub max_age_s: u64,
    pub max_records: usize,
}

/// Remove COMPLETED custody records older than the age bound, then the oldest completed ones
/// beyond the count bound (with their lease files). An accepted or started record is the
/// evidence of an undecided line and is never removed. Returns how many were removed.
pub fn prune_custody(dir: &Path, retention: &Retention, now: u64) -> Result<usize, String> {
    let Ok(entries) = std::fs::read_dir(dir) else { return Ok(0) };
    let mut completed = Vec::new();
    for entry in entries {
        let entry = entry.map_err(|e| e.to_string())?;
        let path = entry.path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let Ok(Some(value)) = mini_sdk::store::read_json(&path) else { continue };
        if value["phase"] == "completed" {
            completed.push((value["finishedAt"].as_u64().unwrap_or(0), path));
        }
    }
    completed.sort();
    let over = completed.len().saturating_sub(retention.max_records);
    let mut removed = 0;
    for (i, (at, path)) in completed.iter().enumerate() {
        if i < over || now.saturating_sub(*at) > retention.max_age_s {
            std::fs::remove_file(path).map_err(|e| format!("{}: {e}", path.display()))?;
            let _ = std::fs::remove_file(path.with_extension("lock"));
            removed += 1;
        }
    }
    Ok(removed)
}

/// At most `limit` bytes of `text`, cut on a character boundary, marked when cut.
pub fn bounded_text(text: &str, limit: usize) -> String {
    if text.len() <= limit {
        return text.to_owned();
    }
    let mut end = limit;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}\n[custody keeps the first {limit} bytes]", &text[..end])
}

fn capture<R: Read + Send + 'static>(r: Option<R>) -> std::thread::JoinHandle<String> {
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        let mut truncated=false;
        if let Some(mut r) = r {
            let mut chunk=[0u8;8192];
            loop {
                match r.read(&mut chunk) {
                    Ok(0) | Err(_) => break,
                    Ok(n) => {let keep=n.min(MAX_CAPTURE.saturating_sub(buf.len()));buf.extend_from_slice(&chunk[..keep]);truncated|=keep<n;}
                }
            }
        }
        let mut text=String::from_utf8_lossy(&buf).into_owned();
        if truncated{text.push_str("\n[entrance capture truncated at 1 MiB]\n");}
        text
    })
}

#[derive(Debug)]
pub struct Outcome {
    pub exit: Option<i32>,
    pub stdout: String,
    pub stderr: String,
    pub ending: Ending,
}

impl Outcome {
    fn entrance(ending: Ending) -> Self {
        Outcome { exit: None, stdout: String::new(), stderr: String::new(), ending }
    }
}

/// One session: the home and the workspace the forced command is given.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Session {
    pub name: String,
    pub home: PathBuf,
    pub workspace: PathBuf,
}

/// Where sessions live and who the sponsor is.
#[derive(Debug, Clone)]
pub struct Sessions {
    pub dir: PathBuf,
    pub sponsor: String,
    pub sponsor_workspace: PathBuf,
}

impl Sessions {
    /// `MINI_SESSIONS` (default layout `/var/lib/mini/sessions`), `MINI_SPONSOR` and
    /// `MINI_SPONSOR_WORKSPACE`.
    pub fn from_env() -> Result<Self, String> {
        let sponsor = crate::env_required("MINI_SPONSOR")?;
        if !is_session_name(&sponsor) {
            return Err("MINI_SPONSOR is not a session name".into());
        }
        Ok(Sessions {
            dir: env_path("MINI_SESSIONS")?,
            sponsor,
            sponsor_workspace: env_path("MINI_SPONSOR_WORKSPACE")?,
        })
    }

    /// The session NAME, whose home must already exist (the friends roster renderer makes
    /// it). The entrance never creates a session.
    pub fn open(&self, name: &str) -> Result<Session, String> {
        if !is_session_name(name) {
            return Err(format!("{name:?} is not a session name"));
        }
        let home = self.dir.join(name);
        match std::fs::symlink_metadata(&home) {
            Ok(m) if m.is_dir() => {}
            _ => return Err(format!("session {name} has no home on this box yet; ember must add it to the friends roster")),
        }
        let workspace = if name == self.sponsor { self.sponsor_workspace.clone() } else { home.join("workspace") };
        Ok(Session { name: name.to_string(), home, workspace })
    }
}

/// The entrance's own checks on a line before any session runs it. `Err` is the text of a
/// `usage:` ending.
pub fn check_line(line: &str) -> Result<(), String> {
    let n = line.chars().count();
    if n > MAX_LINE {
        return Err(format!("the line is {n} characters; the limit is {MAX_LINE}"));
    }
    if line.trim().is_empty() {
        return Err("the line is empty; try /mini-help".into());
    }
    if line.chars().any(char::is_control) {
        return Err("the line contains a control character; one line only".into());
    }
    Ok(())
}

/// A line log is rotated to `<file>.1` (one generation) once it passes this size.
pub const MAX_LOG: u64 = 1 << 20;

/// Append one record to `HOME/<file>` (created 0600), rotating it past [`MAX_LOG`].
pub fn append_log(home: &Path, file: &str, record: &serde_json::Value) -> std::io::Result<()> {
    let path = home.join(file);
    if std::fs::symlink_metadata(&path).is_ok_and(|m| m.is_file() && m.len() > MAX_LOG) {
        std::fs::rename(&path, home.join(format!("{file}.1")))?;
    }
    let mut f = OpenOptions::new().create(true).append(true).mode(0o600).open(home.join(file))?;
    let mut line = serde_json::to_vec(record)?;
    line.push(b'\n');
    f.write_all(&line)
}

/// The `discord.log` record for one line: who, what, how it ended.
pub fn log_record(at: u64, user: &str, interaction: &str, line: &str, ending: &Ending, exit: Option<i32>) -> serde_json::Value {
    json!({
        "at": at,
        "discord_user": user,
        "interaction": interaction,
        "line": line,
        "ending": ending.word,
        "ending_line": ending.line,
        "exit": exit,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_checks() {
        assert!(check_line("read shared").is_ok());
        assert!(check_line(&"a".repeat(MAX_LINE)).is_ok());
        assert_eq!(
            check_line(&"a".repeat(MAX_LINE + 1)).unwrap_err(),
            "the line is 1001 characters; the limit is 1000"
        );
        assert!(check_line("   ").is_err());
        assert!(check_line("read a\nexit").is_err());
        assert!(check_line("read a\u{7}").is_err());
    }

    #[test]
    fn the_runner_answer_is_exact_or_undecided() {
        let ok = format!("{RUNNER_HEADER} 3 5 7\nhello\nerror:");
        let (exit, out, err) = parse_runner_answer(ok.as_bytes()).unwrap();
        assert_eq!((exit, out.as_str(), err.as_str()), (3, "hello", "\nerror:"));
        for bad in [
            format!("{RUNNER_HEADER} 0 5 0\nhel"),
            format!("{RUNNER_HEADER} 0 1 0\nab"),
            format!("other 0 0 0\n"),
            format!("{RUNNER_HEADER} 0 0\n"),
            format!("{RUNNER_HEADER} 0 99999999 0\n"),
            String::new(),
        ] {
            assert!(parse_runner_answer(bad.as_bytes()).is_none(), "{bad:?}");
        }
    }

    #[test]
    fn a_runner_socket_carries_name_and_line_and_its_answer() {
        let dir = std::env::temp_dir().join(format!("runner-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let socket = dir.join("s");
        let listener = std::os::unix::net::UnixListener::bind(&socket).unwrap();
        let server = std::thread::spawn(move || {
            let (mut s, _) = listener.accept().unwrap();
            let mut got = String::new();
            s.read_to_string(&mut got).unwrap();
            assert_eq!(got, "alice\nread shared\n");
            s.write_all(format!("{RUNNER_HEADER} 0 3 0\nok\n").as_bytes()).unwrap();
            drop(s);
            // A second connection that answers nothing: the line may have run.
            let (s, _) = listener.accept().unwrap();
            drop(s);
        });
        let d = Deployment { wrapper: "/x".into(), mini: "/x".into(), host: "/x".into(), config: "/x".into(),
            socket: "/x".into(), timeout: Duration::from_secs(2), runner: Some(socket) };
        let session = Session { name: "alice".into(), home: "/h".into(), workspace: "/h/workspace".into() };
        let o = d.run(&session, "read shared");
        assert_eq!((o.exit, o.stdout.as_str(), o.ending.word.as_str()), (Some(0), "ok\n", "ok"));
        let o = d.run(&session, "read shared");
        assert_eq!(o.ending.word, "undecided");
        server.join().unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn retention_removes_only_old_or_surplus_completed_custody() {
        let dir = std::env::temp_dir().join(format!("custody-ret-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let put = |name: &str, phase: &str, at: u64| {
            std::fs::write(dir.join(format!("{name}.json")), json!({"phase":phase,"finishedAt":at}).to_string()).unwrap();
        };
        put("old", "completed", 10);
        put("a", "completed", 1000);
        put("b", "completed", 1001);
        put("c", "completed", 1002);
        put("running", "started", 0);
        put("waiting", "accepted", 0);
        let r = Retention { max_age_s: 500, max_records: 2 };
        assert_eq!(prune_custody(&dir, &r, 1100).unwrap(), 2, "the old one, then the oldest surplus");
        let left: Vec<_> = std::fs::read_dir(&dir).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
        for kept in ["b.json", "c.json", "running.json", "waiting.json"] {
            assert!(left.contains(&kept.to_string()), "{kept} {left:?}");
        }
        assert_eq!(bounded_text("héllo", 2), "h\n[custody keeps the first 2 bytes]");
        std::fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn sessions_follow_the_roster_renderer_rule() {
        let dir = std::env::temp_dir().join(format!("sessions-test-{}", std::process::id()));
        std::fs::create_dir_all(dir.join("ember")).unwrap();
        std::fs::create_dir_all(dir.join("friend")).unwrap();
        let s = Sessions { dir: dir.clone(), sponsor: "ember".into(), sponsor_workspace: "/store/sponsor".into() };
        assert_eq!(s.open("ember").unwrap().workspace, PathBuf::from("/store/sponsor"));
        let f = s.open("friend").unwrap();
        assert_eq!(f.home, dir.join("friend"));
        assert_eq!(f.workspace, dir.join("friend/workspace"));
        assert!(s.open("absent").unwrap_err().contains("no home"));
        assert!(s.open("../etc").is_err());
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
