//! One line through the ssh entrance's own forced command.
//!
//! The entrance does not re-derive `mini shell`'s environment. It runs
//! `deploy/shell/mini-shell-ssh MINI HOST CONFIG SOCKET WORKSPACE HOME` with the line in
//! `SSH_ORIGINAL_COMMAND` (so the line is one argument to `mini shell --line`, never parsed
//! by a system shell) and an otherwise empty environment. WORKSPACE and HOME come from the
//! session NAME by `render-authorized-keys.sh`'s rule: HOME is `SESSIONS/NAME`; WORKSPACE is
//! the sponsor workspace for the sponsor and `HOME/workspace` for everyone else.

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::process::CommandExt;
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
}

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
        })
    }

    /// Run one line in one session. Never fails: a spawn failure or a timeout is an ending.
    pub fn run(&self, session: &Session, line: &str) -> Outcome {
        let mut cmd = Command::new(&self.wrapper);
        cmd.args([&self.mini, &self.host, &self.config, &self.socket, &session.workspace, &session.home])
            .env_clear()
            .env("PATH", "/usr/bin:/bin")
            .env("LANG", "C.UTF-8")
            .env("SSH_ORIGINAL_COMMAND", line)
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            // Its own process group, so a timeout stops the Host children too.
            .process_group(0);
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
            None => Ending::entrance(
                "undecided",
                &format!(
                    "the line did not finish within {} s and was stopped; if it submitted, `lookup ID` asks the Host again",
                    self.timeout.as_secs()
                ),
            ),
        };
        Outcome { exit: status.and_then(|s| s.code()), stdout, stderr, ending }
    }
}

fn capture<R: Read + Send + 'static>(r: Option<R>) -> std::thread::JoinHandle<String> {
    std::thread::spawn(move || {
        let mut buf = Vec::new();
        if let Some(r) = r {
            let _ = r.take(MAX_CAPTURE as u64).read_to_end(&mut buf);
        }
        String::from_utf8_lossy(&buf).into_owned()
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

/// Append one record to `HOME/<file>` (created 0600).
pub fn append_log(home: &Path, file: &str, record: &serde_json::Value) -> std::io::Result<()> {
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
