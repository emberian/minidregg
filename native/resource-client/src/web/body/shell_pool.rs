//! The body's shell clients: a bounded pool of `mini command-resident` processes, each running
//! one form action's shell lines at a time (`mini_sdk::command_resident` is the wire). A client
//! is taken for a whole run and returned when its reply is in, so a line that outlives its page
//! keeps its client until it is done and no client is ever shared mid-line. A run past its
//! deadline that cannot move the world (a read) is stopped with its client's process group; a
//! client that fails a frame is killed and forgotten, and the next run starts a fresh one.
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// At most this many clients at once (and so this many concurrent form actions).
const CLIENTS_MAX: usize = 4;
/// A run waits at most this long for a client when all are taken, then is refused as busy.
const TAKE_WAIT: Duration = Duration::from_secs(2);
/// A run that outlived its page is waited on this long before its client is stopped.
const DETACHED_MAX: Duration = Duration::from_secs(24 * 3600);

pub(crate) struct Client {
    child: Child,
    requests: ChildStdin,
    replies: ChildStdout,
}

impl Client {
    fn kill(mut self) {
        mini_sdk::command_resident::kill_group(&mut self.child);
        let _ = self.child.wait();
    }
}

#[derive(Default)]
struct State {
    idle: Vec<Client>,
    live: usize,
}

/// The pool: idle clients and how many exist (idle or taken).
#[derive(Default)]
pub(crate) struct Pool {
    state: Mutex<State>,
    freed: Condvar,
    captures: AtomicU64,
}

/// One run's outcome: the exit code, or that the deadline passed (`detached`: the run goes on to
/// its end on its own client), or that the client failed; with what was printed so far.
pub(crate) struct Run {
    /// Every client is taken (at most `CLIENTS_MAX` actions at once): nothing ran.
    pub busy: bool,
    pub code: Option<i32>,
    pub detached: bool,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

impl Pool {
    /// A client: an idle one, a new one under `CLIENTS_MAX`, or one freed within `TAKE_WAIT`.
    /// `Err(true)`: all are taken (busy); `Err(false)`: a new client did not start.
    fn take(&self, start: &dyn Fn() -> std::io::Result<Client>) -> Result<Client, bool> {
        let deadline = Instant::now() + TAKE_WAIT;
        let mut state = self.state.lock().map_err(|_| false)?;
        loop {
            if let Some(client) = state.idle.pop() {
                return Ok(client);
            }
            if state.live < CLIENTS_MAX {
                state.live += 1;
                drop(state);
                return match start() {
                    Ok(client) => Ok(client),
                    Err(_) => {
                        self.forget();
                        Err(false)
                    }
                };
            }
            let left = deadline.saturating_duration_since(Instant::now());
            if left.is_zero() {
                return Err(true);
            }
            state = self.freed.wait_timeout(state, left).map_err(|_| false)?.0;
        }
    }

    fn give_back(&self, client: Client) {
        if let Ok(mut state) = self.state.lock() {
            state.idle.push(client);
        }
        self.freed.notify_one();
    }

    fn forget(&self) {
        if let Ok(mut state) = self.state.lock() {
            state.live = state.live.saturating_sub(1);
        }
        self.freed.notify_one();
    }

    fn discard(&self, client: Client) {
        client.kill();
        self.forget();
    }

    /// Run `arguments` with `stdin` on a pool client until `deadline`. `may_move` lines are never
    /// cut short: past the deadline the run keeps its client to its end (a thread waits, then
    /// returns the client). `bound` caps what is kept of each stream.
    pub(crate) fn run(
        self: &Arc<Self>,
        start: &dyn Fn() -> std::io::Result<Client>,
        capture_dir: &Path,
        arguments: &[&OsStr],
        stdin: &[u8],
        deadline: Instant,
        may_move: bool,
        bound: usize,
    ) -> Option<Run> {
        let mut client = match self.take(start) {
            Ok(client) => client,
            Err(true) => return Some(Run { busy: true, code: None, detached: false, stdout: Vec::new(), stderr: Vec::new() }),
            Err(false) => return None,
        };
        let id = self.captures.fetch_add(1, Ordering::Relaxed);
        let out = capture_dir.join(format!("shell-{}-{id}.out", std::process::id()));
        let err = capture_dir.join(format!("shell-{}-{id}.err", std::process::id()));
        let created = [&out, &err].iter().all(|path| {
            fs::OpenOptions::new().write(true).create_new(true).mode(0o600).custom_flags(libc::O_NOFOLLOW).open(path).is_ok()
        });
        let request = mini_sdk::command_resident::Request { arguments, stdin, stdout: Some(&out), stderr: Some(&err) };
        let sent = created && {
            use std::io::Write;
            client.requests.write_all(&mini_sdk::command_resident::frame(&request)).and_then(|_| client.requests.flush()).is_ok()
        };
        if !sent {
            self.discard(client);
            let _ = fs::remove_file(&out);
            let _ = fs::remove_file(&err);
            return None;
        }
        let reply = mini_sdk::command_resident::read_reply(&mut client.replies, deadline, 0);
        let printed = |path: &Path| read_bounded(path, bound);
        match reply {
            Ok(output) => {
                self.give_back(client);
                let run = Run { busy: false, code: output.status.code(), detached: false, stdout: printed(&out), stderr: printed(&err) };
                let _ = fs::remove_file(&out);
                let _ = fs::remove_file(&err);
                Some(run)
            }
            Err(error) if error.kind() == std::io::ErrorKind::TimedOut && may_move => {
                let run = Run { busy: false, code: None, detached: true, stdout: printed(&out), stderr: printed(&err) };
                let pool = self.clone();
                std::thread::spawn(move || {
                    match mini_sdk::command_resident::read_reply(&mut client.replies, Instant::now() + DETACHED_MAX, 0) {
                        Ok(_) => pool.give_back(client),
                        Err(_) => pool.discard(client),
                    }
                    let _ = fs::remove_file(&out);
                    let _ = fs::remove_file(&err);
                });
                Some(run)
            }
            Err(_) => {
                // A read past its deadline, or a client that ended mid-run: its group is stopped
                // before what it printed is read, so nothing more lands after this.
                self.discard(client);
                let run = Run { busy: false, code: None, detached: false, stdout: printed(&out), stderr: printed(&err) };
                let _ = fs::remove_file(&out);
                let _ = fs::remove_file(&err);
                Some(run)
            }
        }
    }

    /// Run one line to its end in the background with its output appended to `log`.
    pub(crate) fn run_detached(self: &Arc<Self>, start: &dyn Fn() -> std::io::Result<Client>, arguments: &[&OsStr], stdin: &[u8], log: &Path) -> bool {
        let Ok(mut client) = self.take(start) else { return false };
        let request = mini_sdk::command_resident::Request { arguments, stdin, stdout: Some(log), stderr: Some(log) };
        let sent = {
            use std::io::Write;
            client.requests.write_all(&mini_sdk::command_resident::frame(&request)).and_then(|_| client.requests.flush()).is_ok()
        };
        if !sent {
            self.discard(client);
            return false;
        }
        let pool = self.clone();
        std::thread::spawn(move || match mini_sdk::command_resident::read_reply(&mut client.replies, Instant::now() + DETACHED_MAX, 0) {
            Ok(_) => pool.give_back(client),
            Err(_) => pool.discard(client),
        });
        true
    }
}

/// Start a client: `command` is the program with its environment; it leads its own group.
pub(crate) fn start(mut command: Command) -> std::io::Result<Client> {
    command.arg("command-resident").stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit());
    std::os::unix::process::CommandExt::process_group(&mut command, 0);
    let mut child = command.spawn()?;
    let requests = child.stdin.take().ok_or_else(|| std::io::Error::other("client stdin was not piped"))?;
    let replies = child.stdout.take().ok_or_else(|| std::io::Error::other("client stdout was not piped"))?;
    Ok(Client { child, requests, replies })
}

/// At most `bound + 1` bytes of `path` (one overflow byte, as the child capture kept).
fn read_bounded(path: &Path, bound: usize) -> Vec<u8> {
    let mut bytes = Vec::new();
    if let Ok(file) = File::open(path) {
        let _ = file.take(bound as u64 + 1).read_to_end(&mut bytes);
    }
    bytes
}

/// A private directory for the runs' output files, under the member's shell home.
pub(crate) fn capture_dir(home: &Path) -> PathBuf {
    home.join("web-runs")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_full_pool_refuses_as_busy_after_the_short_wait() {
        let pool = Arc::new(Pool::default());
        pool.state.lock().unwrap().live = CLIENTS_MAX;
        let started = Instant::now();
        let run = pool
            .run(&|| Err(std::io::Error::other("never started")), Path::new("/nonexistent"), &[OsStr::new("whoami")], b"", Instant::now() + Duration::from_secs(100), true, 16)
            .expect("a busy pool answers");
        assert!(run.busy && run.code.is_none());
        assert!(started.elapsed() >= TAKE_WAIT && started.elapsed() < TAKE_WAIT + Duration::from_secs(1));
    }
}
