//! Linearizes work-origin Mini child creation with a hard connector break.
//! The caller persists its exact pending attempt before calling `run_capture`.
//! A child that crossed the spawn boundary remains an uncertain exact attempt
//! even when `cancel` kills it; this gate never infers a native refusal.
//! Cancellation affects only this per-invocation Mini client, never the shared
//! persistent Host. A Host call already dispatched may still be accepted after
//! client death; exact lookup and the signed generation fence remain necessary.

use std::fmt;
use std::ffi::OsStr;
use std::io::{self, Read, Write};
use std::os::fd::AsRawFd;
use std::os::unix::process::CommandExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, ChildStdout, Command, Output, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

const MAX_STREAM_BYTES: usize = 1024 * 1024;
const PIPE_DRAIN_GRACE: Duration = Duration::from_millis(300);

#[derive(Default)]
pub struct CustodyGate {
    child: Mutex<Option<Child>>,
    /// The `mini` whose commands run as frames to one resident `mini
    /// command-resident` instead of one child each (`run_resident`).
    resident_program: Option<PathBuf>,
    /// The umask the resident runs with, as the one-shot children it replaces
    /// set it; None inherits this process's.
    resident_umask: Option<libc::mode_t>,
    resident: Mutex<Option<Resident>>,
}

/// The resident client: its own process group, killed by `cancel` exactly as
/// a one-shot child is. `busy` while a request is outstanding; the reply pipe
/// is held by that request until it returns.
struct Resident {
    child: Child,
    requests: ChildStdin,
    replies: Option<ChildStdout>,
    busy: bool,
}

/// Only `BeforeSpawn` certifies that this invocation created no Mini child.
/// Every other failure is conservative: the caller must retain its exact
/// pending attempt until native lookup or an explicit audited resolution.
#[derive(Debug)]
pub enum CustodyError {
    BeforeSpawn,
    Uncertain(io::Error),
}

impl From<io::Error> for CustodyError {
    fn from(error: io::Error) -> Self {
        Self::Uncertain(error)
    }
}

impl fmt::Display for CustodyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BeforeSpawn => write!(f, "hard connector closed before Mini custody spawn"),
            Self::Uncertain(error) => write!(f, "Mini custody child outcome uncertain: {error}"),
        }
    }
}

impl std::error::Error for CustodyError {}

impl CustodyGate {
    pub fn new() -> Self {
        Self::default()
    }

    /// A gate whose commands for `mini` (with no environment or directory of
    /// their own) run in one resident client process.
    pub fn with_resident(mini: &Path, umask: Option<libc::mode_t>) -> Self {
        Self { resident_program: Some(mini.to_path_buf()), resident_umask: umask, ..Self::default() }
    }

    pub fn has_resident(&self) -> bool {
        self.resident_program.is_some()
    }

    fn routes(&self, command: &Command) -> bool {
        self.resident_program.as_deref().is_some_and(|mini| command.get_program() == mini.as_os_str())
            && command.get_envs().next().is_none()
            && command.get_current_dir().is_none()
    }

    /// Called by hard EOF after independently signalling the physical worker.
    /// A racing spawn either observes `cancelled`, or is published under this
    /// lock before we signal it. Reaping and clearing happen under the same
    /// lock, so a reused PID is never signalled through a stale entry.
    pub fn cancel(&self) -> io::Result<Option<u32>> {
        let mut slot = self
            .child
            .lock()
            .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
        let resident = self.cancel_resident()?;
        let Some(child) = slot.as_mut() else {
            return Ok(resident);
        };
        let pid = child.id();
        // The child leads its own process group (see spawn below) and is
        // unreaped while tracked here, so the PGID cannot be stale.
        unsafe {
            libc::kill(-(pid as libc::pid_t), libc::SIGKILL);
        }
        match child.kill() {
            Ok(()) => Ok(Some(pid)),
            Err(error) if error.kind() == io::ErrorKind::InvalidInput => Ok(Some(pid)),
            Err(error) => Err(error),
        }
    }

    /// Kill the resident's process group. An idle resident is reaped here; a
    /// busy one by the request that owns its reply pipe, which then sees EOF.
    fn cancel_resident(&self) -> io::Result<Option<u32>> {
        let mut resident = self
            .resident
            .lock()
            .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
        let Some(running) = resident.as_mut() else {
            return Ok(None);
        };
        let pid = running.child.id();
        unsafe {
            libc::kill(-(pid as libc::pid_t), libc::SIGKILL);
        }
        let _ = running.child.kill();
        if !running.busy {
            let _ = running.child.wait();
            *resident = None;
        }
        Ok(Some(pid))
    }

    /// End an idle resident: its input closes, it exits at the frame
    /// boundary and is reaped (killed after two seconds). A busy one refuses.
    /// The physical quiescence proof admits no effect-capable client process.
    pub fn retire(&self) -> io::Result<()> {
        let mut resident = self
            .resident
            .lock()
            .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
        let Some(running) = resident.take() else { return Ok(()) };
        if running.busy {
            *resident = Some(running);
            return Err(io::Error::other("Mini resident client has an outstanding command"));
        }
        let Resident { mut child, requests, .. } = running;
        drop(requests);
        let start = Instant::now();
        while child.try_wait()?.is_none() {
            if start.elapsed() >= Duration::from_secs(2) {
                unsafe {
                    libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL);
                }
                let _ = child.kill();
                child.wait()?;
                break;
            }
            thread::sleep(Duration::from_millis(5));
        }
        Ok(())
    }

    fn resident_busy(&self) -> io::Result<bool> {
        Ok(self
            .resident
            .lock()
            .map_err(|_| io::Error::other("Mini custody gate poisoned"))?
            .as_ref()
            .is_some_and(|resident| resident.busy))
    }

    /// No custody command is outstanding: every one-shot child this gate
    /// spawned has been reaped (or never existed) and the resident is between
    /// requests.
    pub fn is_idle(&self) -> bool {
        self.child.lock().map(|slot| slot.is_none()).unwrap_or(false)
            && self.resident_busy().map(|busy| !busy).unwrap_or(false)
    }

    /// Bounded by `crate::deadline::NATIVE_CALL`: a child that outlives it is
    /// killed with its process group and reported `Uncertain(TimedOut)`,
    /// exactly like a lost reply.
    pub fn run_capture(
        &self,
        cancelled: &AtomicBool,
        command: &mut Command,
    ) -> Result<Output, CustodyError> {
        self.run_capture_until(cancelled, command, crate::deadline::NATIVE_CALL)
    }

    pub fn run_capture_until(
        &self,
        cancelled: &AtomicBool,
        command: &mut Command,
        limit: Duration,
    ) -> Result<Output, CustodyError> {
        self.run_capture_with_hooks(cancelled, command, limit, || {}, |_| {})
    }

    fn run_capture_with_hooks(
        &self,
        cancelled: &AtomicBool,
        command: &mut Command,
        limit: Duration,
        before_check: impl FnOnce(),
        after_spawn: impl FnOnce(u32),
    ) -> Result<Output, CustodyError> {
        if self.routes(command) {
            return self.run_resident(cancelled, command, limit, before_check, after_spawn);
        }
        let (mut stdout, mut stderr) = {
            let mut slot = self
                .child
                .lock()
                .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
            // Production passes a no-op; the hook holds this exact boundary
            // open only in the deterministic cancellation race tests.
            before_check();
            if cancelled.load(Ordering::SeqCst) {
                return Err(CustodyError::BeforeSpawn);
            }
            if slot.is_some() || self.resident_busy()? {
                return Err(io::Error::other("another Mini custody child is active").into());
            }
            command.process_group(0).stdout(Stdio::piped()).stderr(Stdio::piped());
            let mut child = command.spawn()?;
            let stdout = child
                .stdout
                .take()
                .ok_or_else(|| io::Error::other("Mini child stdout was not piped"))?;
            let stderr = child
                .stderr
                .take()
                .ok_or_else(|| io::Error::other("Mini child stderr was not piped"))?;
            let pid = child.id();
            *slot = Some(child);
            after_spawn(pid);
            (stdout, stderr)
        };

        if let Err(error) = set_nonblocking(&stdout).and_then(|_| set_nonblocking(&stderr)) {
            let _ = self.cancel();
            let _ = self.reap_after_abort(Duration::from_secs(2));
            return Err(error.into());
        }
        let mut out_bytes = Vec::new();
        let mut err_bytes = Vec::new();
        let mut out_eof = false;
        let mut err_eof = false;
        let mut fault: Option<io::Error> = None;
        let mut exited: Option<(std::process::ExitStatus, Instant)> = None;
        let started = Instant::now();
        loop {
            if exited.is_none() && fault.is_none() && started.elapsed() >= limit {
                fault = Some(io::Error::new(io::ErrorKind::TimedOut, format!(
                    "Mini child exceeded its {}s deadline; killed; exact attempt uncertain",
                    limit.as_secs())));
                let _ = self.cancel();
            }
            if !out_eof {
                match drain_nonblocking(&mut stdout, &mut out_bytes) {
                    Ok((eof, overflow)) => {
                        out_eof = eof;
                        if overflow && fault.is_none() {
                            fault = Some(io::Error::other(
                                "Mini stdout exceeded custody capture bound",
                            ));
                            let _ = self.cancel();
                        }
                    }
                    Err(error) => {
                        out_eof = true;
                        if fault.is_none() {
                            fault = Some(error);
                            let _ = self.cancel();
                        }
                    }
                }
            }
            if !err_eof {
                match drain_nonblocking(&mut stderr, &mut err_bytes) {
                    Ok((eof, overflow)) => {
                        err_eof = eof;
                        if overflow && fault.is_none() {
                            fault = Some(io::Error::other(
                                "Mini stderr exceeded custody capture bound",
                            ));
                            let _ = self.cancel();
                        }
                    }
                    Err(error) => {
                        err_eof = true;
                        if fault.is_none() {
                            fault = Some(error);
                            let _ = self.cancel();
                        }
                    }
                }
            }
            if exited.is_none() {
                let mut slot = self
                    .child
                    .lock()
                    .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
                let child = slot
                    .as_mut()
                    .ok_or_else(|| io::Error::other("Mini custody child disappeared"))?;
                match child.try_wait() {
                    Ok(Some(status)) => {
                        slot.take();
                        exited = Some((status, Instant::now()));
                    }
                    Ok(None) => {}
                    Err(error) => {
                        // Keep the identity tracked if reaping itself fails.
                        let _ = child.kill();
                        drop(slot);
                        let _ = self.reap_after_abort(Duration::from_secs(2));
                        return Err(error.into());
                    }
                }
                drop(slot);
            }
            if let Some((status, since)) = exited {
                if out_eof && err_eof {
                    return if let Some(error) = fault {
                        Err(error.into())
                    } else {
                        Ok(Output {
                            status,
                            stdout: out_bytes,
                            stderr: err_bytes,
                        })
                    };
                }
                if since.elapsed() >= PIPE_DRAIN_GRACE {
                    return Err(io::Error::new(io::ErrorKind::TimedOut,
                        "Mini leader exited but a descendant retained an output pipe; exact attempt uncertain").into());
                }
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    /// One command as a frame to the resident client (`mini command-resident`,
    /// resource-client `capture::serve`). Crossing the spawn boundary is
    /// writing the request: after it, every failure is `Uncertain` and the
    /// resident is killed with its group, exactly as a one-shot child is.
    fn run_resident(
        &self,
        cancelled: &AtomicBool,
        command: &Command,
        limit: Duration,
        before_check: impl FnOnce(),
        after_spawn: impl FnOnce(u32),
    ) -> Result<Output, CustodyError> {
        let started = Instant::now();
        let mut frame = Vec::new();
        let arguments: Vec<&OsStr> = command.get_args().collect();
        frame.extend_from_slice(&(arguments.len() as u32).to_be_bytes());
        for argument in &arguments {
            use std::os::unix::ffi::OsStrExt;
            frame.extend_from_slice(&(argument.len() as u32).to_be_bytes());
            frame.extend_from_slice(argument.as_bytes());
        }
        let (mut replies, pid) = {
            let slot = self
                .child
                .lock()
                .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
            before_check();
            if cancelled.load(Ordering::SeqCst) {
                return Err(CustodyError::BeforeSpawn);
            }
            let mut resident = self
                .resident
                .lock()
                .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
            if slot.is_some() || resident.as_ref().is_some_and(|r| r.busy) {
                return Err(io::Error::other("another Mini custody child is active").into());
            }
            if resident.as_mut().is_some_and(|r| !matches!(r.child.try_wait(), Ok(None))) {
                *resident = None;
            }
            if resident.is_none() {
                let mini = self.resident_program.as_deref().ok_or_else(|| io::Error::other("no resident program"))?;
                let mut spawn = Command::new(mini);
                spawn.arg("command-resident").process_group(0)
                    .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit());
                if let Some(mask) = self.resident_umask {
                    unsafe {
                        spawn.pre_exec(move || {
                            libc::umask(mask);
                            Ok(())
                        });
                    }
                }
                let mut child = spawn.spawn()?;
                let requests = child.stdin.take().ok_or_else(|| io::Error::other("resident stdin was not piped"))?;
                let replies = child.stdout.take().ok_or_else(|| io::Error::other("resident stdout was not piped"))?;
                *resident = Some(Resident { child, requests, replies: Some(replies), busy: false });
            }
            let running = resident.as_mut().expect("resident present");
            let pid = running.child.id();
            running.busy = true;
            let Some(replies) = running.replies.take() else {
                running.busy = false;
                return Err(io::Error::other("resident reply pipe absent").into());
            };
            if let Err(error) = running.requests.write_all(&frame) {
                unsafe {
                    libc::kill(-(pid as libc::pid_t), libc::SIGKILL);
                }
                let _ = running.child.kill();
                let _ = running.child.wait();
                *resident = None;
                return Err(error.into());
            }
            after_spawn(pid);
            (replies, pid)
        };
        let reply = read_reply(&mut replies, started + limit, limit);
        let mut resident = self
            .resident
            .lock()
            .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
        match reply {
            Ok(output) => {
                match resident.as_mut() {
                    Some(running) if running.child.id() == pid => {
                        running.replies = Some(replies);
                        running.busy = false;
                    }
                    _ => {}
                }
                Ok(output)
            }
            Err(error) => {
                if let Some(mut running) = resident.take() {
                    unsafe {
                        libc::kill(-(pid as libc::pid_t), libc::SIGKILL);
                    }
                    let _ = running.child.kill();
                    let _ = running.child.wait();
                }
                Err(error.into())
            }
        }
    }

    fn reap_after_abort(&self, limit: Duration) -> io::Result<()> {
        let start = Instant::now();
        loop {
            let mut slot = self
                .child
                .lock()
                .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
            let Some(child) = slot.as_mut() else {
                return Ok(());
            };
            if child.try_wait()?.is_some() {
                slot.take();
                return Ok(());
            }
            drop(slot);
            if start.elapsed() >= limit {
                return Err(io::Error::new(
                    io::ErrorKind::TimedOut,
                    "signalled Mini child has not exited",
                ));
            }
            thread::sleep(Duration::from_millis(10));
        }
    }
}

/// The resident's reply: exit code, then stdout and stderr, each a u32 length
/// and its bytes. Waits on the pipe itself (poll) until `deadline`.
fn read_reply(pipe: &mut ChildStdout, deadline: Instant, limit: Duration) -> io::Result<Output> {
    let mut bytes = Vec::new();
    loop {
        if let Some(output) = parse_reply(&bytes)? {
            return Ok(output);
        }
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            return Err(io::Error::new(io::ErrorKind::TimedOut, format!(
                "Mini resident exceeded its {}s deadline; killed; exact attempt uncertain", limit.as_secs())));
        }
        let mut poll = libc::pollfd { fd: pipe.as_raw_fd(), events: libc::POLLIN, revents: 0 };
        let wait = left.as_millis().min(i32::MAX as u128) as i32;
        match unsafe { libc::poll(&mut poll, 1, wait.max(1)) } {
            0 => continue,
            n if n < 0 => {
                let error = io::Error::last_os_error();
                if error.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(error);
            }
            _ => {}
        }
        let mut chunk = [0u8; 65536];
        match pipe.read(&mut chunk) {
            Ok(0) => return Err(io::Error::new(io::ErrorKind::UnexpectedEof,
                "Mini resident ended before its reply; exact attempt uncertain")),
            Ok(count) => bytes.extend_from_slice(&chunk[..count]),
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
}

fn parse_reply(bytes: &[u8]) -> io::Result<Option<Output>> {
    let Some((&code, mut rest)) = bytes.split_first() else { return Ok(None) };
    let mut streams = Vec::with_capacity(2);
    for _ in 0..2 {
        let Some(length) = rest.get(..4) else { return Ok(None) };
        let length = u32::from_be_bytes(length.try_into().expect("four bytes")) as usize;
        if length > MAX_STREAM_BYTES {
            return Err(io::Error::other("Mini resident reply exceeded custody capture bound"));
        }
        let Some(stream) = rest.get(4..4 + length) else { return Ok(None) };
        streams.push(stream.to_vec());
        rest = &rest[4 + length..];
    }
    if !rest.is_empty() {
        return Err(io::Error::other("Mini resident wrote past its reply"));
    }
    let stderr = streams.pop().expect("two streams");
    let stdout = streams.pop().expect("two streams");
    Ok(Some(Output { status: std::process::ExitStatus::from_raw(i32::from(code) << 8), stdout, stderr }))
}

fn set_nonblocking(pipe: &impl AsRawFd) -> io::Result<()> {
    let fd = pipe.as_raw_fd();
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

fn drain_nonblocking(pipe: &mut impl Read, bytes: &mut Vec<u8>) -> io::Result<(bool, bool)> {
    let mut overflow = false;
    for _ in 0..16 {
        let mut chunk = [0u8; 8192];
        match pipe.read(&mut chunk) {
            Ok(0) => return Ok((true, overflow)),
            Ok(count) => {
                let room = MAX_STREAM_BYTES.saturating_sub(bytes.len());
                bytes.extend_from_slice(&chunk[..count.min(room)]);
                overflow |= count > room;
            }
            Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                return Ok((false, overflow))
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
            Err(error) => return Err(error),
        }
    }
    Ok((false, overflow))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::mpsc;
    use std::sync::Arc;
    use std::time::Instant;

    #[test]
    fn hard_eof_before_spawn_vetoes_native_child() {
        let gate = Arc::new(CustodyGate::new());
        let cancelled = Arc::new(AtomicBool::new(false));
        let (at_boundary, ready) = mpsc::channel();
        let (release, proceed) = mpsc::channel();
        let run_gate = gate.clone();
        let run_cancelled = cancelled.clone();
        let runner = thread::spawn(move || {
            run_gate.run_capture_with_hooks(
                &run_cancelled,
                Command::new("/bin/sleep").arg("30"),
                crate::deadline::NATIVE_CALL,
                || {
                    at_boundary.send(()).unwrap();
                    proceed.recv().unwrap();
                },
                |_| panic!("cancelled Mini child spawned"),
            )
        });
        ready.recv().unwrap();
        cancelled.store(true, Ordering::SeqCst);
        let cancel_gate = gate.clone();
        let canceller = thread::spawn(move || cancel_gate.cancel().unwrap());
        release.send(()).unwrap();
        assert!(matches!(
            runner.join().unwrap(),
            Err(CustodyError::BeforeSpawn)
        ));
        assert_eq!(canceller.join().unwrap(), None);
    }

    #[test]
    fn hard_eof_after_spawn_signals_tracked_child_without_waiting_for_native_call() {
        let gate = Arc::new(CustodyGate::new());
        let cancelled = Arc::new(AtomicBool::new(false));
        let (spawned, ready) = mpsc::channel();
        let (release, proceed) = mpsc::channel();
        let run_gate = gate.clone();
        let run_cancelled = cancelled.clone();
        let runner = thread::spawn(move || {
            run_gate.run_capture_with_hooks(
                &run_cancelled,
                Command::new("/bin/sleep").arg("30"),
                crate::deadline::NATIVE_CALL,
                || {},
                |pid| {
                    spawned.send(pid).unwrap();
                    proceed.recv().unwrap();
                },
            )
        });
        let pid = ready.recv().unwrap();
        let start = Instant::now();
        cancelled.store(true, Ordering::SeqCst);
        let cancel_gate = gate.clone();
        let canceller = thread::spawn(move || cancel_gate.cancel().unwrap());
        release.send(()).unwrap();
        assert_eq!(canceller.join().unwrap(), Some(pid));
        assert!(start.elapsed() < Duration::from_secs(2));
        let output = runner.join().unwrap().unwrap();
        assert!(!output.status.success());
        assert_eq!(gate.cancel().unwrap(), None);
    }

    #[test]
    fn descendant_held_pipe_returns_bounded_uncertainty_after_leader_exit() {
        let gate = CustodyGate::new();
        let cancelled = AtomicBool::new(false);
        let start = Instant::now();
        let result = gate.run_capture(
            &cancelled,
            Command::new("/bin/sh").arg("-c").arg("sleep 1 & exit 0"),
        );
        assert!(matches!(result, Err(CustodyError::Uncertain(error))
            if error.kind() == io::ErrorKind::TimedOut));
        assert!(start.elapsed() < Duration::from_secs(2));
        assert_eq!(gate.cancel().unwrap(), None);
    }

    #[test]
    fn oversized_child_output_is_uncertain_and_bounded() {
        let gate = CustodyGate::new();
        let cancelled = AtomicBool::new(false);
        let result = gate.run_capture(
            &cancelled,
            Command::new("/bin/sh")
                .arg("-c")
                .arg("head -c 1048577 /dev/zero"),
        );
        assert!(matches!(result, Err(CustodyError::Uncertain(_))));
        assert_eq!(gate.cancel().unwrap(), None);
    }

    #[test]
    fn deadline_turns_a_hung_custody_child_into_an_uncertain_timeout() {
        let gate = CustodyGate::new();
        let cancelled = AtomicBool::new(false);
        let start = Instant::now();
        let result = gate.run_capture_until(&cancelled,
            Command::new("/bin/sh").args(["-c", "sleep 30 & sleep 30"]), Duration::from_millis(300));
        match result {
            Err(CustodyError::Uncertain(error)) => assert_eq!(error.kind(), io::ErrorKind::TimedOut),
            other => panic!("expected an uncertain timeout, got {other:?}"),
        }
        assert!(start.elapsed() < Duration::from_secs(5), "{:?}", start.elapsed());
        assert!(gate.is_idle());
    }

    /// A stand-in for `mini command-resident`: it answers each request with
    /// exit code 3, its arguments joined on stdout and its pid on stderr, and
    /// sleeps forever on the argument `hang`.
    fn fake_resident(dir: &Path) -> PathBuf {
        let path = dir.join("mini");
        std::fs::write(&path, concat!(
            "#!/usr/bin/env python3\n",
            "import os,struct,sys,time\n",
            "r,w=sys.stdin.buffer,sys.stdout.buffer\n",
            "assert sys.argv[1:]==['command-resident']\n",
            "while True:\n",
            "  h=r.read(4)\n",
            "  if not h: break\n",
            "  a=[r.read(struct.unpack('>I',r.read(4))[0]) for _ in range(struct.unpack('>I',h)[0])]\n",
            "  if a==[b'hang']: time.sleep(60)\n",
            "  o=b' '.join(a); e=str(os.getpid()).encode()\n",
            "  w.write(bytes([3])+struct.pack('>I',len(o))+o+struct.pack('>I',len(e))+e); w.flush()\n",
        )).unwrap();
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o700)).unwrap();
        path
    }

    #[test]
    fn resident_answers_many_commands_from_one_process_and_cancel_kills_it() {
        let dir = std::env::temp_dir().join(format!("custody-resident-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mini = fake_resident(&dir);
        let gate = Arc::new(CustodyGate::with_resident(&mini, Some(0o077)));
        let cancelled = Arc::new(AtomicBool::new(false));
        let run = |args: &[&str]| {
            let mut command = Command::new(&mini);
            command.args(args);
            gate.run_capture_until(&cancelled, &mut command, Duration::from_secs(10))
        };
        let first = run(&["workspace", "--action", "list"]).unwrap();
        assert_eq!(first.status.code(), Some(3));
        assert_eq!(first.stdout, b"workspace --action list");
        let second = run(&["workspace", "--action", "read", "--name", "x"]).unwrap();
        assert_eq!(second.stdout, b"workspace --action read --name x");
        assert_eq!(first.stderr, second.stderr, "one resident process answered both");
        assert!(gate.is_idle());
        // A command with its own environment is a one-shot child, not a frame.
        let mut own = Command::new("/bin/echo");
        own.arg("alone");
        assert_eq!(gate.run_capture_until(&cancelled, &mut own, Duration::from_secs(10)).unwrap().stdout, b"alone\n");
        // A hung command is killed at hard EOF and reported uncertain; the next one respawns.
        let (gate2, cancelled2) = (gate.clone(), cancelled.clone());
        let hung = thread::spawn(move || {
            let mut command = Command::new(&fake_resident(&std::env::temp_dir().join(format!("custody-resident-{}", std::process::id()))));
            command.arg("hang");
            gate2.run_capture_until(&cancelled2, &mut command, Duration::from_secs(30))
        });
        let started = Instant::now();
        while gate.is_idle() && started.elapsed() < Duration::from_secs(5) {
            thread::sleep(Duration::from_millis(5));
        }
        gate.cancel().unwrap();
        assert!(matches!(hung.join().unwrap(), Err(CustodyError::Uncertain(_))));
        assert!(started.elapsed() < Duration::from_secs(10));
        let third = run(&["again"]).unwrap();
        assert_ne!(third.stderr, first.stderr, "a fresh resident after cancel");
        gate.retire().unwrap();
        let pid: i32 = String::from_utf8(third.stderr).unwrap().parse().unwrap();
        assert_ne!(unsafe { libc::kill(pid, 0) }, 0, "a retired resident is gone");
        let _ = std::fs::remove_dir_all(&dir);
    }

}
