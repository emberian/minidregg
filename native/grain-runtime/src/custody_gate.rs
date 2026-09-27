//! Linearizes work-origin Mini child creation with a hard connector break.
//! The caller persists its exact pending attempt before calling `run_capture`.
//! A child that crossed the spawn boundary remains an uncertain exact attempt
//! even when `cancel` kills it; this gate never infers a native refusal.
//! Cancellation affects only this per-invocation Mini client, never the shared
//! persistent Host. A Host call already dispatched may still be accepted after
//! client death; exact lookup and the signed generation fence remain necessary.

use std::fmt;
use std::io::{self, Read};
use std::os::fd::AsRawFd;
use std::process::{Child, Command, Output, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

const MAX_STREAM_BYTES: usize = 1024 * 1024;
const PIPE_DRAIN_GRACE: Duration = Duration::from_millis(300);

#[derive(Default)]
pub struct CustodyGate {
    child: Mutex<Option<Child>>,
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

    /// Called by hard EOF after independently signalling the physical worker.
    /// A racing spawn either observes `cancelled`, or is published under this
    /// lock before we signal it. Reaping and clearing happen under the same
    /// lock, so a reused PID is never signalled through a stale entry.
    pub fn cancel(&self) -> io::Result<Option<u32>> {
        let mut slot = self
            .child
            .lock()
            .map_err(|_| io::Error::other("Mini custody gate poisoned"))?;
        let Some(child) = slot.as_mut() else {
            return Ok(None);
        };
        let pid = child.id();
        match child.kill() {
            Ok(()) => Ok(Some(pid)),
            Err(error) if error.kind() == io::ErrorKind::InvalidInput => Ok(Some(pid)),
            Err(error) => Err(error),
        }
    }

    pub fn run_capture(
        &self,
        cancelled: &AtomicBool,
        command: &mut Command,
    ) -> Result<Output, CustodyError> {
        self.run_capture_with_hooks(cancelled, command, || {}, |_| {})
    }

    fn run_capture_with_hooks(
        &self,
        cancelled: &AtomicBool,
        command: &mut Command,
        before_check: impl FnOnce(),
        after_spawn: impl FnOnce(u32),
    ) -> Result<Output, CustodyError> {
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
            if slot.is_some() {
                return Err(io::Error::other("another Mini custody child is active").into());
            }
            command.stdout(Stdio::piped()).stderr(Stdio::piped());
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
        loop {
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
}
