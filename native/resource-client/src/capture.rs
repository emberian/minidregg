//! A client command run in this process with its standard streams captured,
//! ending exactly as the child `mini` process it replaces would have ended.
//!
//! The composing verbs (chat, story, Hermes) used to run every workspace
//! operation as a child `mini` so its JSON never reached the friend's
//! terminal. A child re-reads its workspace, re-pins its Host and re-starts
//! its local helpers for every operation. This runs the same `crate::run`
//! here instead: file descriptors 1 and 2 point at private anonymous files for
//! the call, so what the child would have printed is captured, not shown; the
//! per-thread decision slots are cleared before and read after the call, as
//! `main` reads them; the process exit status a command raises is the call's
//! own and the caller's is restored.
//!
//! The descriptor swap is process-wide. Only the single-threaded command-line
//! verbs call this; a server thread never does.
use std::ffi::OsString;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};

/// One anonymous private file, unlinked from birth.
fn anonymous() -> std::io::Result<File> {
    // SAFETY: tmpfile(3) returns a FILE* on a fresh unlinked file or NULL.
    let stream = unsafe { libc::tmpfile() };
    if stream.is_null() {
        return Err(std::io::Error::last_os_error());
    }
    // Keep only a duplicate of its descriptor; the FILE* is closed at once.
    let fd = unsafe { libc::dup(libc::fileno(stream)) };
    unsafe { libc::fclose(stream) };
    if fd < 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(unsafe { File::from_raw_fd(fd) })
}

fn redirect(from: &File, to: i32) -> std::io::Result<OwnedFd> {
    let saved = unsafe { libc::dup(to) };
    if saved < 0 {
        return Err(std::io::Error::last_os_error());
    }
    let saved = unsafe { OwnedFd::from_raw_fd(saved) };
    if unsafe { libc::dup2(from.as_raw_fd(), to) } < 0 {
        return Err(std::io::Error::last_os_error());
    }
    Ok(saved)
}

fn restore(saved: &OwnedFd, to: i32) {
    unsafe { libc::dup2(saved.as_raw_fd(), to) };
}

fn contents(mut file: File) -> Vec<u8> {
    let mut bytes = Vec::new();
    let _ = file.seek(SeekFrom::Start(0)).and_then(|_| file.read_to_end(&mut bytes));
    bytes
}

/// Run `body` with stdout and stderr captured: (its value, stdout, stderr).
pub(crate) fn streams<T>(body: impl FnOnce() -> T) -> std::io::Result<(T, Vec<u8>, Vec<u8>)> {
    let (out, err) = (anonymous()?, anonymous()?);
    let _ = std::io::stdout().flush();
    let saved_out = redirect(&out, 1)?;
    let saved_err = match redirect(&err, 2) {
        Ok(saved) => saved,
        Err(error) => {
            restore(&saved_out, 1);
            return Err(error);
        }
    };
    let value = body();
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    restore(&saved_err, 2);
    restore(&saved_out, 1);
    Ok((value, contents(out), contents(err)))
}

/// `mini COMMAND --NAME VALUE ...` in this process: its exit code, stdout and
/// stderr, byte for byte what the child's `main` would have ended with.
pub(crate) fn command(command: &str, flags: &[(&str, OsString)]) -> std::io::Result<(u8, Vec<u8>, Vec<u8>)> {
    let args = crate::Args {
        command: OsString::from(command),
        values: flags
            .iter()
            .map(|(name, value)| (OsString::from(format!("--{name}")), value.clone()))
            .collect(),
    };
    let (ending, mut stdout, mut stderr) = streams(|| {
        let _ = crate::take_command_ending();
        let _ = crate::take_host_decision();
        let _ = crate::take_line_refusal();
        let outer = crate::swap_exit_status(0);
        let parsed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| crate::run(args)))
            .unwrap_or_else(|_| Err("the client panicked; see the message above".into()));
        let status = crate::swap_exit_status(outer);
        let _ = crate::take_line_refusal();
        crate::main_ending(parsed, status)
    })?;
    // `main` prints its ending after the command returned; so does this.
    stdout.extend_from_slice(ending.stdout.as_bytes());
    stderr.extend_from_slice(ending.stderr.as_bytes());
    Ok((ending.code, stdout, stderr))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn captured_streams_never_reach_the_callers_descriptors_and_are_restored() {
        // libtest captures the print macros per thread; the descriptors are what a
        // command's output reaches outside a test.
        let ((), out, err) = streams(|| {
            std::io::stdout().write_all(b"to stdout\n").unwrap();
            std::io::stderr().write_all(b"to stderr\n").unwrap();
        })
        .unwrap();
        assert_eq!(out, b"to stdout\n");
        assert_eq!(err, b"to stderr\n");
        // Descriptor 1 is the caller's again: a second capture sees only its own bytes.
        let ((), out, _) = streams(|| std::io::stdout().write_all(b"second").unwrap()).unwrap();
        assert_eq!(out, b"second");
    }
}
