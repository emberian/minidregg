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
    let (value, out, err) = streams_into(anonymous()?, anonymous()?, body)?;
    Ok((value, contents(out), contents(err)))
}

/// Run `body` with stdout and stderr pointed at `out` and `err`, which are handed back.
fn streams_into<T>(out: File, err: File, body: impl FnOnce() -> T) -> std::io::Result<(T, File, File)> {
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
    Ok((value, out, err))
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
    ended(|| Ok(args), None)
}

/// `mini ARGV...` in this process, parsed as `main` parses its own arguments.
/// With `sink`, stdout and stderr go to those files as they are printed and come back empty.
pub(crate) fn argv(raw: Vec<OsString>, sink: Option<(File, File)>) -> std::io::Result<(u8, Vec<u8>, Vec<u8>)> {
    ended(|| crate::Args::parse_from(raw), sink)
}

fn ended(args: impl FnOnce() -> crate::Result<crate::Args>, sink: Option<(File, File)>) -> std::io::Result<(u8, Vec<u8>, Vec<u8>)> {
    let named = sink.is_some();
    let (out, err) = match sink {
        Some(files) => files,
        None => (anonymous()?, anonymous()?),
    };
    let (ending, mut out, mut err) = streams_into(out, err, || {
        let _ = crate::take_command_ending();
        let _ = crate::take_host_decision();
        let _ = crate::take_line_refusal();
        let outer = crate::swap_exit_status(0);
        // A closed standard output ends this command (status 141, nothing more printed), never
        // the process serving it (`streams`).
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| args().and_then(crate::run)));
        let closed = matches!(&caught, Err(payload) if mini_streams::is_closed(&**payload));
        let parsed = caught.unwrap_or_else(|_| Err("the client panicked; see the message above".into()));
        let status = crate::swap_exit_status(outer);
        let _ = crate::take_line_refusal();
        if closed {
            let _ = crate::take_command_ending();
            let _ = crate::take_host_decision();
            return crate::MainEnding { code: mini_streams::CLOSED, stdout: String::new(), stderr: String::new() };
        }
        crate::main_ending(parsed, status)
    })?;
    // `main` prints its ending after the command returned; so does this.
    if named {
        let broken = |error: &std::io::Error| error.kind() == std::io::ErrorKind::BrokenPipe;
        match out.write_all(ending.stdout.as_bytes()) {
            Err(error) if broken(&error) => return Ok((mini_streams::CLOSED, Vec::new(), Vec::new())),
            other => other?,
        }
        match err.write_all(ending.stderr.as_bytes()) {
            Err(error) if broken(&error) => {}
            other => other?,
        }
        return Ok((ending.code, Vec::new(), Vec::new()));
    }
    let (mut stdout, mut stderr) = (contents(out), contents(err));
    stdout.extend_from_slice(ending.stdout.as_bytes());
    stderr.extend_from_slice(ending.stderr.as_bytes());
    Ok((ending.code, stdout, stderr))
}

/// `mini command-resident`: one client process that runs many commands for one
/// caller (the Hermes controller), so each is a frame instead of a fresh `mini`
/// that re-reads its workspace, re-pins its Host and reconnects its residents.
///
/// Descriptor 0 carries requests and 1 carries replies (`mini_sdk::command_resident`
/// is the wire); both are moved aside at start, so what is printed between
/// commands goes to standard error. A command reads exactly its request's
/// input bytes, then end of file. End of input between requests ends the process.
#[cfg(unix)]
pub(crate) fn serve() -> crate::Result<()> {
    use std::os::unix::ffi::OsStringExt;
    const ARGS_MAX: u32 = 4096;
    const BYTES_MAX: usize = 4 << 20;
    let moved = |fd: i32| -> std::io::Result<File> {
        let copy = unsafe { libc::dup(fd) };
        if copy < 0 {
            return Err(std::io::Error::last_os_error());
        }
        Ok(unsafe { File::from_raw_fd(copy) })
    };
    let (mut requests, mut replies) = (moved(0).map_err(|e| e.to_string())?, moved(1).map_err(|e| e.to_string())?);
    let null = File::open("/dev/null").map_err(|e| e.to_string())?;
    if unsafe { libc::dup2(null.as_raw_fd(), 0) } < 0 || unsafe { libc::dup2(2, 1) } < 0 {
        return Err(std::io::Error::last_os_error().to_string());
    }
    let word = |file: &mut File| -> std::io::Result<Option<u32>> {
        let mut bytes = [0u8; 4];
        let mut read = 0;
        while read < 4 {
            match file.read(&mut bytes[read..])? {
                0 if read == 0 => return Ok(None),
                0 => return Err(std::io::ErrorKind::UnexpectedEof.into()),
                n => read += n,
            }
        }
        Ok(Some(u32::from_be_bytes(bytes)))
    };
    loop {
        let Some(count) = word(&mut requests).map_err(|e| e.to_string())? else { return Ok(()) };
        if count == 0 || count > ARGS_MAX {
            return Err("command-resident: argument count out of bounds".into());
        }
        let mut raw = Vec::with_capacity(count as usize);
        let mut total = 0usize;
        for _ in 0..count {
            let length = word(&mut requests).map_err(|e| e.to_string())?.ok_or("command-resident: truncated request")? as usize;
            total += length;
            if total > BYTES_MAX {
                return Err("command-resident: request exceeds 4 MiB".into());
            }
            let mut bytes = vec![0u8; length];
            requests.read_exact(&mut bytes).map_err(|e| e.to_string())?;
            raw.push(OsString::from_vec(bytes));
        }
        let length = word(&mut requests).map_err(|e| e.to_string())?.ok_or("command-resident: truncated request")? as usize;
        if total + length > BYTES_MAX {
            return Err("command-resident: request exceeds 4 MiB".into());
        }
        let mut input = anonymous().map_err(|e| e.to_string())?;
        std::io::copy(&mut (&mut requests).take(length as u64), &mut input).map_err(|e| e.to_string())?;
        input.seek(SeekFrom::Start(0)).map_err(|e| e.to_string())?;
        if unsafe { libc::dup2(input.as_raw_fd(), 0) } < 0 {
            return Err(std::io::Error::last_os_error().to_string());
        }
        let mut sink = Vec::with_capacity(2);
        for _ in 0..2 {
            let length = word(&mut requests).map_err(|e| e.to_string())?.ok_or("command-resident: truncated request")? as usize;
            if length > 4096 {
                return Err("command-resident: output path exceeds 4096 bytes".into());
            }
            let mut bytes = vec![0u8; length];
            requests.read_exact(&mut bytes).map_err(|e| e.to_string())?;
            sink.push(OsString::from_vec(bytes));
        }
        let open = |path: &OsString| -> std::io::Result<File> {
            use std::os::unix::fs::OpenOptionsExt;
            std::fs::OpenOptions::new().append(true).create(true).mode(0o600)
                .custom_flags(libc::O_NOFOLLOW | libc::O_CLOEXEC).open(path)
        };
        let sink = match (sink[0].is_empty(), sink[1].is_empty()) {
            (true, true) => None,
            (false, false) => Some((open(&sink[0]).map_err(|e| e.to_string())?, open(&sink[1]).map_err(|e| e.to_string())?)),
            _ => return Err("command-resident: name both output files or neither".into()),
        };
        crate::VERIFY_HOST.store(false, std::sync::atomic::Ordering::Relaxed);
        let ran = argv(raw, sink);
        // Standard input is /dev/null again, and what the process's reader
        // buffered from this command's input is dropped, never the next one's.
        if unsafe { libc::dup2(null.as_raw_fd(), 0) } < 0 {
            return Err(std::io::Error::last_os_error().to_string());
        }
        {
            use std::io::BufRead;
            let mut stdin = std::io::stdin().lock();
            loop {
                let buffered = stdin.fill_buf().map(<[u8]>::len).unwrap_or(0);
                if buffered == 0 {
                    break;
                }
                stdin.consume(buffered);
            }
        }
        let (code, stdout, stderr) = ran.map_err(|e| e.to_string())?;
        let mut reply = Vec::with_capacity(9 + stdout.len() + stderr.len());
        reply.push(code);
        for stream in [&stdout, &stderr] {
            reply.extend_from_slice(&u32::try_from(stream.len()).map_err(|_| "command-resident: reply too large")?.to_be_bytes());
            reply.extend_from_slice(stream);
        }
        replies.write_all(&reply).map_err(|e| e.to_string())?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A resident (`line-resident`) runs a member's line with the member's descriptors as its
    /// streams. A reader that left ends that line with 141, and the resident keeps serving.
    #[test]
    fn a_closed_named_stdout_ends_the_command_not_the_process() {
        let mut ends = [0i32; 2];
        assert_eq!(unsafe { libc::pipe(ends.as_mut_ptr()) }, 0);
        let (read, write) = unsafe { (OwnedFd::from_raw_fd(ends[0]), File::from_raw_fd(ends[1])) };
        drop(read);
        let raw = vec![OsString::from("--help")];
        let (code, _, _) = argv(raw, Some((write, anonymous().unwrap()))).unwrap();
        assert_eq!(code, mini_streams::CLOSED);
        // Printed output (not the ending) on a closed stdout unwinds to the same end.
        let mut ends = [0i32; 2];
        assert_eq!(unsafe { libc::pipe(ends.as_mut_ptr()) }, 0);
        let (read, write) = unsafe { (OwnedFd::from_raw_fd(ends[0]), File::from_raw_fd(ends[1])) };
        drop(read);
        let (_, write, _) = streams_into(write, anonymous().unwrap(), || {
            let caught = std::panic::catch_unwind(|| println!("to nobody"));
            assert!(matches!(&caught, Err(payload) if mini_streams::is_closed(&**payload)));
        }).unwrap();
        drop(write);
    }

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
